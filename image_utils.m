#import "image_utils.h"
#import "vcam_shared.h"
#import <AVFoundation/AVFoundation.h>
#import <CoreImage/CoreImage.h>
#import <CoreMedia/CoreMedia.h>
#import <UIKit/UIKit.h>
#import <QuartzCore/QuartzCore.h>
#import <math.h>
#import <ImageIO/ImageIO.h>
#import <errno.h>
#import <fcntl.h>
#import <string.h>
#import <sys/stat.h>
#import <unistd.h>

// Shared with the SpringBoard menu through settings.plist.
typedef NS_ENUM(NSUInteger, VCamMode) {
    VCamModeNone = 0,
    VCamModeImage,
    VCamModeVideo
};

// Decodes the selected video with AVAssetReader and paces the frames against the
// wall clock. Only -initWithAsset:track: and the first -openReaderReportingStages:error:
// run before the source is published; everything else runs on sVideoFrameQueue.
@interface VCamVideoSource : NSObject
@property (atomic, copy) NSString *failureDetail;
@property (atomic) BOOL needsClockResume;
- (instancetype)initWithAsset:(AVURLAsset *)asset track:(AVAssetTrack *)track;
- (BOOL)openReaderReportingStages:(BOOL)reportStages error:(NSString **)errorOut;
- (CVPixelBufferRef)copyFrameForHostTime:(CFTimeInterval)now;
- (void)teardown;
@end

static NSObject *sLock = nil;
static dispatch_once_t sLockOnce;
static CIContext *sRenderContext = nil;
static CGColorSpaceRef sRenderColorSpace = NULL;
static UIImage *sReplacementImage = nil;
static VCamVideoSource *sVideoSource = nil;
static CVPixelBufferRef sCurrentVideoBuffer = NULL;
static CGAffineTransform sVideoPreferredTransform = {1, 0, 0, 1, 0, 0};
static VCamMode sCurrentMode = VCamModeNone;
static BOOL sEnabled = NO;
static CGFloat sOffsetX = 0.0;
static CGFloat sOffsetY = 0.0;
static CGFloat sZoom = 1.0;
static NSInteger sRotation = 0;
static NSUInteger sRefreshTicks = 0;
static NSUInteger sLoadGeneration = 0;
static BOOL sHasReadSettings = NO;
static BOOL sIsLoading = NO;
static NSString *sRequestedPath = nil;
static NSString *sLoadedPath = nil;
static BOOL sHasLoggedFirstRender = NO;
static dispatch_queue_t sVideoFrameQueue = nil;
static dispatch_source_t sVideoFrameTimer = nil;
static BOOL sHasLoggedFirstVideoFrame = NO;
static CFTimeInterval sNextLoadRetryTime = 0.0;
static NSUInteger sLoadFailureCount = 0;
static CFTimeInterval sLastCameraFrameAt = 0.0;
static BOOL sVideoPlaybackPausedByUser = NO;
static BOOL sVideoPausedForCameraIdle = NO;

static void VCamEnsureState(void) {
    dispatch_once(&sLockOnce, ^{
        sLock = [[NSObject alloc] init];
        sRenderContext = [CIContext contextWithOptions:@{
            kCIContextUseSoftwareRenderer: @NO,
            kCIContextCacheIntermediates: @NO
        }];
        sRenderColorSpace = CGColorSpaceCreateDeviceRGB();
        dispatch_queue_attr_t videoQueueAttributes = dispatch_queue_attr_make_with_qos_class(
            DISPATCH_QUEUE_SERIAL, QOS_CLASS_USER_INITIATED, 0);
        sVideoFrameQueue = dispatch_queue_create("com.tinysweet.vcam.video-frame-pump", videoQueueAttributes);
    });
}

static CGFloat VCamNumber(id value, CGFloat fallback) {
    return [value respondsToSelector:@selector(doubleValue)] ? [value doubleValue] : fallback;
}

static void VCamStopVideoFramePumpLocked(void);
static void VCamStopVideoPlaybackLocked(void);

static void VCamStopVideoFramePumpLocked(void) {
    if (sVideoFrameTimer) {
        dispatch_source_cancel(sVideoFrameTimer);
        sVideoFrameTimer = nil;
    }
}

// Pull decoded frames away from BWNodeOutput's real-time camera callback.
// The camera callback only consumes the newest cached pixel buffer; it never
// asks the decoder for a frame itself.
static void VCamStartVideoFramePumpLocked(void) {
    if (sVideoFrameTimer || !sVideoSource || !sEnabled) return;
    if ([VCamCopySetting(VCamVideoPausedKey) boolValue]) return;

    dispatch_source_t timer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0, sVideoFrameQueue);
    if (!timer) return;
    sVideoFrameTimer = timer;
    sVideoSource.needsClockResume = YES;
    VCamSetRuntimeStatus(@"videoFramePump", @"starting");
    dispatch_source_set_timer(timer,
                              dispatch_time(DISPATCH_TIME_NOW, 0),
                              NSEC_PER_SEC / 60,
                              2 * NSEC_PER_MSEC);
    dispatch_source_set_event_handler(timer, ^{
        @autoreleasepool {
        VCamVideoSource *source = nil;
        @synchronized (sLock) {
            if (sCurrentMode != VCamModeVideo || !sEnabled || sVideoSource == nil) return;
            // mediaserverd can keep the decoder alive after Camera is dismissed.
            // Stop decoding while no camera frames are flowing; it will resume
            // automatically when the camera pipeline starts calling us again.
            if (sLastCameraFrameAt > 0.0 && CACurrentMediaTime() - sLastCameraFrameAt > 2.0) {
                sVideoPausedForCameraIdle = YES;
                sHasLoggedFirstVideoFrame = NO;
                VCamStopVideoFramePumpLocked();
                VCamSetRuntimeStatus(@"videoFramePump", @"paused-camera-idle");
                return;
            }
            source = sVideoSource;
        }

        CVPixelBufferRef nextBuffer = [source copyFrameForHostTime:CACurrentMediaTime()];
        NSString *failureDetail = source.failureDetail;
        if (failureDetail.length > 0) {
            if (nextBuffer) CVPixelBufferRelease(nextBuffer);
            @synchronized (sLock) {
                if (sVideoSource == source) {
                    NSString *failedPath = [sLoadedPath copy];
                    VCamStopVideoPlaybackLocked();
                    sCurrentMode = VCamModeNone;
                    // Keep this path marked as handled so a failing codec does not
                    // trigger an endless reload loop on every camera frame.
                    sLoadedPath = failedPath;
                    VCamSetRuntimeStatus(@"videoFramePump", @"player-failed");
                    VCamSetRuntimeStatus(@"videoPlayerError", failureDetail);
                    VCamSetRuntimeStatus(@"mediaState", @"video-player-failed");
                    VCamSetRuntimeStatus(@"mediaDetail", failureDetail);
                    VCamSetRuntimeStatus(@"replacementRendered", @NO);
                }
            }
            return;
        }
        if (!nextBuffer) return;

        BOOL accepted = NO;
        @synchronized (sLock) {
            if (sCurrentMode == VCamModeVideo && sEnabled && sVideoSource == source) {
                CVPixelBufferRef previousBuffer = sCurrentVideoBuffer;
                sCurrentVideoBuffer = nextBuffer; // transfer the +1 reference returned by the reader
                nextBuffer = NULL;
                if (previousBuffer) CVPixelBufferRelease(previousBuffer);
                accepted = YES;
            }
        }
        if (nextBuffer) CVPixelBufferRelease(nextBuffer);

        if (accepted) {
            @synchronized (sLock) {
                if (!sHasLoggedFirstVideoFrame && sCurrentVideoBuffer) {
                    sHasLoggedFirstVideoFrame = YES;
                    size_t width = CVPixelBufferGetWidth(sCurrentVideoBuffer);
                    size_t height = CVPixelBufferGetHeight(sCurrentVideoBuffer);
                    VCamSetRuntimeStatus(@"videoFramePump", @"active");
                    VCamSetRuntimeStatus(@"videoFrameSize", [NSString stringWithFormat:@"%zux%zu", width, height]);
                }
            }
        }
        }
    });
    dispatch_resume(timer);
}

static void VCamStopVideoPlaybackLocked(void) {
    VCamStopVideoFramePumpLocked();
    VCamVideoSource *retiringSource = sVideoSource;
    sVideoSource = nil;
    if (retiringSource && sVideoFrameQueue) {
        // Tear the reader down on the frame queue so it can never race a running tick.
        dispatch_async(sVideoFrameQueue, ^{
            [retiringSource teardown];
        });
    }
    if (sCurrentVideoBuffer) {
        CVPixelBufferRelease(sCurrentVideoBuffer);
        sCurrentVideoBuffer = NULL;
    }
    sVideoPreferredTransform = CGAffineTransformIdentity;
    sHasLoggedFirstVideoFrame = NO;
    sVideoPlaybackPausedByUser = NO;
    sVideoPausedForCameraIdle = NO;
    VCamSetRuntimeStatus(@"videoFramePump", @"stopped");
}

static BOOL VCamDecodeImage(NSString *path, UIImage **imageOut) {
    NSURL *url = [NSURL fileURLWithPath:path];
    CGImageSourceRef imageSource = CGImageSourceCreateWithURL((__bridge CFURLRef)url, NULL);
    if (!imageSource) {
        VCamSetRuntimeStatus(@"mediaState", @"image-open-failed");
        VCamSetRuntimeStatus(@"mediaDetail", @"ImageIO could not open the selected photo from the shared media folder");
        return NO;
    }

    NSDictionary *properties = CFBridgingRelease(CGImageSourceCopyPropertiesAtIndex(imageSource, 0, NULL));
    NSUInteger width = [properties[(NSString *)kCGImagePropertyPixelWidth] unsignedIntegerValue];
    NSUInteger height = [properties[(NSString *)kCGImagePropertyPixelHeight] unsignedIntegerValue];
    NSUInteger maxDimension = MAX(width, height);
    if (maxDimension == 0) maxDimension = 32768;

    NSDictionary *options = @{
        (__bridge NSString *)kCGImageSourceCreateThumbnailFromImageAlways: @YES,
        (__bridge NSString *)kCGImageSourceCreateThumbnailWithTransform: @YES,
        (__bridge NSString *)kCGImageSourceThumbnailMaxPixelSize: @(maxDimension),
        (__bridge NSString *)kCGImageSourceShouldCache: @YES,
        (__bridge NSString *)kCGImageSourceShouldCacheImmediately: @YES
    };
    CGImageRef imageRef = CGImageSourceCreateThumbnailAtIndex(imageSource, 0, (__bridge CFDictionaryRef)options);
    CFRelease(imageSource);
    if (!imageRef) {
        VCamSetRuntimeStatus(@"mediaState", @"image-decode-failed");
        VCamSetRuntimeStatus(@"mediaDetail", @"ImageIO could not decode the selected photo at its original pixel dimensions");
        return NO;
    }

    size_t decodedWidth = CGImageGetWidth(imageRef);
    size_t decodedHeight = CGImageGetHeight(imageRef);
    UIImage *image = [UIImage imageWithCGImage:imageRef scale:1.0 orientation:UIImageOrientationUp];
    CGImageRelease(imageRef);
    if (imageOut) *imageOut = image;

    VCamSetRuntimeStatus(@"mediaState", @"loaded-image");
    VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"Photo decoded (%zux%zu, original pixel dimensions)", decodedWidth, decodedHeight]);
    return YES;
}

// Shown by the SpringBoard menu next to "Media: LOADING". If loading ever hangs,
// the last stage written here tells us which AVFoundation call never returned.
static void VCamVideoStage(NSString *stage) {
    VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"Preparing video: %@", stage]);
}

@implementation VCamVideoSource {
    AVURLAsset *_asset;
    AVAssetTrack *_track;
    AVAssetReader *_reader;
    AVAssetReaderTrackOutput *_output;
    CMSampleBufferRef _pending;   // next frame: already decoded, not yet due
    CFTimeInterval _clockStart;   // host time at which relative time 0 is shown
    double _basePTS;              // presentation time of the first frame of this pass
    BOOL _hasBase;
    double _lastShownTime;        // relative time of the last frame handed out
}

- (instancetype)initWithAsset:(AVURLAsset *)asset track:(AVAssetTrack *)track {
    self = [super init];
    if (self) {
        _asset = asset;
        _track = track;
    }
    return self;
}

- (void)dealloc {
    [self teardown];
}

- (void)teardown {
    if (_reader && _reader.status == AVAssetReaderStatusReading) [_reader cancelReading];
    _reader = nil;
    _output = nil;
    if (_pending) {
        CFRelease(_pending);
        _pending = NULL;
    }
}

- (BOOL)openReaderReportingStages:(BOOL)reportStages error:(NSString **)errorOut {
    [self teardown];
    if (reportStages) VCamVideoStage(@"4/5 creating video reader");
    NSError *error = nil;
    AVAssetReader *reader = [[AVAssetReader alloc] initWithAsset:_asset error:&error];
    if (!reader) {
        if (errorOut) *errorOut = error.localizedDescription ?: @"AVAssetReader could not open the selected video";
        return NO;
    }
    NSDictionary *settings = @{
        (NSString *)kCVPixelBufferPixelFormatTypeKey: @(kCVPixelFormatType_32BGRA)
    };
    AVAssetReaderTrackOutput *output = [[AVAssetReaderTrackOutput alloc] initWithTrack:_track
                                                                         outputSettings:settings];
    output.alwaysCopiesSampleData = NO;
    if (![reader canAddOutput:output]) {
        if (errorOut) *errorOut = @"AVAssetReader cannot create a decoded video output";
        return NO;
    }
    [reader addOutput:output];
    if (reportStages) VCamVideoStage(@"5/5 starting video decoder");
    if (![reader startReading]) {
        if (errorOut) *errorOut = reader.error.localizedDescription ?: @"AVAssetReader failed to start";
        return NO;
    }
    _reader = reader;
    _output = output;
    _hasBase = NO;
    return YES;
}

// Called only on the frame queue. Returns the newest frame that is due at
// hostTime (+1 reference) or NULL when there is nothing new to show.
- (CVPixelBufferRef)copyFrameForHostTime:(CFTimeInterval)now {
    if (self.needsClockResume) {
        self.needsClockResume = NO;
        _clockStart = now - _lastShownTime;
    }

    CVPixelBufferRef result = NULL;
    for (int attempt = 0; attempt < 4; attempt++) {
        if (!_pending) {
            if (!_reader || _reader.status != AVAssetReaderStatusReading) {
                if (_reader && _reader.status == AVAssetReaderStatusFailed) {
                    self.failureDetail = _reader.error.localizedDescription ?: @"AVAssetReader failed while decoding the video";
                    break;
                }
                // Reached the end of the file: start over so the video loops.
                NSString *reopenError = nil;
                if (![self openReaderReportingStages:NO error:&reopenError]) {
                    self.failureDetail = reopenError ?: @"AVAssetReader could not restart the video";
                    break;
                }
            }
            _pending = [_output copyNextSampleBuffer];
            if (!_pending) {
                if (_reader.status == AVAssetReaderStatusFailed) {
                    self.failureDetail = _reader.error.localizedDescription ?: @"AVAssetReader failed while decoding the video";
                }
                break;
            }
            if (!_hasBase) {
                double firstPTS = CMTimeGetSeconds(CMSampleBufferGetPresentationTimeStamp(_pending));
                _basePTS = isfinite(firstPTS) ? firstPTS : 0.0;
                _clockStart = now;
                _lastShownTime = 0.0;
                _hasBase = YES;
            }
        }

        double pts = CMTimeGetSeconds(CMSampleBufferGetPresentationTimeStamp(_pending));
        double relative = isfinite(pts) ? MAX(0.0, pts - _basePTS) : _lastShownTime;
        double elapsed = now - _clockStart;
        if (relative > elapsed) break;                      // not due yet, keep it for the next tick
        if (elapsed - relative > 0.25) _clockStart = now - relative; // far behind: resync instead of racing ahead

        CVImageBufferRef image = CMSampleBufferGetImageBuffer(_pending);
        if (image) {
            if (result) CVPixelBufferRelease(result);
            result = CVPixelBufferRetain(image);
        }
        _lastShownTime = relative;
        CFRelease(_pending);
        _pending = NULL;
    }
    return result;
}

@end

static BOOL VCamPrepareVideo(NSString *path,
                             VCamVideoSource **sourceOut,
                             CGAffineTransform *preferredTransformOut) {
    if (sourceOut) *sourceOut = nil;
    if (preferredTransformOut) *preferredTransformOut = CGAffineTransformIdentity;

    VCamVideoStage(@"1/5 creating asset");
    NSURL *url = [NSURL fileURLWithPath:path];
    AVURLAsset *asset = [AVURLAsset URLAssetWithURL:url options:@{ AVURLAssetPreferPreciseDurationAndTimingKey: @NO }];

    // -[AVAsset tracksWithMediaType:] loads synchronously and can block forever
    // when AVFoundation runs inside mediaserverd. Load the tracks asynchronously
    // and give up after a bounded wait instead of hanging this worker thread.
    VCamVideoStage(@"2/5 loading video tracks (waits up to 10 s)");
    dispatch_semaphore_t tracksLoaded = dispatch_semaphore_create(0);
    [asset loadValuesAsynchronouslyForKeys:@[@"tracks"] completionHandler:^{
        dispatch_semaphore_signal(tracksLoaded);
    }];
    if (dispatch_semaphore_wait(tracksLoaded, dispatch_time(DISPATCH_TIME_NOW, 10 * NSEC_PER_SEC)) != 0) {
        VCamSetRuntimeStatus(@"mediaDetail", @"TIMEOUT at stage 2/5: AVFoundation did not finish loading the video tracks inside mediaserverd within 10 s");
        return NO;
    }
    NSError *tracksError = nil;
    if ([asset statusOfValueForKey:@"tracks" error:&tracksError] != AVKeyValueStatusLoaded) {
        VCamSetRuntimeStatus(@"mediaDetail", tracksError.localizedDescription
                             ? [NSString stringWithFormat:@"Stage 2/5 failed: %@", tracksError.localizedDescription]
                             : @"Stage 2/5 failed: AVFoundation could not load the video tracks");
        return NO;
    }
    NSArray<AVAssetTrack *> *tracks = [asset tracksWithMediaType:AVMediaTypeVideo];
    AVAssetTrack *videoTrack = tracks.firstObject;
    if (!videoTrack) {
        VCamSetRuntimeStatus(@"mediaState", @"video-track-missing");
        VCamSetRuntimeStatus(@"mediaDetail", @"The selected file contains no readable video track");
        return NO;
    }

    // The orientation is a lazily loaded track property; read it with a bounded
    // wait as well and fall back to "no rotation" if it is not available in time.
    VCamVideoStage(@"3/5 reading video orientation (waits up to 5 s)");
    CGAffineTransform trackTransform = CGAffineTransformIdentity;
    dispatch_semaphore_t orientationLoaded = dispatch_semaphore_create(0);
    [videoTrack loadValuesAsynchronouslyForKeys:@[@"preferredTransform"] completionHandler:^{
        dispatch_semaphore_signal(orientationLoaded);
    }];
    if (dispatch_semaphore_wait(orientationLoaded, dispatch_time(DISPATCH_TIME_NOW, 5 * NSEC_PER_SEC)) == 0 &&
        [videoTrack statusOfValueForKey:@"preferredTransform" error:NULL] == AVKeyValueStatusLoaded) {
        trackTransform = videoTrack.preferredTransform;
    }

    // AVPlayer / AVPlayerItem are intentionally not used: creating a player item
    // inside mediaserverd never completes on some devices (the process is killed
    // a few seconds later). AVAssetReader only needs the track that already loaded.
    VCamVideoSource *source = [[VCamVideoSource alloc] initWithAsset:asset track:videoTrack];
    NSString *openError = nil;
    if (![source openReaderReportingStages:YES error:&openError]) {
        VCamSetRuntimeStatus(@"mediaState", @"video-decode-start-failed");
        VCamSetRuntimeStatus(@"mediaDetail", openError ?: @"AVAssetReader failed to start");
        return NO;
    }

    if (sourceOut) *sourceOut = source;
    if (preferredTransformOut) *preferredTransformOut = trackTransform;

    VCamSetRuntimeStatus(@"mediaState", @"loaded-video");
    VCamSetRuntimeStatus(@"mediaDetail", @"Video decoder ready (AVAssetReader, no AVPlayer); imported video is normalized to a camera-friendly 1080p/30 FPS stream when supported");
    return YES;
}

static BOOL VCamOpenSelectedMediaForRead(NSString *path) {
    if (path.length == 0) {
        VCamSetRuntimeStatus(@"mediaFileAccess", @"failed");
        VCamSetRuntimeStatus(@"mediaState", @"file-not-readable");
        VCamSetRuntimeStatus(@"mediaDetail", @"The selected media path is empty");
        return NO;
    }

    // The selected media is copied by SpringBoard into /tmp/VCamMedia.
    // This intentionally uses the same direct filesystem access pattern as
    // the original working /tmp/test.png implementation, without sandbox tokens.
    errno = 0;
    int descriptor = open(path.fileSystemRepresentation, O_RDONLY | O_CLOEXEC);
    if (descriptor < 0) {
        int savedErrno = errno;
        VCamSetRuntimeStatus(@"mediaFileAccess", @"failed");
        VCamSetRuntimeStatus(@"mediaFileOpenErrno", @(savedErrno));
        VCamSetRuntimeStatus(@"mediaState", @"file-not-readable");
        VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"open() failed (errno %d: %s); path %@", savedErrno, strerror(savedErrno), path]);
        return NO;
    }

    struct stat fileInfo;
    BOOL regularFile = fstat(descriptor, &fileInfo) == 0 && S_ISREG(fileInfo.st_mode);
    int statErrno = errno;
    close(descriptor);
    if (!regularFile) {
        VCamSetRuntimeStatus(@"mediaFileAccess", @"failed");
        VCamSetRuntimeStatus(@"mediaState", @"invalid-file");
        VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"The selected path is not a regular file (errno %d: %s)", statErrno, strerror(statErrno)]);
        return NO;
    }

    VCamSetRuntimeStatus(@"mediaFileAccess", @"readable");
    VCamSetRuntimeStatus(@"mediaFileOpenErrno", @0);
    VCamSetRuntimeStatus(@"mediaFileSize", @((unsigned long long)fileInfo.st_size));
    VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"File readable by mediaserverd (%llu bytes)", (unsigned long long)fileInfo.st_size]);
    return YES;
}

static BOOL VCamDecodeMedia(NSString *path,
                            UIImage **imageOut,
                            VCamVideoSource **sourceOut,
                            CGAffineTransform *preferredTransformOut) {
    if (imageOut) *imageOut = nil;
    if (sourceOut) *sourceOut = nil;
    if (preferredTransformOut) *preferredTransformOut = CGAffineTransformIdentity;

    if (!VCamOpenSelectedMediaForRead(path)) return NO;

    NSString *extension = path.pathExtension.lowercaseString;
    NSSet *videoExtensions = [NSSet setWithArray:@[@"mp4", @"mov", @"m4v", @"3gp", @"3g2", @"avi", @"mts", @"m2ts", @"qt"]];
    NSString *mediaType = VCamCopySetting(VCamMediaTypeKey);
    if ([mediaType isEqualToString:@"video"] || [videoExtensions containsObject:extension]) {
        return VCamPrepareVideo(path, sourceOut, preferredTransformOut);
    }
    return VCamDecodeImage(path, imageOut);
}

void loadReplacementMedia(void) {
    VCamEnsureState();

    NSString *newPath = nil;
    NSUInteger generation = 0;
    BOOL shouldStartLoad = NO;

    @synchronized (sLock) {
        sLastCameraFrameAt = CACurrentMediaTime();
        sRefreshTicks++;
        if (sHasReadSettings && (sRefreshTicks % 10) != 0) return;
        sHasReadSettings = YES;

        id enabledValue = VCamCopySetting(VCamEnabledKey);
        if (enabledValue) {
            sEnabled = [enabledValue boolValue];
            VCamSetRuntimeStatus(@"enabledSettingRead", @"confirmed");
        } else {
            // notify_get_state can briefly fail while SpringBoard is publishing
            // the value. A transient miss must not restore the live camera feed.
            // Preserve the last confirmed Enabled value instead of defaulting OFF.
            VCamSetRuntimeStatus(@"enabledSettingRead", @"transient-miss-kept-last-value");
        }
        VCamSetRuntimeStatus(@"replacementEnabled", @(sEnabled));
        sOffsetX = MAX(-1.0, MIN(1.0, VCamNumber(VCamCopySetting(VCamOffsetXKey), 0.0)));
        sOffsetY = MAX(-1.0, MIN(1.0, VCamNumber(VCamCopySetting(VCamOffsetYKey), 0.0)));
        sZoom = MAX(0.1, MIN(10.0, VCamNumber(VCamCopySetting(VCamZoomKey), 1.0)));
        sRotation = (NSInteger)VCamNumber(VCamCopySetting(VCamRotationKey), 0);
        BOOL videoPaused = [VCamCopySetting(VCamVideoPausedKey) boolValue];

        id pathValue = VCamCopySetting(VCamMediaPathKey);
        NSString *observedPath = [pathValue isKindOfClass:[NSString class]] ? [(NSString *)pathValue copy] : nil;
        NSString *observedType = VCamCopySetting(VCamMediaTypeKey);
        VCamSetRuntimeStatus(@"mediaSelectionReceived", @(observedPath.length > 0));
        VCamSetRuntimeStatus(@"mediaSelectionTransport", @"Darwin Notify");
        VCamSetRuntimeStatus(@"mediaSelectionFilename", observedPath.lastPathComponent ?: @"");
        VCamSetRuntimeStatus(@"mediaSelectionType", observedType ?: @"unknown");

        if (!sEnabled) {
            if (sCurrentMode == VCamModeVideo) {
                VCamStopVideoFramePumpLocked();
                VCamSetRuntimeStatus(@"videoFramePump", @"paused-replacement-disabled");
            }
            VCamSetRuntimeStatus(@"replacementRendered", @NO);
            VCamSetRuntimeStatus(@"mediaState", @"disabled");
            VCamSetRuntimeStatus(@"mediaDetail", @"Replacement is turned off");
            return;
        }
        if (![pathValue isKindOfClass:[NSString class]] || [(NSString *)pathValue length] == 0) {
            VCamSetRuntimeStatus(@"replacementRendered", @NO);
            VCamSetRuntimeStatus(@"mediaState", @"no-selection");
            VCamSetRuntimeStatus(@"mediaDetail", @"mediaserverd has not received a selected media path from SpringBoard");
            return;
        }
        newPath = observedPath;
        if ([newPath isEqualToString:sLoadedPath]) {
            if (sCurrentMode == VCamModeVideo && sVideoSource) {
                if (videoPaused) {
                    if (!sVideoPlaybackPausedByUser) {
                        sVideoPlaybackPausedByUser = YES;
                        VCamStopVideoFramePumpLocked();
                        VCamSetRuntimeStatus(@"videoFramePump", @"paused-by-user");
                    }
                } else if (sVideoPlaybackPausedByUser || sVideoPausedForCameraIdle || !sVideoFrameTimer) {
                    sVideoPlaybackPausedByUser = NO;
                    sVideoPausedForCameraIdle = NO;
                    VCamStartVideoFramePumpLocked();
                }
            }
            return;
        }
        if (sIsLoading && [newPath isEqualToString:sRequestedPath]) return;
        if (sNextLoadRetryTime > CACurrentMediaTime() && [newPath isEqualToString:sRequestedPath]) return;

        sLoadGeneration++;
        generation = sLoadGeneration;
        if (sRequestedPath && ![newPath isEqualToString:sRequestedPath]) {
            sLoadFailureCount = 0;
        }
        sRequestedPath = [newPath copy];
        sNextLoadRetryTime = 0.0;
        sIsLoading = YES;
        sCurrentMode = VCamModeNone;
        sReplacementImage = nil;
        VCamStopVideoPlaybackLocked();
        sHasLoggedFirstRender = NO;
        VCamSetRuntimeStatus(@"replacementRendered", @NO);
        VCamSetRuntimeStatus(@"replacementRenderedAt", nil);
        VCamSetRuntimeStatus(@"renderError", nil);
        VCamSetRuntimeStatus(@"mediaState", @"loading");
        VCamSetRuntimeStatus(@"mediaDetail", @"Opening selected media in the camera service");
        shouldStartLoad = YES;
    }

    if (!shouldStartLoad) return;
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        @autoreleasepool {
            UIImage *image = nil;
            VCamVideoSource *videoSource = nil;
            CGAffineTransform preferredTransform = CGAffineTransformIdentity;
            BOOL success = VCamDecodeMedia(newPath, &image, &videoSource, &preferredTransform);

            @synchronized (sLock) {
                if (generation != sLoadGeneration) {
                    if (videoSource) {
                        dispatch_async(sVideoFrameQueue, ^{
                            [videoSource teardown];
                        });
                    }
                    return;
                }
                sIsLoading = NO;
                if (!success) {
                    sLoadedPath = nil;
                    sRequestedPath = [newPath copy];
                    sLoadFailureCount++;
                    CFTimeInterval retryDelay = MIN(30.0, 3.0 * (double)sLoadFailureCount);
                    sNextLoadRetryTime = CACurrentMediaTime() + retryDelay;
                    VCamSetRuntimeStatus(@"mediaRetryCount", @(sLoadFailureCount));
                    VCamSetRuntimeStatus(@"mediaRetryAfterSeconds", @(retryDelay));
                    VCamSetRuntimeStatus(@"mediaState", @"load-failed");
                    VCamSetRuntimeStatus(@"replacementRendered", @NO);
                    sCurrentMode = VCamModeNone;
                    sReplacementImage = nil;
                    VCamStopVideoPlaybackLocked();
                    return;
                }
                sLoadedPath = [newPath copy];
                sRequestedPath = nil;
                sLoadFailureCount = 0;
                sNextLoadRetryTime = 0.0;
                VCamSetRuntimeStatus(@"mediaRetryCount", @0);
                if (image) {
                    sReplacementImage = image;
                    sCurrentMode = VCamModeImage;
                    VCamSetRuntimeStatus(@"mediaDetail", [NSString stringWithFormat:@"Photo ready (%zux%zu)", CGImageGetWidth(image.CGImage), CGImageGetHeight(image.CGImage)]);
                } else {
                    sVideoSource = videoSource;
                    sVideoPreferredTransform = preferredTransform;
                    sCurrentMode = VCamModeVideo;
                    sReplacementImage = nil;
                    sVideoPlaybackPausedByUser = [VCamCopySetting(VCamVideoPausedKey) boolValue];
                    sVideoPausedForCameraIdle = NO;
                    if (!sEnabled || sVideoPlaybackPausedByUser) {
                        if (sVideoPlaybackPausedByUser) VCamSetRuntimeStatus(@"videoFramePump", @"paused-by-user");
                    } else {
                        VCamStartVideoFramePumpLocked();
                    }
                }
            }
        }
    });
}

void drawReplacementOntoBuffer(CVPixelBufferRef targetBuffer) {
    if (!targetBuffer) return;
    VCamEnsureState();

    UIImage *replacementImage = nil;
    CGAffineTransform videoTransform = CGAffineTransformIdentity;
    VCamMode mode = VCamModeNone;
    CGFloat offsetXValue = 0.0;
    CGFloat offsetYValue = 0.0;
    CGFloat zoomValue = 1.0;
    NSInteger rotationValue = 0;
    CIContext *renderContext = nil;
    CGColorSpaceRef renderColorSpace = NULL;

    @synchronized (sLock) {
        if (!sEnabled || sCurrentMode == VCamModeNone || !sRenderContext) return;
        mode = sCurrentMode;
        replacementImage = sReplacementImage;
        videoTransform = sVideoPreferredTransform;
        offsetXValue = sOffsetX;
        offsetYValue = sOffsetY;
        zoomValue = sZoom;
        rotationValue = sRotation;
        renderContext = sRenderContext;
        renderColorSpace = sRenderColorSpace;
    }

    CIImage *source = nil;
    CVPixelBufferRef videoBuffer = NULL;
    if (mode == VCamModeImage && replacementImage.CGImage) {
        source = [CIImage imageWithCGImage:replacementImage.CGImage];
    } else if (mode == VCamModeVideo) {
        // Frame extraction happens on sVideoFrameQueue. Camera delivery only
        // retains the latest frame, avoiding AVPlayer synchronization on this hot path.
        @synchronized (sLock) {
            if (sCurrentVideoBuffer) {
                videoBuffer = sCurrentVideoBuffer;
                CVPixelBufferRetain(videoBuffer);
            }
        }
        if (videoBuffer) {
            source = [CIImage imageWithCVPixelBuffer:videoBuffer];
            if (!CGAffineTransformIsIdentity(videoTransform)) {
                source = [source imageByApplyingTransform:videoTransform];
            }
            CGRect videoExtent = source.extent;
            source = [source imageByApplyingTransform:CGAffineTransformMakeTranslation(-videoExtent.origin.x, -videoExtent.origin.y)];
        }
    }

    if (!source) {
        if (videoBuffer) CVPixelBufferRelease(videoBuffer);
        return;
    }

    size_t targetWidth = CVPixelBufferGetWidth(targetBuffer);
    size_t targetHeight = CVPixelBufferGetHeight(targetBuffer);
    if (targetWidth == 0 || targetHeight == 0) {
        if (videoBuffer) CVPixelBufferRelease(videoBuffer);
        return;
    }
    CGRect targetRect = CGRectMake(0, 0, targetWidth, targetHeight);

    CGRect sourceExtent = source.extent;
    source = [source imageByApplyingTransform:CGAffineTransformMakeTranslation(-sourceExtent.origin.x,
                                                                                -sourceExtent.origin.y)];
    CGFloat radians = ((CGFloat)(rotationValue % 360)) * (CGFloat)M_PI / 180.0;
    if (fabs(radians) > 0.0001) source = [source imageByApplyingTransform:CGAffineTransformMakeRotation(radians)];

    CGRect rotatedExtent = source.extent;
    CGFloat fitScale = MAX((CGFloat)targetWidth / MAX(rotatedExtent.size.width, 1.0),
                           (CGFloat)targetHeight / MAX(rotatedExtent.size.height, 1.0));
    CGFloat scale = fitScale * zoomValue;
    source = [source imageByApplyingTransform:CGAffineTransformMakeScale(scale, scale)];
    CGRect scaledExtent = source.extent;

    CGFloat translateX = ((CGFloat)targetWidth - scaledExtent.size.width) / 2.0 - scaledExtent.origin.x;
    CGFloat translateY = ((CGFloat)targetHeight - scaledExtent.size.height) / 2.0 - scaledExtent.origin.y;
    // Offsets are stored in screen coordinates (UIKit: +X right, +Y down).
    // Core Image uses a Y-up coordinate system, so invert only Y at render time.
    translateX += offsetXValue * (CGFloat)targetWidth;
    translateY -= offsetYValue * (CGFloat)targetHeight;
    source = [source imageByApplyingTransform:CGAffineTransformMakeTranslation(translateX, translateY)];

    CIImage *background = [[CIImage imageWithColor:[CIColor colorWithRed:0 green:0 blue:0 alpha:1]]
                          imageByCroppingToRect:targetRect];
    CIImage *finalImage = [[source imageByCompositingOverImage:background] imageByCroppingToRect:targetRect];
    [renderContext render:finalImage toCVPixelBuffer:targetBuffer bounds:targetRect colorSpace:renderColorSpace];

    if (videoBuffer) CVPixelBufferRelease(videoBuffer);

    if (!sHasLoggedFirstRender) {
        @synchronized (sLock) {
            if (!sHasLoggedFirstRender) {
                sHasLoggedFirstRender = YES;
                VCamSetRuntimeStatus(@"replacementRendered", @YES);
                VCamSetRuntimeStatus(@"replacementRenderedAt", [NSDate date]);
                VCamSetRuntimeStatus(@"renderedFrameSize", [NSString stringWithFormat:@"%zux%zu", targetWidth, targetHeight]);
            }
        }
    }
}
