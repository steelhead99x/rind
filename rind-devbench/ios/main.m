// RindBench v14 (all libraries): a data-driven list of every library x
// operation this build of rind-devbench can time, picked per run.
// The catalog (rows, libraries, sections) comes from the Rust core; nothing
// here names an operation or a library.
#import <UIKit/UIKit.h>
#include <netdb.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <unistd.h>
#include <poll.h>

extern char *devbench_catalog_json(void);
extern int devbench_start(const char *config);
extern char *devbench_status_json(void);
extern void devbench_stop(void);
extern void devbench_free(char *p);
extern void devbench_setenv(const char *key, const char *value);

static id JSON(char *p) {
  if (!p) return nil;
  NSData *d = [NSData dataWithBytes:p length:strlen(p)];
  devbench_free(p);
  return [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
}
static NSString *Fmt(double ns) {
  if (ns >= 1e6) return [NSString stringWithFormat:@"%.3f ms", ns / 1e6];
  if (ns >= 1e3) return [NSString stringWithFormat:@"%.3f µs", ns / 1e3];
  return [NSString stringWithFormat:@"%.1f ns", ns];
}
// TCP connect with a timeout: is the collector listening? (The run connects again itself.)
static BOOL Reachable(NSString *host, int port, int ms) {
  struct addrinfo hints = {0}, *res = NULL; hints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo(host.UTF8String, [NSString stringWithFormat:@"%d", port].UTF8String, &hints, &res) != 0 || !res) return NO;
  int fd = socket(res->ai_family, SOCK_STREAM, 0); BOOL ok = NO;
  if (fd >= 0) {
    fcntl(fd, F_SETFL, O_NONBLOCK);
    if (connect(fd, res->ai_addr, res->ai_addrlen) == 0) ok = YES;
    else { struct pollfd p = {fd, POLLOUT, 0}; if (poll(&p, 1, ms) == 1) { int e = 0; socklen_t l = sizeof e; getsockopt(fd, SOL_SOCKET, SO_ERROR, &e, &l); ok = e == 0; } }
    close(fd);
  }
  freeaddrinfo(res); return ok;
}
#define C_BG [UIColor colorWithRed:0.06 green:0.07 blue:0.09 alpha:1]
#define C_CARD [UIColor colorWithRed:0.11 green:0.12 blue:0.15 alpha:1]
#define C_MUTED [UIColor colorWithWhite:0.65 alpha:1]
#define C_ACCENT [UIColor colorWithRed:0.98 green:0.75 blue:0.20 alpha:1]

@interface VC : UIViewController
@end

@implementation VC {
  UIStackView *root, *libBox, *secBox;
  UILabel *deviceLbl, *statusLbl, *resultsLbl, *collectorLbl;
  UISwitch *agree; UISegmentedControl *preset;
  UIButton *startBtn, *stopBtn, *clearBtn;
  BOOL running;
  NSDictionary *catalog;
  NSMutableDictionary<NSString *, UISwitch *> *libSw, *secSw;
  NSTimer *timer;
}

- (UILabel *)label:(NSString *)t size:(CGFloat)s weight:(UIFontWeight)w color:(UIColor *)c {
  UILabel *l = [UILabel new]; l.text = t; l.numberOfLines = 0; l.textColor = c ?: UIColor.whiteColor;
  l.font = [UIFont systemFontOfSize:s weight:w]; return l;
}
- (UIStackView *)card:(NSArray<UIView *> *)views {
  UIStackView *s = [[UIStackView alloc] initWithArrangedSubviews:views];
  s.axis = UILayoutConstraintAxisVertical; s.spacing = 10; s.layoutMarginsRelativeArrangement = YES;
  s.layoutMargins = UIEdgeInsetsMake(16, 16, 16, 16); s.backgroundColor = C_CARD; s.layer.cornerRadius = 14; return s;
}
- (UIStackView *)switchRow:(NSString *)title on:(BOOL)on enabled:(BOOL)en into:(NSMutableDictionary *)dict key:(NSString *)key {
  UISwitch *sw = [UISwitch new]; sw.on = on; sw.enabled = en; sw.onTintColor = C_ACCENT; dict[key] = sw;
  UILabel *l = [self label:title size:16 weight:UIFontWeightRegular color:en ? nil : C_MUTED];
  UIStackView *r = [[UIStackView alloc] initWithArrangedSubviews:@[sw, l]]; r.spacing = 12; r.alignment = UIStackViewAlignmentCenter; return r;
}
- (UIButton *)button:(NSString *)t action:(SEL)a {
  UIButton *b = [UIButton buttonWithType:UIButtonTypeSystem]; [b setTitle:t forState:UIControlStateNormal];
  b.titleLabel.font = [UIFont systemFontOfSize:18 weight:UIFontWeightSemibold]; b.tintColor = UIColor.blackColor;
  b.backgroundColor = C_ACCENT; b.layer.cornerRadius = 10; b.contentEdgeInsets = UIEdgeInsetsMake(10, 20, 10, 20);
  [b addTarget:self action:a forControlEvents:UIControlEventTouchUpInside]; return b;
}

- (void)viewDidLoad {
  [super viewDidLoad];
  self.view.backgroundColor = C_BG;
  libSw = [NSMutableDictionary new]; secSw = [NSMutableDictionary new];
  UIScrollView *sc = [UIScrollView new]; sc.translatesAutoresizingMaskIntoConstraints = NO; [self.view addSubview:sc];
  root = [UIStackView new]; root.axis = UILayoutConstraintAxisVertical; root.spacing = 16; root.translatesAutoresizingMaskIntoConstraints = NO;
  [sc addSubview:root];
  UILayoutGuide *g = self.view.safeAreaLayoutGuide;
  [NSLayoutConstraint activateConstraints:@[
    [sc.topAnchor constraintEqualToAnchor:g.topAnchor], [sc.bottomAnchor constraintEqualToAnchor:g.bottomAnchor],
    [sc.leadingAnchor constraintEqualToAnchor:g.leadingAnchor], [sc.trailingAnchor constraintEqualToAnchor:g.trailingAnchor],
    [root.topAnchor constraintEqualToAnchor:sc.contentLayoutGuide.topAnchor constant:24],
    [root.bottomAnchor constraintEqualToAnchor:sc.contentLayoutGuide.bottomAnchor constant:-24],
    [root.centerXAnchor constraintEqualToAnchor:sc.centerXAnchor],
    [root.widthAnchor constraintEqualToAnchor:sc.widthAnchor constant:-48],
  ]];
  [root addArrangedSubview:[self label:@"RindBench — every library" size:30 weight:UIFontWeightHeavy color:nil]];
  [root addArrangedSubview:[self label:@"Times rind and the libraries it is compared with (aws-lc-rs, ring, RustCrypto, graviola, libcrux, verified-garbage) on this iPad, with rind-bench's own benchmarks. Pick what to run below. Nothing runs or connects until you agree and press Start test." size:15 weight:UIFontWeightRegular color:C_MUTED]];
  deviceLbl = [self label:@"Reading the list of tests…" size:14 weight:UIFontWeightMedium color:C_ACCENT];
  [root addArrangedSubview:[self card:@[deviceLbl]]];
  libBox = [self card:@[[self label:@"Libraries" size:20 weight:UIFontWeightBold color:nil]]];
  secBox = [self card:@[[self label:@"Operations" size:20 weight:UIFontWeightBold color:nil]]];
  [root addArrangedSubview:libBox]; [root addArrangedSubview:secBox];
  preset = [[UISegmentedControl alloc] initWithItems:@[@"Quick: 1 round, 5 × 50 ms", @"Full: 3 rounds, 10 × 100 ms"]];
  preset.selectedSegmentIndex = 0;
  agree = [UISwitch new]; agree.onTintColor = C_ACCENT; [agree addTarget:self action:@selector(agreeChanged) forControlEvents:UIControlEventValueChanged];
  UILabel *agreeL = [self label:@"I agree to the above: the run keeps the CPU busy (minutes on Quick, longer on Full), warms the iPad, and sends only timings and the model, chip, iPadOS version and CPU features to the computer that installed this app. No name, account, serial or location." size:15 weight:UIFontWeightRegular color:nil];
  UIStackView *agreeRow = [[UIStackView alloc] initWithArrangedSubviews:@[agree, agreeL]]; agreeRow.spacing = 12; agreeRow.alignment = UIStackViewAlignmentCenter;
  startBtn = [self button:@"Start test" action:@selector(startTapped)]; startBtn.enabled = NO; startBtn.alpha = 0.4;
  stopBtn = [self button:@"Stop" action:@selector(stopTapped)]; stopBtn.hidden = YES;
  clearBtn = [self button:@"Clear" action:@selector(clearTapped)]; clearBtn.hidden = YES;
  UIStackView *btns = [[UIStackView alloc] initWithArrangedSubviews:@[startBtn, stopBtn, clearBtn]]; btns.spacing = 12;
  collectorLbl = [self label:@"Results go to: looking for the computer that installed this app…" size:14 weight:UIFontWeightRegular color:C_MUTED];
  [root addArrangedSubview:[self card:@[[self label:@"Timing" size:20 weight:UIFontWeightBold color:nil], preset, agreeRow, collectorLbl, btns]]];
  [self findCollector];
  statusLbl = [self label:@"" size:15 weight:UIFontWeightMedium color:nil];
  resultsLbl = [self label:@"" size:12 weight:UIFontWeightRegular color:nil];
  resultsLbl.font = [UIFont monospacedSystemFontOfSize:12 weight:UIFontWeightRegular];
  [root addArrangedSubview:[self card:@[[self label:@"Status" size:20 weight:UIFontWeightBold color:nil], statusLbl, resultsLbl]]];
  [root addArrangedSubview:[self label:@"An unofficial community tool, not run or endorsed by the rind maintainers." size:12 weight:UIFontWeightRegular color:C_MUTED]];
  // rind-bench's rustls rows read their certificates while the list is made, not only when timed.
  devbench_setenv("RIND_BENCH_KEYS_DIR", [NSBundle.mainBundle.resourcePath stringByAppendingPathComponent:@"keys"].UTF8String);
  dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
    NSDictionary *cat = JSON(devbench_catalog_json());
    dispatch_async(dispatch_get_main_queue(), ^{ [self loaded:cat]; });
  });
}

- (void)loaded:(NSDictionary *)cat {
  catalog = cat;
  if (!cat) { deviceLbl.text = @"Could not read the list of tests."; return; }
  NSDictionary *d = cat[@"device"];
  NSString *sha = [cat[@"rind_commit"] length] > 12 ? [cat[@"rind_commit"] substringToIndex:12] : cat[@"rind_commit"];
  deviceLbl.text = [NSString stringWithFormat:@"%@ · %@ · %@\nrind %@ · %lu rows · %lu libraries · OpenSSL %@",
    d[@"product"], d[@"cpu"], d[@"os"], sha, (unsigned long)[cat[@"rows"] count], (unsigned long)[cat[@"libraries"] count],
    [cat[@"openssl"] boolValue] ? @"built in" : @"not in this build"];
  NSMutableDictionary *lc = [NSMutableDictionary new], *sc = [NSMutableDictionary new];
  for (NSDictionary *r in cat[@"rows"]) { lc[r[@"library"]] = @([lc[r[@"library"]] intValue] + 1); sc[r[@"section"]] = @([sc[r[@"section"]] intValue] + 1); }
  for (NSString *l in cat[@"libraries"])
    [libBox addArrangedSubview:[self switchRow:[NSString stringWithFormat:@"%@  (%@ rows)", l, lc[l]] on:YES enabled:YES into:libSw key:l]];
  for (NSString *s in cat[@"sections"]) {
    int n = [sc[s] intValue];
    [secBox addArrangedSubview:[self switchRow:[NSString stringWithFormat:@"%@  (%d rows)", s, n] on:n > 0 && ![s hasPrefix:@"More: "] enabled:n > 0 into:secSw key:s]];
  }
  statusLbl.text = [NSString stringWithFormat:@"Ready. %lu report operations have no row on this platform.", (unsigned long)[cat[@"operations_without_rows"] count]];
}

// The collector fills itself in from the address baked in at build time (BenchHost/BenchPort); shown, never typed.
- (void)findCollector {
  NSString *host = [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchHost"];
  NSNumber *port = [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchPort"];
  if (!host.length || !port) { collectorLbl.text = @"Results are saved on this iPad (no collector in this build)."; return; }
  dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
    BOOL ok = Reachable(host, port.intValue, 800);
    dispatch_async(dispatch_get_main_queue(), ^{
      self->collectorLbl.text = ok ? [NSString stringWithFormat:@"Results go to: %@:%@ (over Wi-Fi, found automatically). They are also saved on this iPad.", host, port]
                                   : [NSString stringWithFormat:@"Results go to: %@:%@ (could not reach it yet; will try again at Start). They are saved on this iPad either way.", host, port];
      self->collectorLbl.textColor = ok ? UIColor.whiteColor : C_MUTED;
    });
  });
}

- (void)clearTapped {
  if (running) return;
  agree.on = NO; agree.enabled = YES; resultsLbl.text = @""; clearBtn.hidden = YES;
  [startBtn setTitle:@"Start test" forState:UIControlStateNormal]; startBtn.hidden = NO; [self agreeChanged];
  statusLbl.text = [NSString stringWithFormat:@"Ready. %lu report operations have no row on this platform.", (unsigned long)[catalog[@"operations_without_rows"] count]];
  [self findCollector];
}

- (void)agreeChanged { startBtn.enabled = agree.on && catalog; startBtn.alpha = startBtn.enabled ? 1 : 0.4; }

- (void)startTapped {
  if (!agree.on || !catalog) return;
  NSMutableArray *libs = [NSMutableArray new], *secs = [NSMutableArray new];
  for (NSString *k in libSw) if (libSw[k].on) [libs addObject:k];
  for (NSString *k in secSw) if (secSw[k].on) [secs addObject:k];
  if (!libs.count || !secs.count) { statusLbl.text = @"Pick at least one library and one group of operations."; return; }
  BOOL full = preset.selectedSegmentIndex == 1;
  NSString *docs = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
  NSString *keys = [NSBundle.mainBundle.resourcePath stringByAppendingPathComponent:@"keys"];
  NSMutableDictionary *cfg = [@{
    @"libraries": libs, @"sections": secs, @"rounds": @(full ? 3 : 1), @"samples": @(full ? 10 : 5),
    @"sample_ms": @(full ? 100 : 50), @"warm_ms": @(full ? 300 : 150), @"out_dir": docs, @"label": @"ipad",
    @"env": @{@"RIND_BENCH_KEYS_DIR": keys},
  } mutableCopy];
  NSString *host = [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchHost"];
  NSNumber *port = [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchPort"];
  if (host.length && port) { cfg[@"host"] = host; cfg[@"port"] = port; }
  NSData *js = [NSJSONSerialization dataWithJSONObject:cfg options:0 error:nil];
  NSString *s = [[NSString alloc] initWithData:js encoding:NSUTF8StringEncoding];
  if (devbench_start(s.UTF8String) != 0) { NSDictionary *st = JSON(devbench_status_json()); statusLbl.text = [NSString stringWithFormat:@"Could not start: %@", st[@"start_error"]]; return; }
  UIApplication.sharedApplication.idleTimerDisabled = YES;
  startBtn.hidden = YES; clearBtn.hidden = YES; stopBtn.hidden = NO; stopBtn.enabled = YES; agree.enabled = NO; running = YES;
  [self findCollector];
  [timer invalidate];
  timer = [NSTimer scheduledTimerWithTimeInterval:1.0 repeats:YES block:^(NSTimer *t) { [self poll]; }];
}

- (void)stopTapped { devbench_stop(); stopBtn.enabled = NO; statusLbl.text = @"Stopping after the current row…"; }

- (void)poll {
  NSDictionary *s = JSON(devbench_status_json());
  running = [s[@"running"] boolValue];
  NSString *thermal = @[@"nominal", @"fair", @"serious", @"critical"][MIN(3, (NSInteger)NSProcessInfo.processInfo.thermalState)];
  if (running)
    statusLbl.text = [NSString stringWithFormat:@"Running %@ of %@ · round %@ of %@\n%@\nerrors %@ · sent %@ lines (%@) · thermal %@",
      s[@"done"], s[@"total"], s[@"round"], s[@"rounds"], s[@"current"] ?: @"", s[@"errors"], s[@"lines"], s[@"sink"], thermal];
  else
    statusLbl.text = [NSString stringWithFormat:@"%@ · %@ rows in %.0f s · errors %@ · sent %@ lines (%@) · thermal %@",
      [s[@"stopped"] boolValue] ? @"Stopped" : @"Finished", s[@"done"], [s[@"elapsed_s"] doubleValue], s[@"errors"], s[@"lines"], s[@"sink"], thermal];
  // Per operation: each library's median and rind's time as a share of it.
  NSMutableDictionary<NSString *, NSMutableDictionary *> *byOp = [NSMutableDictionary new];
  NSMutableArray *errs = [NSMutableArray new];
  NSDictionary *res = s[@"results"];
  for (NSString *id_ in res) {
    NSDictionary *r = res[id_];
    if ([r[@"t"] isEqual:@"error"]) { [errs addObject:[NSString stringWithFormat:@"ERROR %@: %@", id_, r[@"error"]]]; continue; }
    NSString *op = r[@"op"] ?: id_;
    if (!byOp[op]) byOp[op] = [NSMutableDictionary new];
    byOp[op][r[@"library"] ?: @"?"] = r[@"ns"];
  }
  NSMutableString *out = [NSMutableString new];
  for (NSString *op in [byOp.allKeys sortedArrayUsingSelector:@selector(compare:)]) {
    NSDictionary *libs = byOp[op]; NSNumber *rind = libs[@"rind"];
    [out appendFormat:@"%@\n", [op stringByReplacingOccurrencesOfString:@"/{lib}" withString:@""]];
    for (NSString *l in [libs.allKeys sortedArrayUsingSelector:@selector(compare:)]) {
      double ns = [libs[l] doubleValue];
      [out appendFormat:@"   %-16s %12s", l.UTF8String, Fmt(ns).UTF8String];
      if (rind && ![l isEqual:@"rind"]) [out appendFormat:@"   rind %.2f× its time", rind.doubleValue / ns];
      [out appendString:@"\n"];
    }
  }
  for (NSString *e in errs) [out appendFormat:@"%@\n", e];
  resultsLbl.text = out;
  if (!running) {
    [timer invalidate]; timer = nil; UIApplication.sharedApplication.idleTimerDisabled = NO;
    startBtn.hidden = NO; [startBtn setTitle:@"Run again" forState:UIControlStateNormal]; stopBtn.hidden = YES; clearBtn.hidden = NO; agree.enabled = YES;
  }
}
@end

@interface AppDelegate : UIResponder <UIApplicationDelegate>
@property (strong) UIWindow *window;
@end
@implementation AppDelegate
- (BOOL)application:(UIApplication *)app didFinishLaunchingWithOptions:(NSDictionary *)o {
  self.window = [[UIWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
  self.window.rootViewController = [VC new];
  [self.window makeKeyAndVisible];
  return YES;
}
@end

int main(int argc, char *argv[]) {
  @autoreleasepool { return UIApplicationMain(argc, argv, nil, NSStringFromClass([AppDelegate class])); }
}
