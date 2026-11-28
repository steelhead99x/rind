// RindBench by kixel.ai, v15 (all libraries): one screen, no scrolling. A data-driven
// picker of every library x operation this build of rind-devbench can time,
// and a live summary of the run.
// The catalog (rows, libraries, sections) comes from the Rust core; nothing
// here names an operation or a library.
#import <UIKit/UIKit.h>
#include <netdb.h>
#include <sys/socket.h>
#include <fcntl.h>
#include <unistd.h>
#include <poll.h>
#include <float.h>

extern char *devbench_catalog_json(void);
extern int devbench_start(const char *config);
extern char *devbench_status_json(void);
extern void devbench_stop(void);
extern void devbench_free(char *p);
extern void devbench_setenv(const char *key, const char *value);
extern void devbench_apply_denies(void);

static id JSON(char *p) {
  if (!p) return nil;
  NSData *d = [NSData dataWithBytes:p length:strlen(p)];
  devbench_free(p);
  return [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
}
static NSString *Fmt(double ns) {
  if (ns >= 1e6) return [NSString stringWithFormat:@"%.2f ms", ns / 1e6];
  if (ns >= 1e3) return [NSString stringWithFormat:@"%.2f µs", ns / 1e3];
  return [NSString stringWithFormat:@"%.0f ns", ns];
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
// Launch arguments, the iOS twin of Android's adb extras, for a device runner:
//   xcrun devicectl device process launch --device UDID ai.kixel.rindbench \
//     -preset quick -libraries rind,ring -sections AEADs -autostart YES [-host H -port P]
// Read from the argument domain only, so nothing carries over to a later launch.
static NSString *Arg(NSString *k) {
  id v = [NSUserDefaults.standardUserDefaults volatileDomainForName:NSArgumentDomain][k];
  if ([v isKindOfClass:NSString.class]) return v;
  return [v respondsToSelector:@selector(stringValue)] ? [v stringValue] : nil;
}
static BOOL ArgOn(NSString *k) {
  NSString *v = Arg(k).lowercaseString;
  return [v isEqual:@"yes"] || [v isEqual:@"true"] || [v isEqual:@"1"];
}
static NSSet<NSString *> *ArgList(NSString *k) {
  NSMutableSet *out = [NSMutableSet new];
  for (NSString *p in [Arg(k) componentsSeparatedByString:@","]) {
    NSString *t = [p stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceCharacterSet];
    if (t.length) [out addObject:t];
  }
  return out;
}

#define RGB(r, g, b) [UIColor colorWithRed:(r) / 255.0 green:(g) / 255.0 blue:(b) / 255.0 alpha:1]
// Kixel's palette: graphite surfaces and Kixel amber (android/BRANDING.md).
#define C_BG RGB(7, 9, 13)
#define C_CARD RGB(13, 17, 24)
#define C_LINE RGB(42, 51, 64)
#define C_CHIP RGB(27, 36, 48)
#define C_MUTED RGB(139, 150, 165)
#define C_TEXT RGB(231, 236, 242)
#define C_ACCENT RGB(255, 176, 32)
#define C_GOOD RGB(84, 214, 146)
#define C_BAD RGB(255, 120, 110)

static NSString *const kConsent = @"The run keeps the CPU busy (minutes on Quick, longer on Full) and warms the device. "
  "It sends only timings and the model, chip, OS version and CPU features to the computer that installed this app. "
  "No name, account, serial or location. Results are also saved on this device.";

// Lays its subviews out left to right, wrapping to a new line when one is full.
@interface Flow : UIView
@property CGFloat gap;
@end
@implementation Flow
- (CGSize)fit:(CGFloat)width place:(BOOL)place {
  CGFloat x = 0, y = 0, line = 0;
  for (UIView *v in self.subviews) {
    CGSize s = [v sizeThatFits:CGSizeMake(width, CGFLOAT_MAX)];
    s.width = MIN(s.width, width);
    if (x > 0 && x + s.width > width) { x = 0; y += line + self.gap; line = 0; }
    if (place) v.frame = CGRectMake(x, y, s.width, s.height);
    x += s.width + self.gap; line = MAX(line, s.height);
  }
  return CGSizeMake(width, self.subviews.count ? y + line : 0);
}
- (void)layoutSubviews {
  [super layoutSubviews];
  CGFloat h = [self fit:self.bounds.size.width place:YES].height;
  // Only when the wrapped height changed, so layout settles.
  if (h != self.bounds.size.height) [self invalidateIntrinsicContentSize];
}
- (CGSize)intrinsicContentSize {
  CGFloat w = self.bounds.size.width;
  return CGSizeMake(UIViewNoIntrinsicMetric, w > 0 ? [self fit:w place:NO].height : 30);
}
@end

@interface VC : UIViewController
@end

@implementation VC {
  UIStackView *body, *leftCol, *pickCard, *runCard, *resultsCard;
  UILabel *picksLbl;
  UIScrollView *pickScroll;
  CGFloat flashedFor;
  BOOL isWide, showingRun;
  Flow *libFlow, *secFlow;
  UILabel *deviceLbl, *collectorLbl, *statusLbl, *currentLbl, *scoreLbl, *behindLbl;
  UIProgressView *progress;
  UISwitch *agree; UISegmentedControl *preset;
  UIButton *startBtn, *stopBtn, *clearBtn;
  BOOL running;
  NSDictionary *catalog;
  NSMutableDictionary<NSString *, UIButton *> *libChips, *secChips;
  NSArray<NSString *> *moreSections;
  UIButton *moreChip;
  NSTimer *timer;
}

#pragma mark - building blocks

- (UILabel *)label:(NSString *)t size:(CGFloat)s weight:(UIFontWeight)w color:(UIColor *)c {
  UILabel *l = [UILabel new]; l.text = t; l.numberOfLines = 0; l.textColor = c ?: C_TEXT;
  l.font = [UIFont systemFontOfSize:s weight:w]; return l;
}
- (UILabel *)heading:(NSString *)t {
  UILabel *l = [self label:t.uppercaseString size:12 weight:UIFontWeightBold color:C_MUTED];
  l.attributedText = [[NSAttributedString alloc] initWithString:t.uppercaseString attributes:@{
    NSKernAttributeName: @1.2, NSFontAttributeName: l.font, NSForegroundColorAttributeName: C_MUTED}];
  return l;
}
- (UIStackView *)card:(NSArray<UIView *> *)views {
  UIStackView *s = [[UIStackView alloc] initWithArrangedSubviews:views];
  s.axis = UILayoutConstraintAxisVertical; s.spacing = 10; s.layoutMarginsRelativeArrangement = YES;
  s.layoutMargins = UIEdgeInsetsMake(14, 16, 14, 16); s.backgroundColor = C_CARD; s.layer.cornerRadius = 16;
  s.layer.borderWidth = 1; s.layer.borderColor = C_LINE.CGColor; s.clipsToBounds = YES; return s;
}
// Buttons are drawn from a UIButtonConfiguration (contentEdgeInsets and the
// titleLabel/tint setters are deprecated or ignored once one is set). The app
// paints every state itself, so automatic state updates are off.
static UIButtonConfiguration *ButtonConfig(NSString *title, UIFont *font, NSDirectionalEdgeInsets insets, CGFloat radius) {
  UIButtonConfiguration *c = [UIButtonConfiguration plainButtonConfiguration];
  c.title = title;
  c.contentInsets = insets;
  c.titleLineBreakMode = NSLineBreakByTruncatingTail;
  c.titleTextAttributesTransformer = ^NSDictionary<NSAttributedStringKey, id> *(NSDictionary<NSAttributedStringKey, id> *in) {
    NSMutableDictionary *out = [in mutableCopy]; out[NSFontAttributeName] = font; return out;
  };
  c.background.cornerRadius = radius;
  c.cornerStyle = UIButtonConfigurationCornerStyleFixed;
  return c;
}
- (UIButton *)chip:(NSString *)title on:(BOOL)on enabled:(BOOL)en {
  BOOL small = [self compact];
  UIButtonConfiguration *c = ButtonConfig(title,
      [UIFont systemFontOfSize:small ? 13 : 14 weight:UIFontWeightSemibold],
      small ? NSDirectionalEdgeInsetsMake(5, 10, 5, 10) : NSDirectionalEdgeInsetsMake(7, 12, 7, 12),
      small ? 13 : 15);
  c.background.strokeWidth = 1;
  UIButton *b = [UIButton buttonWithConfiguration:c primaryAction:nil];
  b.automaticallyUpdatesConfiguration = NO;
  b.selected = on; b.enabled = en;
  [b addTarget:self action:@selector(chipTapped:) forControlEvents:UIControlEventTouchUpInside];
  [self paintChip:b]; return b;
}
- (void)paintChip:(UIButton *)b {
  BOOL on = b.selected;
  UIButtonConfiguration *c = b.configuration;
  c.background.backgroundColor = on ? C_ACCENT : C_CHIP;
  c.background.strokeColor = on ? C_ACCENT : C_LINE;
  c.baseForegroundColor = !b.enabled ? C_MUTED : (on ? UIColor.blackColor : C_TEXT);
  b.configuration = c;
  b.alpha = b.enabled ? 1 : 0.45;
}
- (UIButton *)button:(NSString *)t action:(SEL)a primary:(BOOL)primary {
  UIButtonConfiguration *c = ButtonConfig(t, [UIFont systemFontOfSize:17 weight:UIFontWeightBold],
      NSDirectionalEdgeInsetsMake(11, 22, 11, 22), 12);
  c.background.backgroundColor = primary ? C_ACCENT : C_CHIP;
  c.baseForegroundColor = primary ? UIColor.blackColor : C_TEXT;
  UIButton *b = [UIButton buttonWithConfiguration:c primaryAction:nil];
  b.automaticallyUpdatesConfiguration = NO;
  [b addTarget:self action:a forControlEvents:UIControlEventTouchUpInside]; return b;
}
// A configured button's title lives in its configuration.
static void SetTitle(UIButton *b, NSString *t) {
  UIButtonConfiguration *c = b.configuration; c.title = t; b.configuration = c;
}

#pragma mark - layout

- (void)viewDidLoad {
  [super viewDidLoad];
  self.view.backgroundColor = C_BG;
  libChips = [NSMutableDictionary new]; secChips = [NSMutableDictionary new];

  // Header: name, device, where results go.
  UILabel *title = [self label:@"RindBench" size:28 weight:UIFontWeightHeavy color:nil];
  UILabel *tag = [self label:@"by kixel.ai" size:15 weight:UIFontWeightSemibold color:C_MUTED];
  UIStackView *titleRow = [[UIStackView alloc] initWithArrangedSubviews:@[title, tag, [UIView new]]];
  titleRow.spacing = 10; titleRow.alignment = UIStackViewAlignmentLastBaseline;
  deviceLbl = [self label:@"Reading the list of tests…" size:13 weight:UIFontWeightMedium color:C_MUTED];
  deviceLbl.numberOfLines = 2;
  collectorLbl = [self label:@"Results: looking for the computer that installed this app…" size:13 weight:UIFontWeightRegular color:C_MUTED];
  collectorLbl.numberOfLines = 2;
  UIStackView *header = [[UIStackView alloc] initWithArrangedSubviews:@[titleRow, deviceLbl, collectorLbl]];
  header.axis = UILayoutConstraintAxisVertical; header.spacing = 4;

  // Left column: what to run, and how.
  libFlow = [Flow new]; libFlow.gap = 8;
  secFlow = [Flow new]; secFlow.gap = 8;
  // The chips sit in their own scroller: on a short screen the picker gives
  // up height, and the chips that do not fit stay reachable by scrolling the
  // picker, while the rest of the screen stays put.
  UIStackView *chips = [[UIStackView alloc] initWithArrangedSubviews:@[[self heading:@"Libraries"], libFlow, [self heading:@"Operations"], secFlow]];
  chips.axis = UILayoutConstraintAxisVertical; chips.spacing = 10; [chips setCustomSpacing:16 afterView:libFlow];
  chips.translatesAutoresizingMaskIntoConstraints = NO;
  pickScroll = [UIScrollView new]; pickScroll.alwaysBounceVertical = NO; pickScroll.showsHorizontalScrollIndicator = NO;
  pickScroll.indicatorStyle = UIScrollViewIndicatorStyleWhite;
  [pickScroll addSubview:chips];
  [NSLayoutConstraint activateConstraints:@[
    [chips.topAnchor constraintEqualToAnchor:pickScroll.contentLayoutGuide.topAnchor],
    [chips.bottomAnchor constraintEqualToAnchor:pickScroll.contentLayoutGuide.bottomAnchor],
    [chips.leadingAnchor constraintEqualToAnchor:pickScroll.contentLayoutGuide.leadingAnchor],
    [chips.trailingAnchor constraintEqualToAnchor:pickScroll.contentLayoutGuide.trailingAnchor],
    [chips.widthAnchor constraintEqualToAnchor:pickScroll.frameLayoutGuide.widthAnchor],
  ]];
  // The scroller wants the chips' whole height, and gives it up before the run controls do.
  NSLayoutConstraint *natural = [pickScroll.heightAnchor constraintEqualToAnchor:chips.heightAnchor];
  natural.priority = UILayoutPriorityDefaultHigh - 10; natural.active = YES;
  UIStackView *pick = [self card:@[pickScroll]];
  pickCard = pick;

  preset = [[UISegmentedControl alloc] initWithItems:@[@"Quick · 1 round", @"Full · 3 rounds"]];
  preset.selectedSegmentIndex = 0; preset.selectedSegmentTintColor = C_ACCENT;
  [preset setTitleTextAttributes:@{NSForegroundColorAttributeName: UIColor.blackColor} forState:UIControlStateSelected];
  [preset setTitleTextAttributes:@{NSForegroundColorAttributeName: C_TEXT} forState:UIControlStateNormal];
  agree = [UISwitch new]; agree.onTintColor = C_ACCENT;
  [agree addTarget:self action:@selector(agreeChanged) forControlEvents:UIControlEventValueChanged];
  UILabel *agreeL = [self label:@"I agree: busy CPU for minutes; sends only timings and device model." size:14 weight:UIFontWeightRegular color:nil];
  UIButton *info = [UIButton buttonWithType:UIButtonTypeInfoLight]; info.tintColor = C_ACCENT;
  [info addTarget:self action:@selector(showConsent) forControlEvents:UIControlEventTouchUpInside];
  UIStackView *agreeRow = [[UIStackView alloc] initWithArrangedSubviews:@[agree, agreeL, info]];
  agreeRow.spacing = 10; agreeRow.alignment = UIStackViewAlignmentCenter;
  startBtn = [self button:@"Start test" action:@selector(startTapped) primary:YES]; startBtn.enabled = NO; startBtn.alpha = 0.4;
  stopBtn = [self button:@"Stop" action:@selector(stopTapped) primary:NO]; stopBtn.hidden = YES;
  clearBtn = [self button:@"Clear" action:@selector(clearTapped) primary:NO]; clearBtn.hidden = YES;
  UIStackView *btns = [[UIStackView alloc] initWithArrangedSubviews:@[startBtn, stopBtn, clearBtn]];
  btns.spacing = 10; btns.distribution = UIStackViewDistributionFillEqually;
  UIStackView *run = [self card:@[preset, agreeRow, btns]];
  runCard = run;
  if ([Arg(@"preset") isEqual:@"full"]) preset.selectedSegmentIndex = 1;

  UIView *leftSpring = [UIView new];
  [leftSpring setContentHuggingPriority:UILayoutPriorityDefaultLow - 1 forAxis:UILayoutConstraintAxisVertical];
  leftCol = [[UIStackView alloc] initWithArrangedSubviews:@[pick, run, leftSpring]];
  leftCol.axis = UILayoutConstraintAxisVertical; leftCol.spacing = 12;

  // Right column: the run, summarised to fit. Every row's full timings go to
  // the collector and to this device's files.
  statusLbl = [self label:@"" size:16 weight:UIFontWeightBold color:nil];
  // On a narrow screen the picker folds away during and after a run, and this line stands in for it.
  picksLbl = [self label:@"" size:13 weight:UIFontWeightMedium color:C_ACCENT]; picksLbl.hidden = YES;
  progress = [[UIProgressView alloc] initWithProgressViewStyle:UIProgressViewStyleDefault];
  progress.progressTintColor = C_ACCENT; progress.trackTintColor = C_LINE; progress.progress = 0;
  currentLbl = [self label:@"" size:13 weight:UIFontWeightRegular color:C_MUTED]; currentLbl.numberOfLines = 2;
  scoreLbl = [self label:@"" size:34 weight:UIFontWeightHeavy color:C_GOOD]; scoreLbl.numberOfLines = 1;
  scoreLbl.adjustsFontSizeToFitWidth = YES; scoreLbl.minimumScaleFactor = 0.5;
  behindLbl = [self label:@"" size:13 weight:UIFontWeightRegular color:nil];
  behindLbl.font = [UIFont monospacedSystemFontOfSize:13 weight:UIFontWeightRegular];
  behindLbl.lineBreakMode = NSLineBreakByTruncatingTail;
  [behindLbl setContentCompressionResistancePriority:UILayoutPriorityDefaultLow forAxis:UILayoutConstraintAxisVertical];
  UIView *spring = [UIView new];
  [spring setContentHuggingPriority:UILayoutPriorityDefaultLow forAxis:UILayoutConstraintAxisVertical];
  UILabel *foot = [self label:@"An unofficial community tool, not run or endorsed by the rind maintainers." size:11 weight:UIFontWeightRegular color:C_MUTED];
  UIStackView *results = [self card:@[[self heading:@"Run"], picksLbl, statusLbl, progress, currentLbl, scoreLbl, behindLbl, spring, foot]];
  [results setContentHuggingPriority:UILayoutPriorityDefaultLow forAxis:UILayoutConstraintAxisVertical];
  [results setContentCompressionResistancePriority:UILayoutPriorityDefaultLow forAxis:UILayoutConstraintAxisVertical];
  resultsCard = results;

  body = [[UIStackView alloc] initWithArrangedSubviews:@[leftCol, results]];
  body.spacing = 12;
  [header setContentHuggingPriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisVertical];
  [leftCol setContentHuggingPriority:UILayoutPriorityDefaultHigh forAxis:UILayoutConstraintAxisVertical];
  // When a short screen can't fit everything, the run panel gives way first,
  // then the picker (its chips scroll inside it), and never the run controls.
  [run setContentCompressionResistancePriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisVertical];
  UIStackView *root = [[UIStackView alloc] initWithArrangedSubviews:@[header, body]];
  root.axis = UILayoutConstraintAxisVertical; root.spacing = 14; root.translatesAutoresizingMaskIntoConstraints = NO;
  [self.view addSubview:root];
  UILayoutGuide *g = self.view.safeAreaLayoutGuide;
  [NSLayoutConstraint activateConstraints:@[
    [root.topAnchor constraintEqualToAnchor:g.topAnchor constant:16],
    [root.bottomAnchor constraintEqualToAnchor:g.bottomAnchor constant:-16],
    [root.leadingAnchor constraintEqualToAnchor:g.leadingAnchor constant:20],
    [root.trailingAnchor constraintEqualToAnchor:g.trailingAnchor constant:-20],
  ]];
  [self arrange:self.view.bounds.size];

  [self findCollector];
  // rind-bench's rustls rows read their certificates while the list is made, not only when timed.
  devbench_setenv("RIND_BENCH_KEYS_DIR", [NSBundle.mainBundle.resourcePath stringByAppendingPathComponent:@"keys"].UTF8String);
  dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
    NSDictionary *cat = JSON(devbench_catalog_json());
    dispatch_async(dispatch_get_main_queue(), ^{ [self loaded:cat]; });
  });
}

// Wide screens put the picker and the run side by side; narrow ones stack them.
- (void)arrange:(CGSize)size {
  isWide = size.width > size.height && size.width >= 700;
  [self foldPicker];
  body.axis = isWide ? UILayoutConstraintAxisHorizontal : UILayoutConstraintAxisVertical;
  body.distribution = isWide ? UIStackViewDistributionFillEqually : UIStackViewDistributionFill;
  body.alignment = UIStackViewAlignmentFill;
}
- (void)viewWillTransitionToSize:(CGSize)size withTransitionCoordinator:(id<UIViewControllerTransitionCoordinator>)c {
  [super viewWillTransitionToSize:size withTransitionCoordinator:c];
  [c animateAlongsideTransition:^(id<UIViewControllerTransitionCoordinatorContext> ctx) { [self arrange:size]; } completion:nil];
}

// iOS hides a scroll indicator until the view scrolls, so when chips are out
// of view, flash it once per picker height to show there are more.
- (void)viewDidLayoutSubviews {
  [super viewDidLayoutSubviews];
  CGFloat h = pickScroll.bounds.size.height;
  BOOL more = !pickCard.hidden && h > 0 && pickScroll.contentSize.height > h + 0.5;
  if (more && h != flashedFor) { flashedFor = h; [pickScroll flashScrollIndicators]; }
  if (!more) flashedFor = 0;
}

// Narrow screens have room for the picker or a run's results, not both: the
// picker shows until Start, then folds into one line until Clear.
- (void)foldPicker {
  BOOL fold = showingRun && !isWide;
  pickCard.hidden = fold; picksLbl.hidden = !fold;
}
- (BOOL)compact { return self.view.bounds.size.width < 500; }

#pragma mark - catalog

- (void)loaded:(NSDictionary *)cat {
  catalog = cat;
  if (!cat) { deviceLbl.text = @"Could not read the list of tests."; return; }
  NSDictionary *d = cat[@"device"];
  NSString *sha = [cat[@"rind_commit"] length] > 12 ? [cat[@"rind_commit"] substringToIndex:12] : cat[@"rind_commit"];
  // Only the fields this device reports.
  NSMutableArray *parts = [NSMutableArray new];
  for (NSString *k in @[@"product", @"cpu", @"os"]) {
    id v = d[k];
    if ([v isKindOfClass:NSString.class] && [v length] && ![v isEqual:@"unknown"]) [parts addObject:v];
  }
  if (sha.length) [parts addObject:[@"rind " stringByAppendingString:sha]];
  [parts addObject:[NSString stringWithFormat:@"%lu rows", (unsigned long)[cat[@"rows"] count]]];
  [parts addObject:[cat[@"openssl"] boolValue] ? @"OpenSSL built in" : @"no OpenSSL in this build"];
  deviceLbl.text = [parts componentsJoinedByString:@" · "];
  NSMutableDictionary *lc = [NSMutableDictionary new], *sc = [NSMutableDictionary new];
  for (NSDictionary *r in cat[@"rows"]) { lc[r[@"library"]] = @([lc[r[@"library"]] intValue] + 1); sc[r[@"section"]] = @([sc[r[@"section"]] intValue] + 1); }
  NSSet *wantLibs = ArgList(@"libraries"), *wantSecs = ArgList(@"sections");
  for (NSString *l in cat[@"libraries"]) {
    UIButton *b = [self chip:l on:!wantLibs.count || [wantLibs containsObject:l] enabled:YES]; libChips[l] = b; [libFlow addSubview:b];
  }
  // rind-bench's extra rows ("More: <file>", off by default) share one chip, so the screen never has to scroll.
  NSMutableArray *more = [NSMutableArray new];
  BOOL moreOn = NO;
  for (NSString *s in cat[@"sections"]) {
    int n = [sc[s] intValue];
    if ([s hasPrefix:@"More: "]) { if (n > 0) { [more addObject:s]; moreOn |= [wantSecs containsObject:s]; } continue; }
    UIButton *b = [self chip:s on:n > 0 && (!wantSecs.count || [wantSecs containsObject:s]) enabled:n > 0]; secChips[s] = b; [secFlow addSubview:b];
  }
  moreSections = more;
  if (more.count) {
    moreChip = [self chip:[NSString stringWithFormat:@"+ %lu more groups", (unsigned long)more.count] on:moreOn enabled:YES];
    [secFlow addSubview:moreChip];
  }
  [libFlow invalidateIntrinsicContentSize]; [secFlow invalidateIntrinsicContentSize];
  [self ready];
  [self reportLayout:@"ready"];
  // -autostart waits a moment, so a runner can capture the picker before the run.
  if (ArgOn(@"autostart"))
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(3 * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
      self->agree.on = YES; [self agreeChanged]; [self startTapped];
    });
}

// One machine-readable line saying whether the screen fits, for a device
// runner checking "no scrolling" without a person looking:
//   RINDBENCH_LAYOUT {"phase":"ready","w":390,"h":844,"wide":false,"folded":false,"fits":true,"clipped":[]}
// fits: the run controls are whole and on screen, and the run panel shows its
// status (and score, once there is one). "picker" in clipped means some chips
// are out of view and scroll inside the picker, which a short screen allows.
- (void)reportLayout:(NSString *)phase {
  dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(0.6 * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
    [self.view layoutIfNeeded];
    UIView *root = self.view;
    CGFloat bottom = CGRectGetMaxY(root.safeAreaLayoutGuide.layoutFrame) + 1;
    CGFloat (^maxY)(UIView *) = ^CGFloat(UIView *v) { return CGRectGetMaxY([v convertRect:v.bounds toView:root]); };
    BOOL (^whole)(UIView *) = ^BOOL(UIView *v) {
      CGFloat need = [v systemLayoutSizeFittingSize:CGSizeMake(v.bounds.size.width, 0)
                      withHorizontalFittingPriority:UILayoutPriorityRequired
                            verticalFittingPriority:UILayoutPriorityFittingSizeLevel].height;
      return need <= v.bounds.size.height + 1;
    };
    BOOL (^shown)(UIView *) = ^BOOL(UIView *v) {
      CGFloat need = [v sizeThatFits:CGSizeMake(v.bounds.size.width, CGFLOAT_MAX)].height;
      return !v.hidden && v.bounds.size.height + 1 >= need && maxY(v) <= maxY(self->resultsCard) + 1 && maxY(v) <= bottom;
    };
    NSMutableArray *clipped = [NSMutableArray new];
    if (!whole(self->runCard) || maxY(self->runCard) > bottom) [clipped addObject:@"run controls"];
    UIScrollView *ps = self->pickScroll;
    if (!self->pickCard.hidden && (!whole(self->pickCard) || ps.contentSize.height > ps.bounds.size.height + 1)) [clipped addObject:@"picker"];
    if (self->statusLbl.text.length && !shown(self->statusLbl)) [clipped addObject:@"status"];
    if (self->scoreLbl.text.length && !shown(self->scoreLbl)) [clipped addObject:@"score"];
    BOOL fits = YES;
    for (NSString *c in clipped) if (![c isEqual:@"picker"]) fits = NO;
    NSDictionary *o = @{@"phase": phase, @"w": @((int)root.bounds.size.width), @"h": @((int)root.bounds.size.height),
                        @"wide": @(self->isWide), @"folded": @(self->pickCard.hidden), @"fits": @(fits), @"clipped": clipped};
    NSData *js = [NSJSONSerialization dataWithJSONObject:o options:NSJSONWritingSortedKeys error:nil];
    NSString *line = [@"RINDBENCH_LAYOUT " stringByAppendingString:[[NSString alloc] initWithData:js encoding:NSUTF8StringEncoding]];
    // stderr reaches `devicectl … --console`; NSLog reaches the device log.
    fprintf(stderr, "%s\n", line.UTF8String); fflush(stderr);
    NSLog(@"%@", line);
  });
}

- (void)ready {
  statusLbl.text = @"Ready";
  progress.progress = 0;
  currentLbl.text = [NSString stringWithFormat:@"%lu report operations have no row on this platform.", (unsigned long)[catalog[@"operations_without_rows"] count]];
  scoreLbl.text = @""; behindLbl.text = @"";
}

- (void)chipTapped:(UIButton *)b {
  if (running) return;
  b.selected = !b.selected; [self paintChip:b];
}

- (void)showConsent {
  UIAlertController *a = [UIAlertController alertControllerWithTitle:@"Before you start" message:kConsent preferredStyle:UIAlertControllerStyleAlert];
  [a addAction:[UIAlertAction actionWithTitle:@"OK" style:UIAlertActionStyleDefault handler:nil]];
  [self presentViewController:a animated:YES completion:nil];
}

// The collector fills itself in from the address baked in at build time (BenchHost/BenchPort),
// or from -host/-port at launch; shown, never typed.
- (NSString *)colHost { NSString *h = Arg(@"host"); return h.length ? h : [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchHost"]; }
- (NSNumber *)colPort {
  if (Arg(@"port").intValue > 0) return @(Arg(@"port").intValue);
  id p = [NSBundle.mainBundle objectForInfoDictionaryKey:@"BenchPort"];
  return [p respondsToSelector:@selector(intValue)] && [p intValue] > 0 ? @([p intValue]) : nil;
}
- (void)findCollector {
  NSString *host = [self colHost];
  NSNumber *port = [self colPort];
  if (!host.length || !port) { collectorLbl.text = @"Results: saved on this device (no collector in this build)"; return; }
  dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
    BOOL ok = Reachable(host, port.intValue, 800);
    dispatch_async(dispatch_get_main_queue(), ^{
      self->collectorLbl.text = ok ? [NSString stringWithFormat:@"● Results: %@:%@ over the network, and saved on this device", host, port]
                                   : [NSString stringWithFormat:@"○ Results: %@:%@ not reachable yet (tries again at Start); saved on this device", host, port];
      self->collectorLbl.textColor = ok ? C_GOOD : C_MUTED;
    });
  });
}

#pragma mark - run

- (void)agreeChanged { startBtn.enabled = agree.on && catalog; startBtn.alpha = startBtn.enabled ? 1 : 0.4; }

- (void)setPicking:(BOOL)en {
  for (UIButton *b in libFlow.subviews) b.userInteractionEnabled = en;
  for (UIButton *b in secFlow.subviews) b.userInteractionEnabled = en;
  preset.enabled = en; agree.enabled = en;
}

- (void)clearTapped {
  if (running) return;
  agree.on = NO; clearBtn.hidden = YES;
  SetTitle(startBtn, @"Start test"); startBtn.hidden = NO;
  showingRun = NO; [self foldPicker];
  [self setPicking:YES]; [self agreeChanged]; [self ready]; [self findCollector];
}

- (void)startTapped {
  if (!agree.on || !catalog) return;
  NSMutableArray *libs = [NSMutableArray new], *secs = [NSMutableArray new];
  for (NSString *k in libChips) if (libChips[k].selected) [libs addObject:k];
  for (NSString *k in secChips) if (secChips[k].selected) [secs addObject:k];
  if (moreChip.selected) [secs addObjectsFromArray:moreSections];
  if (!libs.count || !secs.count) { statusLbl.text = @"Pick at least one library and one operation"; return; }
  BOOL full = preset.selectedSegmentIndex == 1;
  NSString *docs = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
  NSString *keys = [NSBundle.mainBundle.resourcePath stringByAppendingPathComponent:@"keys"];
  NSMutableDictionary *cfg = [@{
    @"libraries": libs, @"sections": secs, @"rounds": @(full ? 3 : 1), @"samples": @(full ? 10 : 5),
    @"sample_ms": @(full ? 100 : 50), @"warm_ms": @(full ? 300 : 150), @"out_dir": docs, @"label": @"ipad",
    @"env": @{@"RIND_BENCH_KEYS_DIR": keys},
  } mutableCopy];
  NSString *host = [self colHost];
  NSNumber *port = [self colPort];
  if (host.length && port) { cfg[@"host"] = host; cfg[@"port"] = port; }
  NSData *js = [NSJSONSerialization dataWithJSONObject:cfg options:0 error:nil];
  NSString *s = [[NSString alloc] initWithData:js encoding:NSUTF8StringEncoding];
  if (devbench_start(s.UTF8String) != 0) { NSDictionary *st = JSON(devbench_status_json()); statusLbl.text = [NSString stringWithFormat:@"Could not start: %@", st[@"start_error"]]; return; }
  UIApplication.sharedApplication.idleTimerDisabled = YES;
  startBtn.hidden = YES; clearBtn.hidden = YES; stopBtn.hidden = NO; stopBtn.enabled = YES; running = YES;
  [self setPicking:NO];
  picksLbl.text = [NSString stringWithFormat:@"%@ · %lu libraries · %lu groups", full ? @"Full" : @"Quick", (unsigned long)libs.count, (unsigned long)secs.count];
  showingRun = YES; [self foldPicker];
  statusLbl.text = @"Starting…"; scoreLbl.text = @""; behindLbl.text = @"";
  [self findCollector];
  [timer invalidate];
  timer = [NSTimer scheduledTimerWithTimeInterval:1.0 repeats:YES block:^(NSTimer *t) { [self poll]; }];
  [self reportLayout:@"run"];
}

- (void)stopTapped { devbench_stop(); stopBtn.enabled = NO; statusLbl.text = @"Stopping after the current row…"; }

- (void)poll {
  NSDictionary *s = JSON(devbench_status_json());
  running = [s[@"running"] boolValue];
  NSString *thermal = @[@"nominal", @"fair", @"serious", @"critical"][MIN(3, (NSInteger)NSProcessInfo.processInfo.thermalState)];
  double done = [s[@"done"] doubleValue], total = MAX(1, [s[@"total"] doubleValue]);
  progress.progress = done / total;
  if (running) {
    statusLbl.text = [NSString stringWithFormat:@"Running %@ of %@ · round %@ of %@", s[@"done"], s[@"total"], s[@"round"], s[@"rounds"]];
    currentLbl.text = [NSString stringWithFormat:@"%@\nerrors %@ · sent %@ lines (%@) · thermal %@", s[@"current"] ?: @"", s[@"errors"], s[@"lines"], s[@"sink"], thermal];
  } else {
    statusLbl.text = [NSString stringWithFormat:@"%@ · %@ rows in %.0f s", [s[@"stopped"] boolValue] ? @"Stopped" : @"Finished", s[@"done"], [s[@"elapsed_s"] doubleValue]];
    currentLbl.text = [NSString stringWithFormat:@"errors %@ · sent %@ lines (%@) · thermal %@ · full timings saved on this device", s[@"errors"], s[@"lines"], s[@"sink"], thermal];
  }
  [self summarize:s[@"results"]];
  if (!running) {
    [timer invalidate]; timer = nil; UIApplication.sharedApplication.idleTimerDisabled = NO;
    startBtn.hidden = NO; SetTitle(startBtn, @"Run again"); stopBtn.hidden = YES; clearBtn.hidden = NO;
    [self setPicking:YES];
    [self reportLayout:@"done"];
  }
}

// Per operation, the fastest library. The score counts the operations rind
// is fastest at; the list shows where it is not, worst first, as many as fit.
- (void)summarize:(NSDictionary *)res {
  NSMutableDictionary<NSString *, NSMutableDictionary *> *byOp = [NSMutableDictionary new];
  int errors = 0;
  for (NSString *id_ in res) {
    NSDictionary *r = res[id_];
    if ([r[@"t"] isEqual:@"error"]) { errors++; continue; }
    NSString *op = r[@"op"] ?: id_;
    if (!byOp[op]) byOp[op] = [NSMutableDictionary new];
    byOp[op][r[@"library"] ?: @"?"] = r[@"ns"];
  }
  int compared = 0, wins = 0;
  NSMutableArray *behind = [NSMutableArray new];
  for (NSString *op in byOp) {
    NSDictionary *libs = byOp[op]; NSNumber *rind = libs[@"rind"];
    if (!rind || libs.count < 2) continue;
    compared++;
    NSString *best = nil; double bestNs = DBL_MAX;
    for (NSString *l in libs) if ([libs[l] doubleValue] < bestNs) { bestNs = [libs[l] doubleValue]; best = l; }
    if ([best isEqual:@"rind"]) wins++;
    else [behind addObject:@{@"op": [op stringByReplacingOccurrencesOfString:@"/{lib}" withString:@""], @"lib": best,
                              @"ratio": @(rind.doubleValue / bestNs), @"ns": rind}];
  }
  if (!compared) { scoreLbl.text = @""; behindLbl.text = errors ? [NSString stringWithFormat:@"%d rows failed so far", errors] : @""; return; }
  scoreLbl.text = [NSString stringWithFormat:@"rind fastest on %d of %d", wins, compared];
  scoreLbl.textColor = wins * 2 >= compared ? C_GOOD : C_ACCENT;
  [behind sortUsingComparator:^NSComparisonResult(NSDictionary *a, NSDictionary *b) { return [b[@"ratio"] compare:a[@"ratio"]]; }];
  NSMutableAttributedString *out = [NSMutableAttributedString new];
  UIFont *mono = [UIFont monospacedSystemFontOfSize:13 weight:UIFontWeightRegular];
  if (behind.count)
    [out appendAttributedString:[[NSAttributedString alloc] initWithString:@"Where another library is faster\n"
      attributes:@{NSFontAttributeName: [UIFont systemFontOfSize:13 weight:UIFontWeightBold], NSForegroundColorAttributeName: C_MUTED}]];
  for (NSDictionary *b in behind) {
    NSString *line = [NSString stringWithFormat:@"%.2f×  %@  (vs %@, rind %@)\n", [b[@"ratio"] doubleValue], b[@"op"], b[@"lib"], Fmt([b[@"ns"] doubleValue])];
    [out appendAttributedString:[[NSAttributedString alloc] initWithString:line
      attributes:@{NSFontAttributeName: mono, NSForegroundColorAttributeName: [b[@"ratio"] doubleValue] > 1.10 ? C_BAD : C_TEXT}]];
  }
  if (errors)
    [out appendAttributedString:[[NSAttributedString alloc] initWithString:[NSString stringWithFormat:@"%d rows failed; see the saved results\n", errors]
      attributes:@{NSFontAttributeName: mono, NSForegroundColorAttributeName: C_BAD}]];
  behindLbl.attributedText = out;
}
@end

@interface AppDelegate : UIResponder <UIApplicationDelegate>
@property (nonatomic, strong) UIWindow *window;
@end
@implementation AppDelegate
- (BOOL)application:(UIApplication *)app didFinishLaunchingWithOptions:(NSDictionary *)o {
  self.window = [[UIWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
  self.window.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
  self.window.rootViewController = [VC new];
  [self.window makeKeyAndVisible];
  return YES;
}
@end

int main(int argc, char *argv[]) {
  // Before UIApplicationMain starts any thread: setenv is not thread safe.
  devbench_apply_denies();
  @autoreleasepool { return UIApplicationMain(argc, argv, nil, NSStringFromClass([AppDelegate class])); }
}
