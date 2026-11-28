# RindBench brand

RindBench is published as **RindBench by kixel.ai** on Android and iOS.
Its identity is Kixel's, shared with Kixel Quest (steelhead99x/quest,
`cloudflare/brand/README.md`).

## Mark

`res/drawable/rindbench_mark.xml` is Kixel's mark, a K of five amber cells on
a graphite tile, with the cell that ends the K's leg drawn as a forward
chevron: a timed run. Kixel Quest uses the same system with Quest's commit
node in that cell. The toolbar shows this mark beside "RindBench" and
"by kixel.ai".

The Details sheet shows Kixel's own mark (`res/drawable-nodpi/kixel_mark.png`,
[kixel.ai's favicon](https://kixel.ai/favicon.svg) rasterized) beside the
publisher name, kixel.ai.

## Launcher and app icons

- Android 8 and later: `res/mipmap-anydpi-v26/ic_launcher.xml`, an adaptive
  icon with a graphite background and the cells as its foreground and
  monochrome layer, sized for the 66 dp safe zone (the cells span 46 dp).
- Older launchers: `res/mipmap-*/ic_launcher.png`, the mark at 48, 72, 96,
  144, and 192 px.
- iOS: `../ios/Resources/AppIcon*.png`, opaque full-bleed squares, since iOS
  rounds the corners.

The PNGs are exported with `rsvg-convert` from the same hand-written SVG.

## Colour

| Role | Night | Day |
| --- | --- | --- |
| Surface | `#07090D` (kixel.ai's graphite) | `#F5F6F8` |
| Controls (primary) | `#FFB020` with `#07090D` text | `#8A5300` with white text |
| Timing display | `#35270E` with `#FFB020` | `#FBEBCB` with `#704400` |
| Selected chips | `#3A2C10` with `#FFDDA0` | `#FFE9C2` with `#4A3000` |

iOS uses the night column (`../ios/main.m`, `C_*`).

## Identifiers

The Android package and the iOS bundle id are both `ai.kixel.rindbench`.
