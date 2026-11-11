#!/usr/bin/env python3
"""Draws the LiveArea art and the in-app logo for Vita Storage Manager.

Outputs (the Vita wants 8-bit palette PNGs for the LiveArea files):
  sce_sys/icon0.png                         128x128
  sce_sys/livearea/contents/bg.png          840x500
  sce_sys/livearea/contents/startup.png     280x158
  assets/logo.png                           256x256 RGBA (scan-screen spinner)

Look: a modern-console home screen. Deep blue-to-black gradients, flowing
light ribbons, soft particles, a glossy white/blue segmented storage ring and
gradient lettering with glow. Original artwork: no platform logos or symbols.
"""
import math, os, random
from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageChops

HERE = os.path.dirname(os.path.abspath(__file__))
SCE = os.path.join(HERE, '..', 'sce_sys')
ASSETS = os.path.join(HERE, '..', 'assets')

DEEP, MID, GLOW = (1, 6, 22), (0, 38, 112), (40, 120, 255)
ICE = (196, 222, 255)
# Ring segments: white through ice and electric blue (sizes = share of the ring)
SEG = [((255, 255, 255), 0.30), ((178, 212, 255), 0.18), ((88, 156, 255), 0.15),
       ((44, 110, 240), 0.11), ((120, 200, 255), 0.07)]
TRACK = (34, 48, 84)

F_LIGHT = ('C:/Windows/Fonts/segoeuil.ttf', 'C:/Windows/Fonts/segoeui.ttf')
F_SEMI = ('C:/Windows/Fonts/seguisb.ttf', 'C:/Windows/Fonts/segoeuib.ttf')
F_BOLD = ('C:/Windows/Fonts/segoeuib.ttf', 'C:/Windows/Fonts/arialbd.ttf')


def font(kind, size):
    for f in kind:
        if os.path.exists(f):
            return ImageFont.truetype(f, size)
    return ImageFont.load_default()


# ------------------------------------------------------------- backdrop

def backdrop(w, h, cx=0.32, cy=0.45, seed=3):
    """Radial blue bloom fading to near-black, light ribbons, particles."""
    random.seed(seed)
    im = Image.new('RGB', (w, h))
    px = im.load()
    R = math.hypot(w, h) * 0.62
    for y in range(h):
        for x in range(w):
            d = min(1.0, math.hypot(x - w * cx, (y - h * cy) * 1.25) / R)
            t = d ** 1.15
            px[x, y] = tuple(int(m + (dp - m) * t) for m, dp in zip(MID, DEEP))
    im = Image.alpha_composite(im.convert('RGBA'), ribbons(w, h))
    im = Image.alpha_composite(im, particles(w, h))
    return im


def ribbons(w, h):
    """Flowing translucent light bands, like a console home screen."""
    lay = Image.new('RGBA', (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(lay)
    bands = [(0.62, 0.10, 1.3, 0.0, 70), (0.70, 0.08, 1.1, 1.7, 55), (0.78, 0.06, 1.6, 3.1, 40)]
    for base, amp, freq, phase, alpha in bands:
        for k in range(14):
            off = k * h * 0.006
            pts = []
            for i in range(0, w + 8, 8):
                u = i / w
                y = h * (base + amp * math.sin(u * math.pi * freq + phase)) + off - u * h * 0.25
                pts.append((i, y))
            a = int(alpha * (1 - k / 14) ** 1.6)
            d.line(pts, fill=(150, 200, 255, a), width=max(1, w // 420))
    soft = lay.filter(ImageFilter.GaussianBlur(max(1, w // 300)))
    glow = lay.filter(ImageFilter.GaussianBlur(max(2, w // 60)))
    return Image.alpha_composite(glow, soft)


def particles(w, h, n=None):
    lay = Image.new('RGBA', (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(lay)
    n = n or int(w * h / 9000)
    for _ in range(n):
        x, y = random.random() * w, random.random() * h
        r = random.choice([1, 1, 1, 2, 2, 3]) * max(1, w // 840)
        a = random.randint(30, 140)
        d.ellipse([x - r, y - r, x + r, y + r], fill=(210, 230, 255, a))
    bokeh = Image.new('RGBA', (w, h), (0, 0, 0, 0))
    bd = ImageDraw.Draw(bokeh)
    for _ in range(max(4, n // 25)):
        x, y = random.random() * w, random.random() * h
        r = random.uniform(0.01, 0.035) * w
        bd.ellipse([x - r, y - r, x + r, y + r], fill=(120, 180, 255, random.randint(18, 40)))
    bokeh = bokeh.filter(ImageFilter.GaussianBlur(w // 160 + 1))
    return Image.alpha_composite(bokeh, lay.filter(ImageFilter.GaussianBlur(0.6)))


# ----------------------------------------------------------------- ring

def ring_layer(size, cx, cy, r, width, gap_deg=6, start=-90):
    lay = Image.new('RGBA', size, (0, 0, 0, 0))
    d = ImageDraw.Draw(lay)

    def arc(a0, a1, col):
        if a1 < a0:
            a0 = a1 = (a0 + a1) / 2
        else:
            d.arc([cx - r, cy - r, cx + r, cy + r], a0, a1, fill=col, width=width)
        rc = r - width / 2
        for a in (a0, a1):
            ax, ay = cx + rc * math.cos(math.radians(a)), cy + rc * math.sin(math.radians(a))
            d.ellipse([ax - width / 2, ay - width / 2, ax + width / 2, ay + width / 2], fill=col)

    cap = math.degrees(width / 2 / max(1, r - width / 2))
    a = start
    for col, share in SEG:
        sweep = share * 360
        arc(a + gap_deg / 2 + cap, a + sweep - gap_deg / 2 - cap, col + (255,))
        a += sweep
    arc(a + gap_deg / 2 + cap, start + 360 - gap_deg / 2 - cap, TRACK + (255,))
    return lay


def gloss(lay, cx, cy, r):
    """Top-left specular highlight clipped to the ring's shape."""
    hl = Image.new('RGBA', lay.size, (0, 0, 0, 0))
    hd = ImageDraw.Draw(hl)
    hd.ellipse([cx - r * 1.1, cy - r * 1.25, cx + r * 0.6, cy + r * 0.05], fill=(255, 255, 255, 90))
    hl = hl.filter(ImageFilter.GaussianBlur(r * 0.12))
    alpha = lay.split()[3]
    hl.putalpha(ImageChops.multiply(hl.split()[3], alpha))
    return Image.alpha_composite(lay, hl)


def put_ring(im, cx, cy, r, width, glow=None):
    lay = gloss(ring_layer(im.size, cx, cy, r, width), cx, cy, r)
    g = lay.filter(ImageFilter.GaussianBlur(glow or width * 0.45))
    tint = Image.new('RGBA', im.size, GLOW + (0,))
    tint.putalpha(g.split()[3])
    out = Image.alpha_composite(im, tint)
    out = Image.alpha_composite(out, tint)
    return Image.alpha_composite(out, lay)


# ---------------------------------------------------------------- text

def text_mask(size, xy, txt, f, tracking=0.0):
    m = Image.new('L', size, 0)
    d = ImageDraw.Draw(m)
    x, y = xy
    for ch in txt:
        d.text((x, y), ch, font=f, fill=255)
        x += d.textlength(ch, font=f) + f.size * tracking
    return m, x


def styled_text(im, xy, txt, f, tracking=0.02, top=(255, 255, 255), bottom=ICE,
                glow=True, shadow=True, reflect=False):
    """Vertical gradient fill + outer glow + soft shadow (+ optional reflection)."""
    m, x_end = text_mask(im.size, xy, txt, f, tracking)
    bbox = m.getbbox()
    if not bbox:
        return x_end
    y0, y1 = bbox[1], bbox[3]
    grad = Image.new('RGBA', im.size)
    gd = ImageDraw.Draw(grad)
    for y in range(y0, y1 + 1):
        t = (y - y0) / max(1, y1 - y0)
        gd.line([(0, y), (im.width, y)], fill=tuple(int(a + (b - a) * t) for a, b in zip(top, bottom)) + (255,))
    out = im
    if shadow:
        sh = Image.new('RGBA', im.size, (0, 4, 20, 0))
        sh.putalpha(m.filter(ImageFilter.GaussianBlur(f.size * 0.06)).point(lambda v: v * 0.8))
        out = Image.alpha_composite(out, ImageChops.offset(sh, 0, int(f.size * 0.05)))
    if glow:
        gl = Image.new('RGBA', im.size, GLOW + (0,))
        gl.putalpha(m.filter(ImageFilter.GaussianBlur(f.size * 0.18)).point(lambda v: int(v * 0.75)))
        out = Image.alpha_composite(out, gl)
    if reflect:
        h = y1 - y0
        ref = grad.copy()
        ref.putalpha(m)
        ref = ref.crop((0, y0, im.width, y1)).transpose(Image.FLIP_TOP_BOTTOM)
        fade = Image.new('L', ref.size)
        fd = ImageDraw.Draw(fade)
        for y in range(ref.height):
            fd.line([(0, y), (ref.width, y)], fill=int(70 * (1 - y / ref.height) ** 2))
        ref.putalpha(ImageChops.multiply(ref.split()[3], fade))
        layer = Image.new('RGBA', im.size, (0, 0, 0, 0))
        layer.paste(ref, (0, y1 + int(h * 0.08)))
        out = Image.alpha_composite(out, layer)
    grad.putalpha(m)
    return Image.alpha_composite(out, grad), x_end


def streak(im, x0, x1, y, thick):
    """A thin light streak that fades at both ends."""
    lay = Image.new('RGBA', im.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(lay)
    for x in range(int(x0), int(x1)):
        t = (x - x0) / (x1 - x0)
        a = int(230 * math.sin(math.pi * t) ** 1.5)
        d.line([(x, y), (x, y + thick)], fill=(200, 225, 255, a))
    g = lay.filter(ImageFilter.GaussianBlur(thick * 3))
    return Image.alpha_composite(Image.alpha_composite(im, g), lay)


# ---------------------------------------------------------------- saves

def save_palette(im, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    rgb = im.convert('RGB')
    pal = rgb.quantize(256, method=Image.MEDIANCUT, kmeans=4)
    rgb.quantize(palette=pal, dither=Image.FLOYDSTEINBERG).save(path, optimize=True)


def make_icon():
    S = 512
    im = backdrop(S, S, cx=0.5, cy=0.42, seed=7)
    im = put_ring(im, S / 2, S / 2, 178, 54, glow=28)
    d = ImageDraw.Draw(im)
    c = (S / 2, S / 2)
    d.ellipse([c[0] - 70, c[1] - 70, c[0] + 70, c[1] + 70], fill=(4, 12, 34, 255))
    # center: a small white "fill level" dot with glow
    dot = Image.new('RGBA', im.size, (0, 0, 0, 0))
    ImageDraw.Draw(dot).ellipse([c[0] - 22, c[1] - 22, c[0] + 22, c[1] + 22], fill=(255, 255, 255, 255))
    gl = Image.new('RGBA', im.size, GLOW + (0,))
    gl.putalpha(dot.split()[3].filter(ImageFilter.GaussianBlur(16)))
    im = Image.alpha_composite(Image.alpha_composite(im, gl), dot)
    save_palette(im.resize((128, 128), Image.LANCZOS), os.path.join(SCE, 'icon0.png'))


def make_bg():
    W, H = 840 * 2, 500 * 2
    im = backdrop(W, H, cx=0.30, cy=0.40, seed=11)
    im = put_ring(im, 1290, 470, 300, 70, glow=40)
    im, _ = styled_text(im, (150, 250), 'VITA', font(F_LIGHT, 60), tracking=0.55, glow=False)
    im, x_end = styled_text(im, (140, 310), 'Storage', font(F_SEMI, 150), tracking=0.01)
    im, _ = styled_text(im, (146, 470), 'MANAGER', font(F_LIGHT, 88), tracking=0.42, top=(225, 238, 255), bottom=(130, 180, 255), reflect=True)
    im = streak(im, 150, 820, 600, 3)
    d = ImageDraw.Draw(im)
    d.text((152, 640), 'See what fills your memory card', font=font(F_LIGHT, 40), fill=(170, 192, 230))
    save_palette(im.resize((840, 500), Image.LANCZOS), os.path.join(SCE, 'livearea', 'contents', 'bg.png'))


def make_startup():
    W, H = 280 * 4, 158 * 4
    im = backdrop(W, H, cx=0.22, cy=0.5, seed=5)
    im = put_ring(im, 200, H / 2, 140, 38, glow=22)
    d = ImageDraw.Draw(im)
    d.ellipse([200 - 26, H / 2 - 26, 200 + 26, H / 2 + 26], fill=(255, 255, 255))
    im, _ = styled_text(im, (402, 150), 'VITA', font(F_LIGHT, 52), tracking=0.6, glow=False)
    im, _ = styled_text(im, (392, 196), 'Storage', font(F_SEMI, 150), tracking=0.01)
    im, _ = styled_text(im, (400, 372), 'MANAGER', font(F_LIGHT, 86), tracking=0.42, top=(225, 238, 255), bottom=(130, 180, 255))
    im = streak(im, 400, 1080, 496, 4)
    save_palette(im.resize((280, 158), Image.LANCZOS), os.path.join(SCE, 'livearea', 'contents', 'startup.png'))


def make_logo():
    S = 512
    base = Image.new('RGBA', (S, S), (0, 0, 0, 0))
    lay = gloss(ring_layer((S, S), S / 2, S / 2, 200, 52), S / 2, S / 2, 200)
    g = Image.new('RGBA', (S, S), GLOW + (0,))
    g.putalpha(lay.split()[3].filter(ImageFilter.GaussianBlur(16)))
    out = Image.alpha_composite(Image.alpha_composite(base, g), lay)
    os.makedirs(ASSETS, exist_ok=True)
    out.resize((256, 256), Image.LANCZOS).save(os.path.join(ASSETS, 'logo.png'), optimize=True)


def main():
    make_icon()
    make_bg()
    make_startup()
    make_logo()
    with open(os.path.join(SCE, 'livearea', 'contents', 'template.xml'), 'w', newline='\n') as f:
        f.write('<?xml version="1.0" encoding="utf-8"?>\n\n'
                '<livearea style="a1" format-ver="01.00" content-rev="3">\n'
                '  <livearea-background>\n    <image>bg.png</image>\n  </livearea-background>\n\n'
                '  <gate>\n    <startup-image>startup.png</startup-image>\n  </gate>\n</livearea>\n')


if __name__ == '__main__':
    main()
