/* Storage: a storage overview for the PS Vita memory card (ux0:).
 *
 * Scans ux0: and sorts what it finds into PS Vita games, homebrew, PSP games,
 * PS1 games, saved data, media, extra (leftover) files and "system & other".
 * Every entry gets its real title from the game's own PARAM.SFO (Vita apps,
 * PSP ISO/CSO images, PBP eboots), an icon, its size, and a "last played"
 * date taken from the newest save or app-data file.
 *
 * Apps can be uninstalled in one step (system uninstaller + update, DLC, data
 * folders and optionally saves). PSP/PS1 games are linked to the Adrenaline
 * bubbles that launch them (data/boot.bin, "ABB" + path at 0x40) so deleting a
 * game can remove its bubble too.
 *
 * Built with vita2d and the Vita's system font. Needs unsafe homebrew mode to
 * read other apps' folders.
 */
#include <psp2/kernel/processmgr.h>
#include <psp2/kernel/threadmgr.h>
#include <psp2/io/fcntl.h>
#include <psp2/io/dirent.h>
#include <psp2/io/stat.h>
#include <psp2/io/devctl.h>
#include <psp2/ctrl.h>
#include <psp2/rtc.h>
#include <psp2/power.h>
#include <psp2/promoterutil.h>
#include <psp2/sysmodule.h>
#include <psp2/apputil.h>
#include <psp2/system_param.h>
#include <vita2d.h>
#include <zlib.h>
#include <png.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <ctype.h>
#include <math.h>

#define SCREEN_W 960
#define SCREEN_H 544
#define MAX_ITEMS 2000
#define MAX_BUBBLES 400
#define MAX_BUB_PER_GAME 6

/* ------------------------------------------------------------------ model */

enum { CAT_VITA, CAT_HB, CAT_PSP, CAT_PS1, CAT_SAVE, CAT_MEDIA, CAT_EXTRA, CAT_OTHER, NCAT };

static const char *cat_name[NCAT] = {
    "PS Vita Games", "Homebrew", "PSP Games", "PS1 Games",
    "Saved Data", "Media", "Extra Files", "System & Other"
};
static const char *cat_desc[NCAT] = {
    "Installed Vita titles, including updates and DLC",
    "Homebrew apps and ports, including their data folders",
    "PSP ISO/CSO images and PSP titles, with their bubbles",
    "PlayStation classics installed as EBOOTs, with their bubbles",
    "Game saves for Vita, PSP and PS1 titles",
    "Videos, music and pictures",
    "Leftovers that are usually safe to clean up",
    "Plugins, system files and everything else"
};
static const unsigned int cat_rgb[NCAT] = {
    0x3B82F6, 0x14B8A6, 0xA855F7, 0xF59E0B,
    0x22C55E, 0xEC4899, 0xF97316, 0x64748B
};

enum { P_APP, P_UPD, P_DLC, P_DATA, P_SAVE, P_BUB, NPART };
enum { ICON_NONE, ICON_FILE, ICON_ISO, ICON_CSO, ICON_PBP };
enum { DEL_NONE, DEL_PATH, DEL_PREFIX, DEL_APP };

typedef struct {
    char name[128];
    char id[24];          /* title ID / disc ID / bubble ID */
    char path[320];       /* main location */
    char data_paths[4][128];  /* matched ux0:data folders (homebrew) */
    uint64_t data_sizes[4];
    unsigned char data_sure[4]; /* 1 = confident match, 0 = guessed or shared */
    int ndata;
    char bub_ids[MAX_BUB_PER_GAME][16]; /* Adrenaline bubbles that launch this PSP/PS1 game */
    uint64_t bub_sizes[MAX_BUB_PER_GAME];
    int nbub;
    int installed;        /* lives in ux0:app and can be uninstalled */
    int protect;          /* core tool: never uninstalled from here */
    char note[112];
    char icon_src[320];
    int cat;
    int icon_kind;
    int del_kind;         /* DEL_PREFIX: delete every dir in path whose name starts with id */
    uint64_t size;        /* what counts toward the category */
    uint64_t part[NPART];
    int last_day;         /* days since 1970, 0 = unknown */
    uint64_t key;         /* timestamps of the app folder, eboot and param.sfo (skip unchanged apps) */
    vita2d_texture *icon;
    int icon_state;       /* 0 not tried, 1 loaded, 2 failed */
} Item;

typedef struct {
    char id[16];
    char title[128];
    char target[256];     /* lowercase launch path from data/boot.bin */
    uint64_t size;
    int linked;
} Bubble;

/* Two models: UM is what the UI shows (loaded from the cache at start-up),
 * SM is what the scanner is building. When a scan finishes they are swapped.
 * Code in the scanning section sees SM through these names; UI code below the
 * drawing section sees UM (the macros are redefined there). */
typedef struct { Item *it; int n; Bubble *bub; int nb; } Model;
static Model UM, SM;
#define items (SM.it)
#define nitems (SM.n)
#define bubbles (SM.bub)
#define nbubbles (SM.nb)
static volatile int scanning;
static int cache_day, cache_hour, cache_min, have_cache;
static uint64_t cache_free;          /* free bytes when the cache was written */
static uint32_t um_app_dirs, sm_app_dirs; /* folders in ux0:app, cached / this scan */
static volatile int g_quick;         /* 1 = quick check found nothing changed */
static volatile int g_checking;      /* the quick check is running */
static int g_full;                   /* this scan must be a full one (START) */
#define DATA_THREADS 1  /* 2 threads measured no faster on a Sony card (23.8 s either way) */
#define MAX_ICONS 64    /* textures kept loaded; the rest are freed and reloaded on demand */
static int icons_loaded;
static uint64_t dev_max, dev_free;
static uint64_t cat_total[NCAT];
static int cat_count[NCAT];
static int today_day;
static int uninstall_ok; /* system uninstaller loaded */

static int can_uninstall(const Item *it) { return uninstall_ok && it->installed && !it->protect; }

/* Confirm/back follow the console setting (○ confirms on Japanese consoles). */
static uint32_t BTN_OK = SCE_CTRL_CROSS, BTN_BACK = SCE_CTRL_CIRCLE;
static int swap_ok;

/* scanner progress, written by the scan thread */
static volatile uint64_t g_scanned_bytes;
static volatile int g_files;
static volatile int g_scan_done;
static char g_stage[2][160];
static volatile int g_stage_idx;

static void set_stage(const char *fmt, ...)
{
    int n = g_stage_idx ^ 1;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(g_stage[n], sizeof g_stage[n], fmt, ap);
    va_end(ap);
    g_stage_idx = n;
}

/* background delete / uninstall job, run off the UI thread */
static volatile int job_running, job_done, job_indet;
static volatile uint64_t job_bytes, job_total;
static char job_label[2][160];
static volatile int job_li;
static int job_ok, job_app_gone;
static char job_err[200];

static void job_stage(int indet, const char *fmt, ...)
{
    int n = job_li ^ 1;
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(job_label[n], sizeof job_label[n], fmt, ap);
    va_end(ap);
    job_indet = indet;
    job_li = n;
}

/* ------------------------------------------------------------- helpers */

static uint32_t rd32(const uint8_t *p) { return p[0] | (p[1] << 8) | (p[2] << 16) | ((uint32_t)p[3] << 24); }
static uint16_t rd16(const uint8_t *p) { return p[0] | (p[1] << 8); }

static int days_civil(int y, unsigned m, unsigned d)
{
    y -= m <= 2;
    int era = (y >= 0 ? y : y - 399) / 400;
    unsigned yoe = (unsigned)(y - era * 400);
    unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + (int)doe - 719468;
}

static int dt_day(const SceDateTime *t)
{
    if (t->year < 1995 || t->month < 1 || t->month > 12 || t->day < 1) return 0;
    return days_civil(t->year, t->month, t->day);
}

static void civil_from_days(int z, int *y, int *m, int *d)
{
    z += 719468;
    int era = (z >= 0 ? z : z - 146096) / 146097;
    unsigned doe = (unsigned)(z - era * 146097);
    unsigned yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    int yy = (int)yoe + era * 400;
    unsigned doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    unsigned mp = (5 * doy + 2) / 153;
    *d = (int)(doy - (153 * mp + 2) / 5 + 1);
    *m = (int)(mp < 10 ? mp + 3 : mp - 9);
    *y = yy + (*m <= 2);
}

static void fmt_date(int day, char *out, int n)
{
    static const char *mon[] = {"Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"};
    int y, m, d;
    if (!day) { snprintf(out, n, "Never"); return; }
    civil_from_days(day, &y, &m, &d);
    snprintf(out, n, "%s %d, %d", mon[m - 1], d, y);
}

static void fmt_ago(int day, char *out, int n)
{
    if (!day) { snprintf(out, n, "Not played yet"); return; }
    int diff = today_day - day;
    if (diff <= 0) snprintf(out, n, "Played today");
    else if (diff == 1) snprintf(out, n, "Played yesterday");
    else if (diff < 14) snprintf(out, n, "Played %d days ago", diff);
    else if (diff < 60) snprintf(out, n, "Played %d weeks ago", diff / 7);
    else if (diff < 730) snprintf(out, n, "Played %d months ago", diff / 30);
    else snprintf(out, n, "Played %d years ago", diff / 365);
}

static void fmt_size(uint64_t b, char *out, int n)
{
    double v = (double)b;
    if (b >= (1ULL << 30)) snprintf(out, n, "%.1f GB", v / (1ULL << 30));
    else if (b >= (1ULL << 20)) snprintf(out, n, "%.0f MB", v / (1ULL << 20));
    else if (b >= 1024) snprintf(out, n, "%.0f KB", v / 1024);
    else if (b > 0) snprintf(out, n, "%u B", (unsigned)b);
    else snprintf(out, n, "0 MB");
}

static void join(char *out, int n, const char *a, const char *b)
{
    size_t l = strlen(a);
    if (l && a[l - 1] == ':') snprintf(out, n, "%s%s", a, b);
    else snprintf(out, n, "%s/%s", a, b);
}

static void lower(char *s) { for (; *s; s++) *s = (char)tolower((unsigned char)*s); }

static int ends_with_ci(const char *s, const char *suf)
{
    size_t a = strlen(s), b = strlen(suf);
    if (a < b) return 0;
    return strcasecmp(s + a - b, suf) == 0;
}

static int is_archive(const char *s)
{
    return ends_with_ci(s, ".vpk") || ends_with_ci(s, ".zip") || ends_with_ci(s, ".7z") ||
           ends_with_ci(s, ".rar") || ends_with_ci(s, ".pkg");
}

static int is_vita_retail_id(const char *id)
{
    if (strncmp(id, "PCS", 3) || !id[3] || id[3] < 'A' || id[3] > 'I') return 0;
    for (int i = 4; i < 9; i++) if (!isdigit((unsigned char)id[i])) return 0;
    return 1;
}

static int path_exists(const char *p) { SceIoStat st; return sceIoGetstat(p, &st) >= 0; }

/* Normalised form: lowercase letters and digits only. */
static void norm(const char *s, char *out, int n)
{
    int j = 0;
    for (; *s && j < n - 1; s++)
        if (isalnum((unsigned char)*s)) out[j++] = (char)tolower((unsigned char)*s);
    out[j] = 0;
}

/* First letter of each word ("Super Mario Galaxy" -> "smg"). */
static void initials(const char *s, char *out, int n)
{
    int j = 0, start = 1;
    for (; *s && j < n - 1; s++) {
        if (isalnum((unsigned char)*s)) {
            if (start) out[j++] = (char)tolower((unsigned char)*s);
            start = 0;
        } else start = 1;
    }
    out[j] = 0;
}

/* Strip ™ ® and line breaks, collapse spaces. */
static void clean_title(char *s)
{
    char *r = s, *w = s;
    int sp = 0;
    while (*r) {
        unsigned char c = (unsigned char)*r;
        if (c == 0xE2 && (unsigned char)r[1] == 0x84 && (unsigned char)r[2] == 0xA2) { r += 3; continue; }
        if (c == 0xC2 && ((unsigned char)r[1] == 0xAE || (unsigned char)r[1] == 0xA9)) { r += 2; continue; }
        if (c == '\n' || c == '\r' || c == '\t' || c == ' ') {
            if (!sp && w != s) *w++ = ' ';
            sp = 1; r++; continue;
        }
        sp = 0;
        *w++ = *r++;
    }
    while (w > s && w[-1] == ' ') w--;
    *w = 0;
}

static uint8_t *read_range(const char *path, uint32_t off, uint32_t len)
{
    if (len == 0 || len > (4u << 20)) return NULL;
    SceUID fd = sceIoOpen(path, SCE_O_RDONLY, 0);
    if (fd < 0) return NULL;
    uint8_t *buf = malloc(len);
    if (buf) {
        if (sceIoLseek(fd, off, SCE_SEEK_SET) != off || sceIoRead(fd, buf, len) != (int)len) { free(buf); buf = NULL; }
    }
    sceIoClose(fd);
    return buf;
}

static uint8_t *read_file(const char *path, uint32_t max, uint32_t *len)
{
    SceIoStat st;
    if (sceIoGetstat(path, &st) < 0 || st.st_size <= 0 || st.st_size > max) return NULL;
    *len = (uint32_t)st.st_size;
    return read_range(path, 0, *len);
}

/* PARAM.SFO lookup. */
static int sfo_get(const uint8_t *b, uint32_t len, const char *key, char *out, int outlen)
{
    if (!b || len < 20 || memcmp(b, "\0PSF", 4)) return 0;
    uint32_t kt = rd32(b + 8), dt = rd32(b + 12), n = rd32(b + 16);
    for (uint32_t i = 0; i < n; i++) {
        uint32_t e = 20 + 16 * i;
        if (e + 16 > len) break;
        uint32_t ko = kt + rd16(b + e), l = rd32(b + e + 4), doff = dt + rd32(b + e + 12);
        uint16_t fmt = rd16(b + e + 2);
        if (ko >= len || doff >= len) continue;
        if (strncmp((const char *)b + ko, key, len - ko)) continue;
        if (fmt == 0x0404) { snprintf(out, outlen, "%u", rd32(b + doff)); return 1; }
        if (doff + l > len) l = len - doff;
        int c = (int)l < outlen - 1 ? (int)l : outlen - 1;
        memcpy(out, b + doff, c);
        out[c] = 0;
        return out[0] != 0;
    }
    return 0;
}

/* ------------------------------------------------- PSP disc (ISO / CSO) */

typedef struct {
    SceUID fd;
    int cso;
    uint32_t block_size, align, nblocks;
    uint32_t *index;
    uint8_t *raw, *blk;
} Disc;

static void disc_close(Disc *d)
{
    if (d->fd >= 0) sceIoClose(d->fd);
    free(d->index); free(d->raw); free(d->blk);
    memset(d, 0, sizeof *d);
    d->fd = -1;
}

static int disc_open(Disc *d, const char *path, int cso)
{
    memset(d, 0, sizeof *d);
    d->fd = sceIoOpen(path, SCE_O_RDONLY, 0);
    if (d->fd < 0) return 0;
    d->cso = cso;
    if (!cso) return 1;
    uint8_t h[24];
    if (sceIoRead(d->fd, h, 24) != 24 || memcmp(h, "CISO", 4)) { disc_close(d); return 0; }
    uint64_t total = rd32(h + 8) | ((uint64_t)rd32(h + 12) << 32);
    d->block_size = rd32(h + 16);
    d->align = h[21];
    if (d->block_size < 2048 || d->block_size > 0x10000 || total == 0) { disc_close(d); return 0; }
    d->nblocks = (uint32_t)((total + d->block_size - 1) / d->block_size);
    uint32_t isz = (d->nblocks + 1) * 4;
    d->index = malloc(isz);
    d->raw = malloc(d->block_size * 2);
    d->blk = malloc(d->block_size);
    if (!d->index || !d->raw || !d->blk || sceIoRead(d->fd, d->index, isz) != (int)isz) { disc_close(d); return 0; }
    return 1;
}

static int disc_read(Disc *d, uint32_t lba, uint8_t *out)
{
    if (!d->cso) {
        if (sceIoLseek(d->fd, (SceOff)lba * 2048, SCE_SEEK_SET) < 0) return 0;
        return sceIoRead(d->fd, out, 2048) == 2048;
    }
    uint64_t off = (uint64_t)lba * 2048;
    uint32_t b = (uint32_t)(off / d->block_size), inb = (uint32_t)(off % d->block_size);
    if (b >= d->nblocks) return 0;
    uint32_t i0 = d->index[b], i1 = d->index[b + 1];
    int plain = (i0 & 0x80000000u) != 0;
    uint64_t p0 = (uint64_t)(i0 & 0x7FFFFFFFu) << d->align, p1 = (uint64_t)(i1 & 0x7FFFFFFFu) << d->align;
    uint32_t len = (uint32_t)(p1 - p0);
    if (len > d->block_size * 2) len = d->block_size * 2;
    if (sceIoLseek(d->fd, (SceOff)p0, SCE_SEEK_SET) < 0) return 0;
    if (plain || len >= d->block_size) {
        if (sceIoRead(d->fd, d->blk, d->block_size) != (int)d->block_size) return 0;
    } else {
        if (sceIoRead(d->fd, d->raw, len) <= 0) return 0;
        z_stream z;
        memset(&z, 0, sizeof z);
        if (inflateInit2(&z, -15) != Z_OK) return 0;
        z.next_in = d->raw; z.avail_in = len;
        z.next_out = d->blk; z.avail_out = d->block_size;
        int r = inflate(&z, Z_FINISH);
        inflateEnd(&z);
        if (r != Z_STREAM_END && z.avail_out != 0) return 0;
    }
    memcpy(out, d->blk + inb, 2048);
    return 1;
}

/* Find name inside the directory at (lba, size). Returns 1 and fills out lba/size. */
static int iso_find(Disc *d, uint32_t dlba, uint32_t dsize, const char *name, uint32_t *olba, uint32_t *osize)
{
    uint8_t sec[2048];
    size_t nl = strlen(name);
    for (uint32_t s = 0; s * 2048 < dsize && s < 64; s++) {
        if (!disc_read(d, dlba + s, sec)) return 0;
        uint32_t p = 0;
        while (p < 2048) {
            uint8_t rl = sec[p];
            if (rl == 0) break;
            if (p + rl > 2048 || rl < 34) break;
            uint8_t fl = sec[p + 32];
            const char *fn = (const char *)sec + p + 33;
            int len = fl;
            for (int k = 0; k < fl; k++) if (fn[k] == ';') { len = k; break; }
            if ((size_t)len == nl && strncasecmp(fn, name, nl) == 0) {
                *olba = rd32(sec + p + 2);
                *osize = rd32(sec + p + 10);
                return 1;
            }
            p += rl;
        }
    }
    return 0;
}

static uint8_t *iso_read_file(const char *path, int cso, const char *dir, const char *file, uint32_t max, uint32_t *len)
{
    Disc d;
    uint8_t *out = NULL, sec[2048];
    if (!disc_open(&d, path, cso)) return NULL;
    uint32_t lba, sz;
    if (disc_read(&d, 16, sec) && memcmp(sec + 1, "CD001", 5) == 0) {
        uint32_t rlba = rd32(sec + 156 + 2), rsz = rd32(sec + 156 + 10);
        if (iso_find(&d, rlba, rsz, dir, &lba, &sz) && iso_find(&d, lba, sz, file, &lba, &sz) && sz && sz <= max) {
            out = malloc(sz + 2048);
            if (out) {
                for (uint32_t i = 0; i * 2048 < sz; i++)
                    if (!disc_read(&d, lba + i, out + i * 2048)) { free(out); out = NULL; break; }
                if (out) *len = sz;
            }
        }
    }
    disc_close(&d);
    return out;
}

/* PBP: returns section n (0 = PARAM.SFO, 1 = ICON0.PNG). */
static uint8_t *pbp_section(const char *path, int n, uint32_t *len)
{
    uint8_t *h = read_range(path, 0, 40);
    if (!h) return NULL;
    uint8_t *out = NULL;
    if (memcmp(h, "\0PBP", 4) == 0) {
        uint32_t a = rd32(h + 8 + 4 * n), b = rd32(h + 8 + 4 * (n + 1));
        if (b > a && b - a < (2u << 20)) { out = read_range(path, a, b - a); if (out) *len = b - a; }
    }
    free(h);
    return out;
}

/* ------------------------------------------------------------- scanning */

static uint64_t g_cluster = 32768;  /* card cluster size, from the device info */
static uint64_t round_cl(uint64_t s) { return (s + g_cluster - 1) / g_cluster * g_cluster; }
static uint64_t dt_key(const SceDateTime *t);

typedef struct { uint64_t size, alloc; int newest; } Acc;

/* Recursive walk. Besides the logical size it estimates the space the folder
 * really occupies (files rounded up to whole clusters, plus each folder's own
 * exFAT directory entries), so changes can be matched against free space. */
static void walk(const char *path, Acc *a)
{
    SceUID d = sceIoDopen(path);
    if (d < 0) return;
    SceIoDirent e;
    uint64_t dir_bytes = 0;
    char sub[1024];
    for (;;) {
        memset(&e, 0, sizeof e);
        if (sceIoDread(d, &e) <= 0) break;
        if (!strcmp(e.d_name, ".") || !strcmp(e.d_name, "..")) continue;
        dir_bytes += 32 * (2 + (strlen(e.d_name) + 14) / 15);
        join(sub, sizeof sub, path, e.d_name);
        if (SCE_S_ISDIR(e.d_stat.st_mode)) walk(sub, a);
        else {
            uint64_t sz = (uint64_t)e.d_stat.st_size;
            a->size += sz;
            a->alloc += round_cl(sz);
            __atomic_add_fetch(&g_files, 1, __ATOMIC_RELAXED);
            __atomic_add_fetch(&g_scanned_bytes, sz, __ATOMIC_RELAXED);
            int dd = dt_day(&e.d_stat.st_mtime);
            if (dd > a->newest && dd <= today_day + 1) a->newest = dd;
        }
    }
    sceIoDclose(d);
    a->alloc += round_cl(dir_bytes ? dir_bytes : 1);
}

/* ---- measured units: every folder (or loose file) the scan sizes. Saved in
 * the cache so a refresh can trust folders whose numbers can't have changed. */
#define MAX_UNITS 6000
typedef struct { uint32_t hash; char path[200]; uint64_t size, alloc; int newest; int isfile; int seen; } Unit;
typedef struct { Unit *u; int n; } Units;
static Units UO, UN, UP; /* last scan (cached), this scan, measured fresh by the probe */
static int incremental;  /* this scan may trust UO */

static uint32_t phash(const char *s)
{
    uint32_t h = 2166136261u;
    for (; *s; s++) h = (h ^ (unsigned char)tolower((unsigned char)*s)) * 16777619u;
    return h;
}

static Unit *ufind(Units *t, const char *path)
{
    uint32_t h = phash(path);
    for (int i = 0; i < t->n; i++)
        if (t->u[i].hash == h && !strcasecmp(t->u[i].path, path)) return &t->u[i];
    return NULL;
}

static Unit *uadd(Units *t, const char *path, uint64_t size, uint64_t alloc, int newest, int isfile)
{
    if (!t->u || t->n >= MAX_UNITS) return NULL;
    Unit *u = &t->u[t->n++];
    memset(u, 0, sizeof *u);
    u->hash = phash(path);
    snprintf(u->path, sizeof u->path, "%s", path);
    u->size = size; u->alloc = alloc; u->newest = newest; u->isfile = isfile;
    return u;
}

static uint64_t unit_from(Unit *u, int *newest)
{
    __atomic_add_fetch(&g_scanned_bytes, u->size, __ATOMIC_RELAXED);
    uadd(&UN, u->path, u->size, u->alloc, u->newest, u->isfile);
    if (newest && u->newest > *newest) *newest = u->newest;
    return u->size;
}

/* Size of a folder: fresh from the probe, trusted from the last scan when
 * refreshing incrementally, otherwise walked now. */
static uint64_t unit_size(const char *path, int *newest)
{
    Unit *u = ufind(&UP, path);
    if (!u && incremental) u = ufind(&UO, path);
    if (u) return unit_from(u, newest);
    Acc a = {0, 0, 0};
    walk(path, &a);
    uadd(&UN, path, a.size, a.alloc, a.newest, 0);
    if (newest && a.newest > *newest) *newest = a.newest;
    return a.size;
}

/* For apps whose fingerprint is unchanged: trust the last scan even in a full scan. */
static uint64_t unit_reuse(const char *path)
{
    Unit *u = ufind(&UP, path);
    if (!u) u = ufind(&UO, path);
    return u ? unit_from(u, NULL) : unit_size(path, NULL);
}

static void unit_file(const char *path, uint64_t size) { uadd(&UN, path, size, round_cl(size), 0, 1); }

typedef struct { char name[256]; int dir; uint64_t size; int day; uint64_t mkey; } Ent;

/* Reads a directory listing (one level). Caller frees. */
static Ent *list_dir(const char *path, int *count)
{
    *count = 0;
    SceUID d = sceIoDopen(path);
    if (d < 0) return NULL;
    int cap = 64, n = 0;
    Ent *v = malloc(sizeof(Ent) * cap);
    SceIoDirent e;
    for (;;) {
        memset(&e, 0, sizeof e);
        if (sceIoDread(d, &e) <= 0) break;
        if (!strcmp(e.d_name, ".") || !strcmp(e.d_name, "..")) continue;
        if (n == cap) { cap *= 2; v = realloc(v, sizeof(Ent) * cap); }
        snprintf(v[n].name, sizeof v[n].name, "%s", e.d_name);
        v[n].dir = SCE_S_ISDIR(e.d_stat.st_mode);
        v[n].size = v[n].dir ? 0 : (uint64_t)e.d_stat.st_size;
        v[n].day = dt_day(&e.d_stat.st_mtime);
        v[n].mkey = dt_key(&e.d_stat.st_mtime);
        n++;
    }
    sceIoDclose(d);
    *count = n;
    return v;
}

/* Model helpers. The scanner calls them on SM and the UI on UM, through the
 * new_item / find_id / add_extra / add_orphan_bubble macros. */
static Item *m_new_item(Model *m, int cat)
{
    if (m->n >= MAX_ITEMS) return NULL;
    Item *it = &m->it[m->n++];
    memset(it, 0, sizeof *it);
    it->cat = cat;
    return it;
}

static Item *m_find_id(Model *m, const char *id, int catmask)
{
    for (int i = 0; i < m->n; i++)
        if ((catmask >> m->it[i].cat) & 1)
            if (m->it[i].id[0] && strcasecmp(m->it[i].id, id) == 0) return &m->it[i];
    return NULL;
}

#define new_item(c) m_new_item(&SM, c)
#define find_id(i, m) m_find_id(&SM, i, m)
#define add_extra(p, n, no, s) m_add_extra(&SM, p, n, no, s)
#define add_orphan_bubble(i, t, s) m_add_orphan_bubble(&SM, i, t, s)

static Item *m_add_extra(Model *m, const char *path, const char *name, const char *note, uint64_t size)
{
    if (size == 0) return NULL;
    Item *it = m_new_item(m, CAT_EXTRA);
    if (!it) return NULL;
    snprintf(it->path, sizeof it->path, "%s", path);
    snprintf(it->name, sizeof it->name, "%s", name);
    snprintf(it->note, sizeof it->note, "%s", note);
    it->size = it->part[P_DATA] = size;
    it->del_kind = DEL_PATH;
    return it;
}

/* An orphaned Adrenaline bubble, listed under Extra Files. */
static void m_add_orphan_bubble(Model *m, const char *id, const char *title, uint64_t size)
{
    char path[64], name[160];
    snprintf(path, sizeof path, "ux0:app/%s", id);
    snprintf(name, sizeof name, "Bubble: %s", title[0] ? title : id);
    Item *it = m_add_extra(m, path, name, "Adrenaline bubble for a game that's no longer on the card", size ? size : 1);
    if (!it) return;
    snprintf(it->id, sizeof it->id, "%s", id);
    snprintf(it->icon_src, sizeof it->icon_src, "%s/sce_sys/icon0.png", path);
    it->icon_kind = ICON_FILE;
    it->del_kind = uninstall_ok ? DEL_APP : DEL_NONE;
    if (!uninstall_ok) snprintf(it->note, sizeof it->note, "Orphaned bubble; hold it on the home screen and choose Delete");
}

/* Core tools that must never be uninstalled from here: this app, the file
 * manager, PSP/PS1 support, the package installer and the exploit/plugin tools. */
static const char *protected_ids[] = {
    "STRG00001", "VITASHELL", "MLCL00001", "PSPEMUCFW", "ADRBUBMAN", "PKGJ00000",
    "AUTOPLUG2", "SKGD3PL0Y", "SKGTLSE12", "SKGYAMT01", "SHARKF00D", "PCSI00011",
    "SKGH3NKAK", "HENKAKU01", "SKGPKGI00",
    "RETROLNCR", /* RetroFlow's Adrenaline launcher: has a bubble-style boot.bin but isn't a game bubble */
};

/* ---- user settings: ux0:data/Storage/settings.txt
 *   data <folder> = <TITLE ID>   link a ux0:data folder to its app
 *   protect <TITLE ID>           never offer to uninstall this app
 *   shared <folder>              a data folder several apps use      */
#define SETTINGS_PATH "ux0:data/Storage/settings.txt"
#define MAX_USER 64
static char ua_folder[MAX_USER][64], ua_id[MAX_USER][16];
static char up_id[MAX_USER][16], us_folder[MAX_USER][64];
static int n_ua, n_up, n_us;

static const char *SETTINGS_DEFAULT =
    "# Vita Storage Manager settings. Lines starting with # are ignored.\n"
    "#\n"
    "# Link a ux0:data folder to the app that uses it, when Storage Manager\n"
    "# can't tell from the names (use the app's title ID, shown in its details):\n"
    "#   data kotor2 = KOTR00002\n"
    "#\n"
    "# Never offer to uninstall an app:\n"
    "#   protect VITASHELL\n"
    "#\n"
    "# A data folder that several apps use. It's never ticked for deletion\n"
    "# by default when one of them is uninstalled:\n"
    "#   shared retroarch\n"
    "\n";

static void trim(char *s)
{
    char *e = s + strlen(s);
    while (e > s && isspace((unsigned char)e[-1])) *--e = 0;
    char *b = s;
    while (*b && isspace((unsigned char)*b)) b++;
    if (b != s) memmove(s, b, strlen(b) + 1);
}

static void load_settings(void)
{
    uint32_t len = 0;
    char *buf = (char *)read_file(SETTINGS_PATH, 1 << 16, &len);
    if (!buf) {
        sceIoMkdir("ux0:data/Storage", 0777);
        SceUID f = sceIoOpen(SETTINGS_PATH, SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC, 0777);
        if (f >= 0) { sceIoWrite(f, SETTINGS_DEFAULT, strlen(SETTINGS_DEFAULT)); sceIoClose(f); }
        return;
    }
    buf = realloc(buf, len + 1);
    buf[len] = 0;
    for (char *line = strtok(buf, "\r\n"); line; line = strtok(NULL, "\r\n")) {
        char l[256];
        snprintf(l, sizeof l, "%s", line);
        char *hash = strchr(l, '#');
        if (hash) *hash = 0;
        trim(l);
        if (!strncasecmp(l, "data ", 5)) {
            char *eq = strchr(l, '=');
            if (!eq || n_ua >= MAX_USER) continue;
            *eq = 0;
            char a[64], b[32];
            snprintf(a, sizeof a, "%s", l + 5); trim(a);
            snprintf(b, sizeof b, "%s", eq + 1); trim(b);
            if (a[0] && b[0]) { norm(a, ua_folder[n_ua], sizeof ua_folder[0]); snprintf(ua_id[n_ua], sizeof ua_id[0], "%s", b); n_ua++; }
        } else if (!strncasecmp(l, "protect ", 8) && n_up < MAX_USER) {
            snprintf(up_id[n_up], sizeof up_id[0], "%s", l + 8); trim(up_id[n_up]);
            if (up_id[n_up][0]) n_up++;
        } else if (!strncasecmp(l, "shared ", 7) && n_us < MAX_USER) {
            char a[64];
            snprintf(a, sizeof a, "%s", l + 7); trim(a);
            if (a[0]) { norm(a, us_folder[n_us], sizeof us_folder[0]); n_us++; }
        }
    }
    free(buf);
}

static int is_protected(const char *id)
{
    for (unsigned i = 0; i < sizeof protected_ids / sizeof protected_ids[0]; i++)
        if (!strcasecmp(id, protected_ids[i])) return 1;
    for (int i = 0; i < n_up; i++) if (!strcasecmp(id, up_id[i])) return 1;
    return 0;
}

/* Data folders that several apps may read, so they're never ticked by default. */
static const char *shared_data[] = { "retroarch", "retroflow", "pspemu", "savedata", "plugins", "tai" };

/* Adrenaline bubble: data/boot.bin = "ABB" ... launch path at 0x40. */
static int read_bubble(const char *app_dir, char *target, int n)
{
    char p[400];
    snprintf(p, sizeof p, "%s/data/boot.bin", app_dir);
    uint32_t len = 0;
    uint8_t *b = read_file(p, 1 << 16, &len);
    int ok = 0;
    if (b && len > 0x41 && memcmp(b, "ABB", 3) == 0) {
        int m = 0;
        for (uint32_t i = 0x40; i < len && b[i] && m < n - 1; i++) target[m++] = (char)b[i];
        target[m] = 0;
        lower(target);
        for (char *c = target; *c; c++) if (*c == '\\') *c = '/';
        if (!strncmp(target, "ms0:/", 5) || !strncmp(target, "ef0:/", 5)) {
            char t[300];
            snprintf(t, sizeof t, "ux0:pspemu/%s", target + 5);
            snprintf(target, n, "%s", t);
        }
        ok = 1;
    }
    free(b);
    return ok;
}

static uint64_t dt_key(const SceDateTime *t)
{
    return ((((((uint64_t)t->year * 13 + t->month) * 32 + t->day) * 24 + t->hour) * 60 + t->minute) * 60 + t->second) * 1000000ULL + t->microsecond;
}

/* Fingerprint of an installed app: changes when it is reinstalled or updated in place. */
static uint64_t app_key(const char *app_dir)
{
    static const char *files[] = {"", "/eboot.bin", "/sce_sys/param.sfo"};
    char p[400];
    uint64_t k = 1469598103934665603ULL;
    for (int i = 0; i < 3; i++) {
        SceIoStat st;
        snprintf(p, sizeof p, "%s%s", app_dir, files[i]);
        if (sceIoGetstat(p, &st) < 0) { if (i == 0) return 0; continue; }
        k = (k ^ dt_key(&st.st_mtime)) * 1099511628211ULL;
        k = (k ^ (uint64_t)st.st_size) * 1099511628211ULL;
    }
    return k;
}

static void scan_apps(void)
{
    int n;
    Ent *v = list_dir("ux0:app", &n);
    char p[512], sfo_path[512], target[256];
    sm_app_dirs = 0;
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        sm_app_dirs++;
        set_stage("Apps and games (%d of %d)", i + 1, n);
        join(p, sizeof p, "ux0:app", v[i].name);

        int is_bub = !is_protected(v[i].name) && read_bubble(p, target, sizeof target);
        if (is_bub || (strncmp(v[i].name, "PSPEMU", 6) == 0 && !is_protected(v[i].name))) {
            uint64_t sz = unit_size(p, NULL);
            if (is_bub && nbubbles < MAX_BUBBLES) {
                Bubble *b = &bubbles[nbubbles++];
                memset(b, 0, sizeof *b);
                snprintf(b->id, sizeof b->id, "%s", v[i].name);
                snprintf(b->target, sizeof b->target, "%s", target);
                b->size = sz;
                snprintf(sfo_path, sizeof sfo_path, "%s/sce_sys/param.sfo", p);
                uint32_t len = 0;
                uint8_t *sfo = read_file(sfo_path, 1 << 16, &len);
                sfo_get(sfo, len, "TITLE", b->title, sizeof b->title);
                free(sfo);
                clean_title(b->title);
            }
            continue; /* bubbles are attached to their games later */
        }

        uint64_t key = app_key(p);
        Item *old = key ? m_find_id(&UM, v[i].name, (1 << CAT_VITA) | (1 << CAT_HB)) : NULL;
        if (old && old->installed && old->key == key) {
            /* unchanged since the last scan: reuse its size and title */
            Item *it = new_item(old->cat);
            if (!it) break;
            *it = *old;
            memset(it->part + 1, 0, sizeof(uint64_t) * (NPART - 1));
            it->ndata = 0;
            it->last_day = 0;
            it->size = 0;
            it->icon = NULL;
            it->icon_state = 0;
            unit_reuse(p);
            continue;
        }

        Item *it = new_item(is_vita_retail_id(v[i].name) ? CAT_VITA : CAT_HB);
        if (!it) break;
        snprintf(it->id, sizeof it->id, "%s", v[i].name);
        snprintf(it->path, sizeof it->path, "%s", p);
        it->key = key;
        it->part[P_APP] = unit_size(p, NULL);
        snprintf(sfo_path, sizeof sfo_path, "%s/sce_sys/param.sfo", p);
        uint32_t len = 0;
        uint8_t *sfo = read_file(sfo_path, 1 << 16, &len);
        if (!sfo_get(sfo, len, "TITLE", it->name, sizeof it->name) &&
            !sfo_get(sfo, len, "STITLE", it->name, sizeof it->name))
            snprintf(it->name, sizeof it->name, "%s", v[i].name);
        free(sfo);
        clean_title(it->name);
        if (!it->name[0]) snprintf(it->name, sizeof it->name, "%s", v[i].name);
        snprintf(it->icon_src, sizeof it->icon_src, "%s/sce_sys/icon0.png", p);
        it->icon_kind = ICON_FILE;
        it->installed = 1;
        it->protect = is_protected(v[i].name);
        if (it->protect)
            snprintf(it->note, sizeof it->note, "Protected: Storage won't uninstall this core tool.");
    }
    free(v);
}

/* ux0:patch and ux0:addcont belong to installed apps; orphans are extras. */
static void scan_addons(const char *root, int part, const char *what)
{
    int n;
    Ent *v = list_dir(root, &n);
    char p[512], sfo_path[512], name[160], title[128];
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        set_stage("%s (%d of %d)", what, i + 1, n);
        join(p, sizeof p, root, v[i].name);
        uint64_t sz = unit_size(p, NULL);
        Item *owner = find_id(v[i].name, (1 << CAT_VITA) | (1 << CAT_HB));
        if (owner) { owner->part[part] += sz; continue; }
        title[0] = 0;
        snprintf(sfo_path, sizeof sfo_path, "%s/sce_sys/param.sfo", p);
        uint32_t len = 0;
        uint8_t *sfo = read_file(sfo_path, 1 << 16, &len);
        sfo_get(sfo, len, "TITLE", title, sizeof title);
        free(sfo);
        clean_title(title);
        snprintf(name, sizeof name, "%s: %s", part == P_UPD ? "Update" : "DLC", title[0] ? title : v[i].name);
        Item *it = add_extra(p, name, part == P_UPD ? "Update for a game that is no longer installed"
                                                    : "DLC for a game that is no longer installed", sz);
        if (it) snprintf(it->id, sizeof it->id, "%s", v[i].name);
    }
    free(v);
}

/* Known ux0:data folder names that don't resemble their app's title. */
static const char *data_alias[][2] = {
    {"kotor2", "KOTR00002"}, {"2s2h", "2SHIP2HAR"}, {"c2port", "C2VITA001"},
    {"goldeneye007", "GEVT00001"}, {"soh", "SHIPOFHAR"}, {"pd", "PRFCTDARK"},
    {"smg", "SMGV00001"}, {"thug", "THUG00001"}, {"melee", "MLVITA002"},
    {"mania", "MANIA0001"}, {"lighthouse", "BANJO0064"}, {"outlaw", "OUTLAW001"},
    {"fury3", "FURY00003"}, {"azahar", "AZAHARPSV"}, {"retroarch", "RETROVITA"},
    {"papership", "PPMR00001"},
};

/* Finds the homebrew app a ux0:data folder belongs to. *sure is set when the
 * match is strong and unambiguous (safe to tick for deletion by default). */
static Item *match_data(const char *folder, int *sure)
{
    char f[256], t[256], ini[64], id[32];
    *sure = 0;
    norm(folder, f, sizeof f);
    if (!f[0]) return NULL;
    int shared = 0;
    for (unsigned s = 0; s < sizeof shared_data / sizeof shared_data[0]; s++)
        if (!strcmp(f, shared_data[s])) shared = 1;
    for (int s = 0; s < n_us; s++) if (!strcmp(f, us_folder[s])) shared = 1;
    for (int a = 0; a < n_ua; a++)            /* the user's own links come first */
        if (!strcmp(f, ua_folder[a])) {
            Item *it = find_id(ua_id[a], 1 << CAT_HB);
            if (it) { *sure = !shared; return it; }
        }
    for (unsigned a = 0; a < sizeof data_alias / sizeof data_alias[0]; a++)
        if (!strcmp(f, data_alias[a][0])) {
            Item *it = find_id(data_alias[a][1], 1 << CAT_HB);
            if (it) { *sure = !shared; return it; }
        }
    Item *best = NULL;
    int best_score = 0, second = 0;
    for (int i = 0; i < nitems; i++) {
        Item *it = &items[i];
        if (it->cat != CAT_HB || !it->installed) continue;
        norm(it->name, t, sizeof t);
        norm(it->id, id, sizeof id);
        initials(it->name, ini, sizeof ini);
        int s = 0;
        if (!strcmp(f, t) || !strcmp(f, id)) s = 1000;
        else if (strlen(f) >= 4 && strstr(t, f)) s = 300 + (int)strlen(f);
        else if (strlen(t) >= 4 && strstr(f, t)) s = 300 + (int)strlen(t);
        else if (strlen(f) >= 4 && strstr(id, f)) s = 200 + (int)strlen(f);
        else if (strlen(f) >= 2 && strlen(ini) >= 2 && !strcmp(f, ini)) s = 100;
        if (s > best_score) { second = best_score; best_score = s; best = it; }
        else if (s > second) second = s;
    }
    /* exact or title-containment matches with no close rival count as sure */
    *sure = best && !shared && best_score >= 300 && second < 200;
    return best;
}

static void add_data_folder(Item *it, const char *path, uint64_t size, int sure)
{
    it->part[P_DATA] += size;
    if (it->ndata >= 4) return;
    snprintf(it->data_paths[it->ndata], sizeof it->data_paths[0], "%s", path);
    it->data_sizes[it->ndata] = size;
    it->data_sure[it->ndata] = (unsigned char)sure;
    it->ndata++;
}

/* Folder sizes for ux0:data are measured by DATA_THREADS workers sharing a
 * queue; matching them to apps happens afterwards on the scan thread. */
static Ent *pd_ents;
static int pd_n;
static volatile int pd_next, pd_done;
static uint64_t *pd_size;
static int *pd_newest;

static int data_worker(SceSize args, void *argp)
{
    (void)args; (void)argp;
    char p[512];
    for (;;) {
        int i = __atomic_fetch_add(&pd_next, 1, __ATOMIC_RELAXED);
        if (i >= pd_n) break;
        if (pd_ents[i].dir && strcasecmp(pd_ents[i].name, "Storage")) {
            join(p, sizeof p, "ux0:data", pd_ents[i].name);
            int newest = 0;
            pd_size[i] = unit_size(p, &newest);
            pd_newest[i] = newest;
        }
        __atomic_add_fetch(&pd_done, 1, __ATOMIC_RELAXED);
    }
    sceKernelExitDeleteThread(0);
    return 0;
}

static void measure_data_parallel(Ent *v, int n)
{
    pd_ents = v; pd_n = n; pd_next = 0; pd_done = 0;
    pd_size = calloc(n ? n : 1, sizeof(uint64_t));
    pd_newest = calloc(n ? n : 1, sizeof(int));
    SceUID th[DATA_THREADS];
    int started = 0;
    for (int t = 0; t < DATA_THREADS; t++) {
        th[t] = sceKernelCreateThread("datascan", data_worker, 0x10000100, 256 * 1024, 0, 0, NULL);
        if (th[t] >= 0 && sceKernelStartThread(th[t], 0, NULL) >= 0) started++;
    }
    if (!started) { data_worker(0, NULL); return; }  /* fall back to doing it here */
    while (pd_done < n) {
        set_stage("App data (%d of %d)", pd_done, n);
        sceKernelDelayThread(100000);
    }
}

static void scan_data(void)
{
    int n;
    Ent *v = list_dir("ux0:data", &n);
    char p[512], name[300];
    measure_data_parallel(v, n);
    for (int i = 0; i < n; i++) {
        join(p, sizeof p, "ux0:data", v[i].name);
        if (!v[i].dir) {
            g_scanned_bytes += v[i].size;
            unit_file(p, v[i].size);
            if (is_archive(v[i].name)) {
                snprintf(name, sizeof name, "%s", v[i].name);
                add_extra(p, name, "Installer or archive left in ux0:data", v[i].size);
            }
            continue;
        }
        if (!strcasecmp(v[i].name, "Storage")) continue; /* our own folder */
        int newest = pd_newest[i];
        uint64_t sz = pd_size[i];
        int sure = 0;
        Item *owner = match_data(v[i].name, &sure);
        if (owner) {
            add_data_folder(owner, p, sz, sure);
            if (newest > owner->last_day) owner->last_day = newest;
            continue;
        }
        Item *it = new_item(CAT_HB);
        if (!it) break;
        snprintf(it->name, sizeof it->name, "%s", v[i].name);
        snprintf(it->path, sizeof it->path, "%s", p);
        snprintf(it->note, sizeof it->note, "Data folder; its app wasn't identified. Check before deleting.");
        it->part[P_DATA] = sz;
        it->size = sz;
        it->last_day = newest;
        it->del_kind = DEL_PATH;
    }
    free(v);
    free(pd_size); pd_size = NULL;
    free(pd_newest); pd_newest = NULL;
}

static void scan_psp_isos(const char *dir)
{
    int n;
    Ent *v = list_dir(dir, &n);
    char p[512], title[128], disc[24];
    for (int i = 0; i < n; i++) {
        join(p, sizeof p, dir, v[i].name);
        if (v[i].dir) { scan_psp_isos(p); continue; }
        g_scanned_bytes += v[i].size;
        g_files++;
        unit_file(p, v[i].size);
        int cso = ends_with_ci(v[i].name, ".cso");
        if (!cso && !ends_with_ci(v[i].name, ".iso")) {
            if (is_archive(v[i].name)) add_extra(p, v[i].name, "Archive left in the PSP ISO folder", v[i].size);
            continue;
        }
        set_stage("PSP games (%d of %d)", i + 1, n);

        /* same file as last time (path, size, date): reuse its title instead of opening the image */
        Item *old = NULL;
        for (int k = 0; k < UM.n && !old; k++)
            if (UM.it[k].cat == CAT_PSP && UM.it[k].key == v[i].mkey && UM.it[k].part[P_APP] == v[i].size &&
                !strcasecmp(UM.it[k].path, p)) old = &UM.it[k];
        if (old) {
            Item *it = new_item(CAT_PSP);
            if (!it) break;
            *it = *old;
            memset(it->part + 1, 0, sizeof(uint64_t) * (NPART - 1));
            it->nbub = 0;
            it->last_day = 0;
            it->size = 0;
            it->icon = NULL;
            it->icon_state = 0;
            continue;
        }

        Item *it = new_item(CAT_PSP);
        if (!it) break;
        snprintf(it->path, sizeof it->path, "%s", p);
        it->key = v[i].mkey;
        it->part[P_APP] = v[i].size;
        it->del_kind = DEL_PATH;
        it->icon_kind = cso ? ICON_CSO : ICON_ISO;
        snprintf(it->icon_src, sizeof it->icon_src, "%s", p);
        title[0] = disc[0] = 0;
        uint32_t len = 0;
        uint8_t *sfo = iso_read_file(p, cso, "PSP_GAME", "PARAM.SFO", 1 << 16, &len);
        sfo_get(sfo, len, "TITLE", title, sizeof title);
        sfo_get(sfo, len, "DISC_ID", disc, sizeof disc);
        free(sfo);
        clean_title(title);
        if (title[0]) snprintf(it->name, sizeof it->name, "%s", title);
        else {
            snprintf(it->name, sizeof it->name, "%s", v[i].name);
            char *dot = strrchr(it->name, '.');
            if (dot) *dot = 0;
        }
        snprintf(it->id, sizeof it->id, "%s", disc);
    }
    free(v);
}

static void scan_psp_game(void)
{
    const char *root = "ux0:pspemu/PSP/GAME";
    int n;
    Ent *v = list_dir(root, &n);
    char p[512], eboot[600], title[128], cat[16], disc[24];
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        set_stage("PSP and PS1 titles (%d of %d)", i + 1, n);
        join(p, sizeof p, root, v[i].name);
        snprintf(eboot, sizeof eboot, "%s/EBOOT.PBP", p);
        title[0] = cat[0] = disc[0] = 0;
        uint32_t len = 0;
        uint8_t *sfo = pbp_section(eboot, 0, &len);
        sfo_get(sfo, len, "TITLE", title, sizeof title);
        sfo_get(sfo, len, "CATEGORY", cat, sizeof cat);
        sfo_get(sfo, len, "DISC_ID", disc, sizeof disc);
        free(sfo);
        clean_title(title);
        Item *it = new_item(!strcmp(cat, "ME") ? CAT_PS1 : CAT_PSP);
        if (!it) break;
        snprintf(it->path, sizeof it->path, "%s", p);
        snprintf(it->name, sizeof it->name, "%s", title[0] ? title : v[i].name);
        snprintf(it->id, sizeof it->id, "%s", disc[0] ? disc : v[i].name);
        it->part[P_APP] = unit_size(p, NULL);
        it->del_kind = DEL_PATH;
        it->icon_kind = ICON_PBP;
        snprintf(it->icon_src, sizeof it->icon_src, "%s", eboot);
    }
    free(v);
}

/* Attach each Adrenaline bubble to the PSP/PS1 game it launches. Bubbles that
 * point at a game that's gone become Extra Files. Writes a log for checking. */
static void link_bubbles(void)
{
    char lp[340], le[340];
    SceUID log = -1;
    sceIoMkdir("ux0:data/Storage", 0777);
    log = sceIoOpen("ux0:data/Storage/bubbles.log", SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC, 0777);
    for (int b = 0; b < nbubbles; b++) {
        Bubble *bu = &bubbles[b];
        Item *hit = NULL;
        for (int i = 0; i < nitems && !hit; i++) {
            Item *it = &items[i];
            if (it->cat != CAT_PSP && it->cat != CAT_PS1) continue;
            snprintf(lp, sizeof lp, "%s", it->path); lower(lp);
            snprintf(le, sizeof le, "%s", it->icon_src); lower(le);
            size_t pl = strlen(lp);
            if (!strcmp(bu->target, lp) || !strcmp(bu->target, le) ||
                (!strncmp(bu->target, lp, pl) && bu->target[pl] == '/'))
                hit = it;
        }
        const char *what;
        if (hit) {
            if (hit->nbub < MAX_BUB_PER_GAME) {
                snprintf(hit->bub_ids[hit->nbub], sizeof hit->bub_ids[0], "%s", bu->id);
                hit->bub_sizes[hit->nbub] = bu->size;
                hit->nbub++;
            }
            hit->part[P_BUB] += bu->size;
            bu->linked = 1;
            what = "linked";
        } else if (bu->target[0] && !path_exists(bu->target)) {
            add_orphan_bubble(bu->id, bu->title, bu->size);
            what = "orphan (target missing)";
        } else what = "unlinked (target exists elsewhere)";
        if (log >= 0) {
            char line[700];
            int l = snprintf(line, sizeof line, "%s | %s | %s | %s%s%s\n", bu->id, bu->title, bu->target, what,
                             hit ? " -> " : "", hit ? hit->name : "");
            sceIoWrite(log, line, l);
        }
    }
    if (log >= 0) sceIoClose(log);
}

static void copy_icon(Item *dst, const Item *src)
{
    dst->icon_kind = src->icon_kind;
    snprintf(dst->icon_src, sizeof dst->icon_src, "%s", src->icon_src);
}

static void scan_saves(void)
{
    char p[512], sfo_path[600], title[128];
    int n;
    /* Vita (and some homebrew) saves: one folder per title ID */
    Ent *v = list_dir("ux0:user/00/savedata", &n);
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        set_stage("Vita saves (%d of %d)", i + 1, n);
        join(p, sizeof p, "ux0:user/00/savedata", v[i].name);
        int newest = 0;
        uint64_t sz = unit_size(p, &newest);
        Item *game = find_id(v[i].name, (1 << CAT_VITA) | (1 << CAT_HB));
        Item *it = new_item(CAT_SAVE);
        if (!it) break;
        snprintf(it->id, sizeof it->id, "%s", v[i].name);
        snprintf(it->path, sizeof it->path, "%s", p);
        it->size = it->part[P_SAVE] = sz;
        it->last_day = newest;
        it->del_kind = DEL_PATH;
        if (game) {
            snprintf(it->name, sizeof it->name, "%s", game->name);
            copy_icon(it, game);
            game->part[P_SAVE] += sz;
            if (newest > game->last_day) game->last_day = newest;
        } else {
            snprintf(it->name, sizeof it->name, "%s", v[i].name);
            snprintf(it->note, sizeof it->note, "Save for a title that is not installed");
        }
    }
    free(v);

    /* PSP / PS1 saves: SAVEDATA/<9-char game ID><suffix>, grouped by game ID */
    const char *sroot = "ux0:pspemu/PSP/SAVEDATA";
    v = list_dir(sroot, &n);
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        set_stage("PSP saves (%d of %d)", i + 1, n);
        char gid[16];
        snprintf(gid, sizeof gid, "%.9s", v[i].name);
        join(p, sizeof p, sroot, v[i].name);
        int newest = 0;
        uint64_t sz = unit_size(p, &newest);
        Item *it = NULL;
        for (int k = 0; k < nitems; k++)
            if (items[k].cat == CAT_SAVE && items[k].del_kind == DEL_PREFIX && !strcmp(items[k].id, gid)) { it = &items[k]; break; }
        Item *game = find_id(gid, (1 << CAT_PSP) | (1 << CAT_PS1));
        if (!it) {
            it = new_item(CAT_SAVE);
            if (!it) break;
            snprintf(it->id, sizeof it->id, "%s", gid);
            snprintf(it->path, sizeof it->path, "%s", sroot);
            it->del_kind = DEL_PREFIX;
            if (game) { snprintf(it->name, sizeof it->name, "%s", game->name); copy_icon(it, game); }
            else {
                title[0] = 0;
                snprintf(sfo_path, sizeof sfo_path, "%s/PARAM.SFO", p);
                uint32_t len = 0;
                uint8_t *sfo = read_file(sfo_path, 1 << 16, &len);
                sfo_get(sfo, len, "TITLE", title, sizeof title);
                free(sfo);
                clean_title(title);
                snprintf(it->name, sizeof it->name, "%s", title[0] ? title : gid);
                snprintf(it->icon_src, sizeof it->icon_src, "%s/ICON0.PNG", p);
                it->icon_kind = ICON_FILE;
                snprintf(it->note, sizeof it->note, "Save for a game that is not on this card");
            }
        }
        it->size += sz;
        it->part[P_SAVE] += sz;
        if (newest > it->last_day) it->last_day = newest;
        if (game) { game->part[P_SAVE] += sz; if (newest > game->last_day) game->last_day = newest; }
    }
    free(v);
}

static void scan_media(void)
{
    static const char *dirs[][2] = {
        {"ux0:video", "Videos"}, {"ux0:music", "Music"}, {"ux0:picture", "Pictures & Screenshots"}
    };
    set_stage("Media");
    for (int i = 0; i < 3; i++) {
        int newest = 0;
        uint64_t sz = unit_size(dirs[i][0], &newest);
        if (!sz) continue;
        Item *it = new_item(CAT_MEDIA);
        if (!it) return;
        snprintf(it->name, sizeof it->name, "%s", dirs[i][1]);
        snprintf(it->path, sizeof it->path, "%s", dirs[i][0]);
        it->size = it->part[P_DATA] = sz;
        it->last_day = newest;
        snprintf(it->note, sizeof it->note, "Manage these in the Vita's own Video, Music and Photos apps");
    }
}

static void scan_extras(void)
{
    char p[512], name[300];
    int n;
    set_stage("Extra files");
    /* loose installers and archives in the card root */
    Ent *v = list_dir("ux0:", &n);
    for (int i = 0; i < n; i++) {
        if (v[i].dir) continue;
        join(p, sizeof p, "ux0:", v[i].name);
        g_scanned_bytes += v[i].size;
        unit_file(p, v[i].size);
        if (is_archive(v[i].name))
            add_extra(p, v[i].name, ends_with_ci(v[i].name, ".vpk") ? "App installer (VPK) in the card root" : "Archive in the card root", v[i].size);
    }
    free(v);

    static const char *dl_dirs[][2] = {
        {"ux0:downloads", "Downloaded file"}, {"ux0:download", "Downloaded file"}, {"ux0:VPKs", "Stored app installer"}
    };
    for (int d = 0; d < 3; d++) {
        v = list_dir(dl_dirs[d][0], &n);
        for (int i = 0; i < n; i++) {
            join(p, sizeof p, dl_dirs[d][0], v[i].name);
            uint64_t sz = v[i].dir ? unit_size(p, NULL) : v[i].size;
            if (!v[i].dir) { g_scanned_bytes += sz; unit_file(p, sz); }
            add_extra(p, v[i].name, dl_dirs[d][1], sz);
        }
        free(v);
    }

    /* PKGj: sub-folders are unfinished or leftover installs */
    v = list_dir("ux0:pkgj", &n);
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        join(p, sizeof p, "ux0:pkgj", v[i].name);
        snprintf(name, sizeof name, "PKGj leftover: %s", v[i].name);
        add_extra(p, name, "Unfinished or leftover PKGj download", unit_size(p, NULL));
    }
    free(v);

    static const char *misc[][3] = {
        {"ux0:bgdl", "Background downloads", "Leftover background-download files"},
        {"ux0:temp", "Temporary files", "Temporary files"},
        {"ux0:SceIoTrash", "System trash", "Files the system marked for deletion"},
    };
    for (int i = 0; i < 3; i++) {
        uint64_t sz = unit_size(misc[i][0], NULL);
        if (sz >= (1u << 20)) add_extra(misc[i][0], misc[i][1], misc[i][2], sz);
    }
}

/* Folders that hold no listed items but do change (system metadata, plugins,
 * Adrenaline's own files). Measuring them lets a refresh account for every
 * change in free space. They count toward "System & Other". */
static int name_in(const char *name, const char *const *list, int n)
{
    for (int i = 0; i < n; i++) if (!strcasecmp(name, list[i])) return 1;
    return 0;
}

static void scan_other(void)
{
    static const char *root_known[] = {"app", "patch", "addcont", "data", "pspemu", "user", "pkgj", "downloads",
                                       "download", "VPKs", "bgdl", "temp", "SceIoTrash", "video", "music",
                                       "picture", "System Volume Information"};
    static const struct { const char *dir; const char *skip[3]; } sub[] = {
        {"ux0:user/00", {"savedata", NULL, NULL}},
        {"ux0:pspemu", {"ISO", "PSP", NULL}},
        {"ux0:pspemu/PSP", {"GAME", "SAVEDATA", NULL}},
    };
    char p[512];
    int n;
    set_stage("System files");
    Ent *v = list_dir("ux0:", &n);
    for (int i = 0; i < n; i++)
        if (v[i].dir && !name_in(v[i].name, root_known, sizeof root_known / sizeof root_known[0])) {
            join(p, sizeof p, "ux0:", v[i].name);
            unit_size(p, NULL);
        }
    free(v);
    /* Loose files in folders the refresh compares but no stage records
     * (PKGj's title lists and config, stray files next to apps or saves). */
    static const char *loose[] = {"ux0:pkgj", "ux0:app", "ux0:patch", "ux0:addcont", "ux0:user/00/savedata",
                                  "ux0:pspemu/PSP/SAVEDATA", "ux0:pspemu/PSP/GAME"};
    for (unsigned s = 0; s < sizeof loose / sizeof loose[0]; s++) {
        v = list_dir(loose[s], &n);
        for (int i = 0; i < n; i++)
            if (!v[i].dir) { join(p, sizeof p, loose[s], v[i].name); unit_file(p, v[i].size); }
        free(v);
    }
    for (unsigned s = 0; s < sizeof sub / sizeof sub[0]; s++) {
        v = list_dir(sub[s].dir, &n);
        for (int i = 0; i < n; i++) {
            int skip = 0;
            for (int k = 0; k < 3 && sub[s].skip[k]; k++) if (!strcasecmp(v[i].name, sub[s].skip[k])) skip = 1;
            if (skip) continue;
            join(p, sizeof p, sub[s].dir, v[i].name);
            if (v[i].dir) unit_size(p, NULL);
            else unit_file(p, v[i].size);
        }
        free(v);
    }
}

/* --------------------------------------------------- incremental refresh */

/* How likely a unit is to have changed, highest first. The probe always walks
 * classes >= 60, then stops as soon as the changes add up to the change in
 * free space. */
static int unit_class(const char *p)
{
    if (!strncasecmp(p, "ux0:picture", 11) || !strncasecmp(p, "ux0:video", 9) || !strncasecmp(p, "ux0:music", 9)) return 90;
    if (!strncasecmp(p, "ux0:user/00/savedata/", 21) || !strncasecmp(p, "ux0:pspemu/PSP/SAVEDATA/", 24)) return 80;
    if (!strncasecmp(p, "ux0:pspemu/", 11) && strncasecmp(p, "ux0:pspemu/ISO", 14) && strncasecmp(p, "ux0:pspemu/PSP/GAME", 19)) return 70;
    if (!strncasecmp(p, "ux0:data/", 9)) return 60;
    if (!strncasecmp(p, "ux0:bgdl", 8) || !strncasecmp(p, "ux0:temp", 8) || !strncasecmp(p, "ux0:SceIoTrash", 14) ||
        !strncasecmp(p, "ux0:pkgj/", 9) || !strncasecmp(p, "ux0:download", 12) || !strncasecmp(p, "ux0:VPKs/", 9)) return 50;
    if (!strncasecmp(p, "ux0:patch/", 10) || !strncasecmp(p, "ux0:addcont/", 12)) return 20;
    if (!strncasecmp(p, "ux0:app/", 8) || !strncasecmp(p, "ux0:pspemu/PSP/GAME/", 20)) return 10;
    return 30;
}

typedef struct { int idx, cls, newest; } Cand;
static int cmp_cand(const void *a, const void *b)
{
    const Cand *x = a, *y = b;
    if (x->cls != y->cls) return y->cls - x->cls;
    return y->newest - x->newest;
}

static char probe_log[2400];

/* The biggest differences the probe found, for the log. */
typedef struct { char path[96]; int64_t delta; } Diff;
static Diff diffs[12];
static int ndiffs;

static void note_diff(const char *path, int64_t delta)
{
    if (!delta) return;
    int64_t ad = delta < 0 ? -delta : delta;
    int slot = ndiffs < 12 ? ndiffs++ : -1;
    if (slot < 0) {                       /* replace the smallest if this one is bigger */
        int m = 0;
        for (int i = 1; i < 12; i++) if (llabs(diffs[i].delta) < llabs(diffs[m].delta)) m = i;
        if (llabs(diffs[m].delta) >= ad) return;
        slot = m;
    }
    snprintf(diffs[slot].path, sizeof diffs[slot].path, "%s", path);
    diffs[slot].delta = delta;
}

static void probe(void)
{
    char p[512];
    UP.n = 0;
    int64_t observed = (int64_t)cache_free - (int64_t)dev_free;  /* bytes used up since the last scan */
    int64_t acc = 0, tol = 16 * (int64_t)g_cluster;
    int walked = 0;
    ndiffs = 0;
    for (int i = 0; i < UO.n; i++) UO.u[i].seen = 0;

    /* A. Structure: list every folder the scan lists and compare with last time.
     *    New folders and changed apps are walked now; files are compared by size. */
    static const char *parents[] = {"ux0:app", "ux0:patch", "ux0:addcont", "ux0:data", "ux0:user/00/savedata",
                                    "ux0:pspemu/PSP/SAVEDATA", "ux0:pspemu/PSP/GAME", "ux0:pkgj", "ux0:downloads",
                                    "ux0:download", "ux0:VPKs", "ux0:", "ux0:pspemu/ISO"};
    for (unsigned k = 0; k < sizeof parents / sizeof parents[0]; k++) {
        int n;
        Ent *v = list_dir(parents[k], &n);
        int is_root = !strcmp(parents[k], "ux0:"), is_app = !strcmp(parents[k], "ux0:app");
        for (int i = 0; i < n; i++) {
            join(p, sizeof p, parents[k], v[i].name);
            Unit *o = ufind(&UO, p);
            if (o) o->seen = 1;
            if (v[i].dir) {
                if (is_root) continue; /* root folders are checked as units below */
                if (!strcmp(parents[k], "ux0:data") && !strcasecmp(v[i].name, "Storage")) continue;
                int changed = !o;
                if (!changed && is_app) {
                    Item *it = m_find_id(&UM, v[i].name, (1 << CAT_VITA) | (1 << CAT_HB));
                    if (it && it->installed && it->key && app_key(p) != it->key) changed = 1;
                }
                if (changed) {
                    Acc a = {0, 0, 0};
                    set_stage("Checking %s", v[i].name);
                    walk(p, &a);
                    walked++;
                    uadd(&UP, p, a.size, a.alloc, a.newest, 0);
                    acc += (int64_t)a.alloc - (int64_t)(o ? o->alloc : 0);
                    note_diff(p, (int64_t)a.alloc - (int64_t)(o ? o->alloc : 0));
                }
            } else if (!o || o->size != v[i].size) {
                uint64_t al = round_cl(v[i].size);
                uadd(&UP, p, v[i].size, al, 0, 1);
                acc += (int64_t)al - (int64_t)(o ? o->alloc : 0);
                note_diff(p, (int64_t)al - (int64_t)(o ? o->alloc : 0));
            }
        }
        free(v);
    }

    /* Units not under those folders (media, root folders, system files, ISOs in
     * sub-folders): check they still exist; loose files are re-measured by stat. */
    for (int i = 0; i < UO.n; i++) {
        Unit *u = &UO.u[i];
        if (u->seen) continue;
        SceIoStat st;
        if (sceIoGetstat(u->path, &st) < 0) { acc -= (int64_t)u->alloc; note_diff(u->path, -(int64_t)u->alloc); u->seen = 2; continue; }  /* gone */
        if (u->isfile) {
            u->seen = 1;
            if ((uint64_t)st.st_size != u->size) {
                uint64_t al = round_cl(st.st_size);
                uadd(&UP, u->path, st.st_size, al, 0, 1);
                acc += (int64_t)al - (int64_t)u->alloc;
                note_diff(u->path, (int64_t)al - (int64_t)u->alloc);
            }
        }
    }

    /* B. Walk the remaining folders, likeliest to have changed first, until
     *    the changes found add up to the change in free space. */
    Cand *c = malloc(sizeof(Cand) * (UO.n ? UO.n : 1));
    int nc = 0;
    for (int i = 0; i < UO.n; i++) {
        Unit *u = &UO.u[i];
        if (u->seen == 2 || u->isfile || ufind(&UP, u->path)) continue;
        int cls = unit_class(u->path);
        if (cls == 10) continue; /* apps are covered by their fingerprints; never re-walk them here */
        c[nc].idx = i; c[nc].cls = cls; c[nc].newest = u->newest; nc++;
    }
    qsort(c, nc, sizeof(Cand), cmp_cand);
    int saves = 0, data = 0;
    for (int k = 0; k < nc; k++) {                        /* only the most recent saves and data are "always" */
        if (c[k].cls == 80 && ++saves > 15) c[k].cls = 45;
        if (c[k].cls == 60 && ++data > 5) c[k].cls = 40;
    }
    qsort(c, nc, sizeof(Cand), cmp_cand);
    int matched = 0;
    for (int k = 0; k < nc; k++) {
        if (c[k].cls < 60 && llabs(observed - acc) <= tol) { matched = 1; break; }
        Unit *u = &UO.u[c[k].idx];
        Acc a = {0, 0, 0};
        const char *nm = strrchr(u->path, '/');
        set_stage("Checking %s", nm ? nm + 1 : u->path);
        walk(u->path, &a);
        walked++;
        uadd(&UP, u->path, a.size, a.alloc, a.newest, 0);
        note_diff(u->path, (int64_t)a.alloc - (int64_t)u->alloc);
        /* Media is always re-measured but not counted: the system's Photos
         * folders swing by several MB on paper without free space moving. */
        if (c[k].cls != 90) acc += (int64_t)a.alloc - (int64_t)u->alloc;
    }
    if (!matched && llabs(observed - acc) <= tol) matched = 1;
    free(c);
    int l = snprintf(probe_log, sizeof probe_log, "probe: walked %d folders; cluster %u KB; free space changed %+lld KB, found %+lld KB; %s\n",
                     walked, (unsigned)(g_cluster / 1024), (long long)(observed / 1024), (long long)(acc / 1024),
                     matched ? "matched, the rest trusted" : "no match, all but apps re-measured");
    for (int i = 0; i < ndiffs && l < (int)sizeof probe_log - 140; i++)
        l += snprintf(probe_log + l, sizeof probe_log - l, "  %+9lld KB  %s\n", (long long)(diffs[i].delta / 1024), diffs[i].path);
}

static void compute_totals_m(Model *m)
{
    memset(cat_total, 0, sizeof cat_total);
    memset(cat_count, 0, sizeof cat_count);
    for (int i = 0; i < m->n; i++) {
        Item *it = &m->it[i];
        if (it->cat == CAT_VITA) it->size = it->part[P_APP] + it->part[P_UPD] + it->part[P_DLC];
        else if (it->cat == CAT_HB) it->size = it->part[P_APP] + it->part[P_DATA];
        else if (it->cat == CAT_PSP || it->cat == CAT_PS1) it->size = it->part[P_APP] + it->part[P_BUB];
        cat_total[it->cat] += it->size;
        cat_count[it->cat]++;
    }
    uint64_t used = dev_max - dev_free, known = 0;
    for (int c = 0; c < CAT_OTHER; c++) known += cat_total[c];
    cat_total[CAT_OTHER] = used > known ? used - known : 0;
}

typedef struct { SceOff max_size; SceOff free_size; SceSize cluster_size; void *unk; } DevInfo;

static void query_space(void)
{
    DevInfo info;
    memset(&info, 0, sizeof info);
    if (sceIoDevctl("ux0:", 0x3001, NULL, 0, &info, sizeof info) >= 0) {
        dev_max = (uint64_t)info.max_size;
        dev_free = (uint64_t)info.free_size;
        if (info.cluster_size >= 512 && info.cluster_size <= (1u << 22)) g_cluster = info.cluster_size;
    }
}

/* Per-stage timing, written to ux0:data/Storage/scan.log after each scan. */
static char scan_log[4096];

/* Appends to scan.log, starting it over once it grows past 24 KB. */
static void append_log(const char *text, int len)
{
    const char *path = "ux0:data/Storage/scan.log";
    SceIoStat st;
    int flags = SCE_O_WRONLY | SCE_O_CREAT | SCE_O_APPEND;
    if (sceIoGetstat(path, &st) >= 0 && st.st_size > 24 * 1024) flags = SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC;
    sceIoMkdir("ux0:data/Storage", 0777);
    SceUID f = sceIoOpen(path, flags, 0777);
    if (f < 0) return;
    SceDateTime now;
    sceRtcGetCurrentClockLocalTime(&now);
    char head[64];
    int hl = snprintf(head, sizeof head, "==== %04d-%02d-%02d %02d:%02d\n", now.year, now.month, now.day, now.hour, now.minute);
    sceIoWrite(f, head, hl);
    sceIoWrite(f, text, len);
    sceIoClose(f);
}
static int scan_log_len;
static uint64_t t_stage;
static int f_stage;

static void timed(const char *name)
{
    uint64_t now = sceKernelGetProcessTimeWide();
    if (name && scan_log_len < (int)sizeof scan_log - 100)
        scan_log_len += snprintf(scan_log + scan_log_len, sizeof scan_log - scan_log_len,
                                 "%-14s %7.2f s  %7d files\n", name, (now - t_stage) / 1e6, g_files - f_stage);
    t_stage = now;
    f_stage = g_files;
}

/* Nothing changed if free space is identical to the byte and every cached app
 * still has the same fingerprint (and no app folder was added or removed). */
static int quick_check(void)
{
    query_space();
    if (!have_cache || dev_free != cache_free) return 0;
    int n, dirs = 0;
    Ent *v = list_dir("ux0:app", &n);
    for (int i = 0; i < n; i++) if (v[i].dir) dirs++;
    free(v);
    if ((uint32_t)dirs != um_app_dirs) return 0;
    for (int i = 0; i < UM.n; i++)
        if (UM.it[i].installed && UM.it[i].key && app_key(UM.it[i].path) != UM.it[i].key) return 0;

    /* Games often rewrite a save at the same size, which leaves free space
     * untouched. Saves are small, so check them directly: any change in size
     * or newest date means a real refresh (that's where "Last played" comes from). */
    static const char *save_roots[] = {"ux0:user/00/savedata", "ux0:pspemu/PSP/SAVEDATA"};
    char p[512];
    for (int r = 0; r < 2; r++) {
        v = list_dir(save_roots[r], &n);
        for (int i = 0; i < n; i++) {
            if (!v[i].dir) continue;
            join(p, sizeof p, save_roots[r], v[i].name);
            Unit *u = ufind(&UO, p);
            Acc a = {0, 0, 0};
            walk(p, &a);
            if (!u || u->size != a.size || u->newest != a.newest) { free(v); return 0; }
        }
        free(v);
    }
    return 1;
}

/* One-time check of how this card's file system dates folders, to decide
 * whether unchanged folders can be skipped. Results go to diag.log. */
static void mtime_diag(void)
{
    const char *dir = "ux0:data/Storage/mtime_test", *file = "ux0:data/Storage/mtime_test/f.bin";
    char out[1024];
    int l = 0;
    SceIoStat s0, s1, s2, s3, f1, f2;
    uint8_t buf[4096];
    memset(buf, 0x5A, sizeof buf);
    sceIoRemove(file);
    sceIoRmdir(dir);
    sceIoMkdir("ux0:data/Storage", 0777);
    if (sceIoMkdir(dir, 0777) < 0) return;
    sceIoGetstat(dir, &s0);
    sceKernelDelayThread(2100000);
    SceUID f = sceIoOpen(file, SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC, 0777);
    if (f >= 0) { sceIoWrite(f, buf, sizeof buf); sceIoClose(f); }
    sceIoGetstat(dir, &s1);
    sceIoGetstat(file, &f1);
    sceKernelDelayThread(2100000);
    f = sceIoOpen(file, SCE_O_WRONLY | SCE_O_APPEND, 0777);          /* grow an existing file */
    if (f >= 0) { for (int i = 0; i < 16; i++) sceIoWrite(f, buf, sizeof buf); sceIoClose(f); }
    sceIoGetstat(dir, &s2);
    sceIoGetstat(file, &f2);
    sceKernelDelayThread(2100000);
    sceIoRemove(file);                                                  /* remove a file */
    sceIoGetstat(dir, &s3);
    sceIoRmdir(dir);
    l += snprintf(out + l, sizeof out - l, "dir mtime changes when a file is created: %s\n", dt_key(&s1.st_mtime) != dt_key(&s0.st_mtime) ? "YES" : "no");
    l += snprintf(out + l, sizeof out - l, "dir mtime changes when a file grows:      %s\n", dt_key(&s2.st_mtime) != dt_key(&s1.st_mtime) ? "YES" : "no");
    l += snprintf(out + l, sizeof out - l, "dir mtime changes when a file is removed: %s\n", dt_key(&s3.st_mtime) != dt_key(&s2.st_mtime) ? "YES" : "no");
    l += snprintf(out + l, sizeof out - l, "file mtime changes when it grows:         %s\n", dt_key(&f2.st_mtime) != dt_key(&f1.st_mtime) ? "YES" : "no");
    l += snprintf(out + l, sizeof out - l, "raw dir mtimes: %04d-%02d-%02d %02d:%02d:%02d.%06u / %02d:%02d:%02d.%06u / %02d:%02d:%02d.%06u / %02d:%02d:%02d.%06u\n",
                  s0.st_mtime.year, s0.st_mtime.month, s0.st_mtime.day, s0.st_mtime.hour, s0.st_mtime.minute, s0.st_mtime.second, (unsigned)s0.st_mtime.microsecond,
                  s1.st_mtime.hour, s1.st_mtime.minute, s1.st_mtime.second, (unsigned)s1.st_mtime.microsecond,
                  s2.st_mtime.hour, s2.st_mtime.minute, s2.st_mtime.second, (unsigned)s2.st_mtime.microsecond,
                  s3.st_mtime.hour, s3.st_mtime.minute, s3.st_mtime.second, (unsigned)s3.st_mtime.microsecond);
    SceUID lg = sceIoOpen("ux0:data/Storage/diag.log", SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC, 0777);
    if (lg >= 0) { sceIoWrite(lg, out, l); sceIoClose(lg); }
}

static int scan_thread(SceSize args, void *argp)
{
    (void)args; (void)argp;
    uint64_t t0 = sceKernelGetProcessTimeWide();
    g_quick = 0;
    if (!g_full && have_cache) {
        g_checking = 1;
        set_stage("Checking for changes");
        int same = quick_check();
        g_checking = 0;
        if (same) {
            char line[96];
            int l = snprintf(line, sizeof line, "quick check: free space identical, up to date (%.2f s)\n",
                             (sceKernelGetProcessTimeWide() - t0) / 1e6);
            append_log(line, l); /* before the cache header records free space */
            g_quick = 1;
            g_scan_done = 1;
            sceKernelExitDeleteThread(0);
            return 0;
        }
    }
    if (!path_exists("ux0:data/Storage/diag.log")) mtime_diag();
    scan_log_len = 0;
    timed(NULL);
    query_space();
    UN.n = 0;
    UP.n = 0;
    probe_log[0] = 0;
    incremental = !g_full && have_cache && UO.n > 0;
    if (incremental) {
        set_stage("Finding what changed");
        probe();                                      timed("probe");
    }
    scan_apps();                                      timed("apps");
    scan_addons("ux0:patch", P_UPD, "Game updates");  timed("updates");
    scan_addons("ux0:addcont", P_DLC, "DLC");         timed("dlc");
    scan_data();                                      timed("data");
    scan_psp_isos("ux0:pspemu/ISO");                  timed("psp isos");
    scan_psp_game();                                  timed("psp/ps1 game");
    set_stage("Matching bubbles to games");
    link_bubbles();                                   timed("bubbles");
    scan_saves();                                     timed("saves");
    scan_media();                                     timed("media");
    scan_extras();                                    timed("extras");
    scan_other();                                     timed("system files");
    if (scan_log_len < (int)sizeof scan_log - 320)
        scan_log_len += snprintf(scan_log + scan_log_len, sizeof scan_log - scan_log_len, "%s%s",
                                 incremental ? probe_log : "full scan\n", "");
    {
        if (scan_log_len < (int)sizeof scan_log - 80)
            scan_log_len += snprintf(scan_log + scan_log_len, sizeof scan_log - scan_log_len, "TOTAL          %7.2f s  %7d files\n",
                                     (sceKernelGetProcessTimeWide() - t0) / 1e6, g_files);
        append_log(scan_log, scan_log_len);
    }
    g_scan_done = 1;
    sceKernelExitDeleteThread(0);
    return 0;
}

/* ------------------------------------------------------------- deleting */

/* Recursive delete; adds each removed file's size to job_bytes for the progress bar. */
static int rm_rf(const char *path)
{
    SceIoStat st;
    if (sceIoGetstat(path, &st) < 0) return 0;
    if (!SCE_S_ISDIR(st.st_mode)) {
        int ok = sceIoRemove(path) >= 0;
        if (ok) job_bytes += st.st_size;
        return ok;
    }
    SceUID d = sceIoDopen(path);
    if (d >= 0) {
        SceIoDirent e;
        char sub[1024];
        for (;;) {
            memset(&e, 0, sizeof e);
            if (sceIoDread(d, &e) <= 0) break;
            if (!strcmp(e.d_name, ".") || !strcmp(e.d_name, "..")) continue;
            join(sub, sizeof sub, path, e.d_name);
            if (SCE_S_ISDIR(e.d_stat.st_mode)) rm_rf(sub);
            else if (sceIoRemove(sub) >= 0) job_bytes += e.d_stat.st_size;
        }
        sceIoDclose(d);
    }
    return sceIoRmdir(path) >= 0;
}

static int rm_prefix(const char *dir, const char *prefix)
{
    int n, ok = 1;
    char p[512];
    Ent *v = list_dir(dir, &n);
    for (int i = 0; i < n; i++)
        if (v[i].dir && strncmp(v[i].name, prefix, strlen(prefix)) == 0) {
            join(p, sizeof p, dir, v[i].name);
            ok &= rm_rf(p);
        }
    free(v);
    return ok;
}

static int uninstall_app(const char *id)
{
    char p[64];
    int res = scePromoterUtilityDeletePkg(id);
    if (res < 0) return res;
    snprintf(p, sizeof p, "ux0:app/%s", id);
    if (path_exists(p)) rm_rf(p);
    return 0;
}

/* From here on, code works on what the UI shows. */
#undef items
#undef nitems
#undef bubbles
#undef nbubbles
#undef new_item
#undef find_id
#undef add_extra
#undef add_orphan_bubble
#define items (UM.it)
#define nitems (UM.n)
#define new_item(c) m_new_item(&UM, c)
#define find_id(i, m) m_find_id(&UM, i, m)
#define add_extra(p, n, no, s) m_add_extra(&UM, p, n, no, s)
#define add_orphan_bubble(i, t, s) m_add_orphan_bubble(&UM, i, t, s)
#define compute_totals() compute_totals_m(&UM)

/* ------------------------------------------------------------------ cache */

#define CACHE_PATH "ux0:data/Storage/cache.bin"
typedef struct {
    char magic[8];
    uint32_t item_size, bubble_size, n, nb;
    int day, hour, minute;
    uint64_t dev_max;
    uint64_t dev_free;   /* measured after the cache file itself was written */
    uint32_t app_dirs;
    uint32_t unit_size, nunits;
} CacheHdr;

/* Rewrites just the header in place (same size, so free space doesn't move). */
static void patch_cache_header(int stamp_now)
{
    CacheHdr h;
    SceUID f = sceIoOpen(CACHE_PATH, SCE_O_RDWR, 0);
    if (f < 0) return;
    if (sceIoRead(f, &h, sizeof h) == (int)sizeof h) {
        if (stamp_now) {
            SceDateTime now;
            sceRtcGetCurrentClockLocalTime(&now);
            h.day = dt_day(&now); h.hour = now.hour; h.minute = now.minute;
            cache_day = h.day; cache_hour = h.hour; cache_min = h.minute;
        }
        query_space();
        h.dev_free = dev_free;
        cache_free = dev_free;
        sceIoLseek(f, 0, SCE_SEEK_SET);
        sceIoWrite(f, &h, sizeof h);
    }
    sceIoClose(f);
}

static void write_cache(void)
{
    SceDateTime now;
    sceRtcGetCurrentClockLocalTime(&now);
    CacheHdr h;
    memset(&h, 0, sizeof h);
    memcpy(h.magic, "VSMCACH2", 8);
    h.unit_size = sizeof(Unit);
    h.nunits = UO.n;
    h.item_size = sizeof(Item);
    h.bubble_size = sizeof(Bubble);
    h.n = UM.n;
    h.nb = UM.nb;
    h.day = dt_day(&now); h.hour = now.hour; h.minute = now.minute;
    h.dev_max = dev_max;
    h.app_dirs = um_app_dirs;
    sceIoMkdir("ux0:data/Storage", 0777);
    SceUID f = sceIoOpen(CACHE_PATH ".tmp", SCE_O_WRONLY | SCE_O_CREAT | SCE_O_TRUNC, 0777);
    if (f < 0) return;
    int ok = sceIoWrite(f, &h, sizeof h) == (int)sizeof h;
    if (ok && UM.n) ok = sceIoWrite(f, UM.it, sizeof(Item) * UM.n) == (int)(sizeof(Item) * UM.n);
    if (ok && UM.nb) ok = sceIoWrite(f, UM.bub, sizeof(Bubble) * UM.nb) == (int)(sizeof(Bubble) * UM.nb);
    if (ok && UO.n) ok = sceIoWrite(f, UO.u, sizeof(Unit) * UO.n) == (int)(sizeof(Unit) * UO.n);
    sceIoClose(f);
    if (!ok) { sceIoRemove(CACHE_PATH ".tmp"); return; }
    sceIoRemove(CACHE_PATH);
    sceIoRename(CACHE_PATH ".tmp", CACHE_PATH);
    cache_day = h.day; cache_hour = h.hour; cache_min = h.minute;
    have_cache = 1;
    patch_cache_header(0); /* record free space now that every file is written */
}

static int load_cache(void)
{
    CacheHdr h;
    SceUID f = sceIoOpen(CACHE_PATH, SCE_O_RDONLY, 0);
    if (f < 0) return 0;
    int ok = sceIoRead(f, &h, sizeof h) == (int)sizeof h && !memcmp(h.magic, "VSMCACH2", 8) &&
             h.item_size == sizeof(Item) && h.bubble_size == sizeof(Bubble) && h.unit_size == sizeof(Unit) &&
             h.n <= MAX_ITEMS && h.nb <= MAX_BUBBLES && h.nunits <= MAX_UNITS;
    if (ok && h.n) ok = sceIoRead(f, UM.it, sizeof(Item) * h.n) == (int)(sizeof(Item) * h.n);
    if (ok && h.nb) ok = sceIoRead(f, UM.bub, sizeof(Bubble) * h.nb) == (int)(sizeof(Bubble) * h.nb);
    if (ok && h.nunits) ok = sceIoRead(f, UO.u, sizeof(Unit) * h.nunits) == (int)(sizeof(Unit) * h.nunits);
    sceIoClose(f);
    if (!ok) { UM.n = UM.nb = 0; UO.n = 0; return 0; }
    UO.n = h.nunits;
    UM.n = h.n;
    UM.nb = h.nb;
    cache_free = h.dev_free;
    um_app_dirs = h.app_dirs;
    for (int i = 0; i < UM.n; i++) { UM.it[i].icon = NULL; UM.it[i].icon_state = 0; }
    cache_day = h.day; cache_hour = h.hour; cache_min = h.minute;
    have_cache = 1;
    return 1;
}

/* --------------------------------------------------------------- drawing */

static vita2d_pgf *font;
static vita2d_texture *logo;
static uint64_t frame;

#define RGB(c, a) RGBA8(((c) >> 16) & 255, ((c) >> 8) & 255, (c) & 255, (a))
#define C_TEXT   RGBA8(236, 241, 250, 255)
#define C_DIM    RGBA8(140, 152, 176, 255)
#define C_FAINT  RGBA8(84, 96, 122, 255)
#define C_CARD   RGBA8(24, 32, 52, 255)
#define C_SEL    RGBA8(34, 48, 80, 255)
#define C_LINE   RGBA8(40, 52, 78, 255)
#define C_ACCENT RGBA8(96, 165, 250, 255)
#define C_WARN   RGBA8(253, 186, 116, 255)

/* The system font (latin PGF) only covers ASCII and Latin-1. When vita2d's
 * PGF renderer meets a character the font lacks, adding it to the glyph cache
 * can write past the cache texture: in video memory that corrupted GPU data
 * and crashed, in main memory it showed as diagonal streaks. Everything drawn
 * goes through this first: common typographic characters become ASCII, any
 * other character beyond Latin-1 becomes '?', and broken UTF-8 is dropped. */
static const char *safe_text(const char *in, char *out, int n)
{
    int j = 0;
    const unsigned char *s = (const unsigned char *)in;
    while (*s && j < n - 4) {
        unsigned cp, len;
        if (s[0] < 0x80) { cp = s[0]; len = 1; }
        else if ((s[0] & 0xE0) == 0xC0 && (s[1] & 0xC0) == 0x80) { cp = ((s[0] & 0x1F) << 6) | (s[1] & 0x3F); len = 2; }
        else if ((s[0] & 0xF0) == 0xE0 && (s[1] & 0xC0) == 0x80 && (s[2] & 0xC0) == 0x80) {
            cp = ((s[0] & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F); len = 3;
        } else if ((s[0] & 0xF8) == 0xF0 && (s[1] & 0xC0) == 0x80 && (s[2] & 0xC0) == 0x80 && (s[3] & 0xC0) == 0x80) {
            cp = 0x10000; len = 4;
        } else { s++; continue; }                       /* broken byte: drop it */
        s += len;
        const char *rep = NULL;
        switch (cp) {
        case 0x2018: case 0x2019: case 0x201A: case 0x2032: rep = "'"; break;
        case 0x201C: case 0x201D: case 0x201E: case 0x2033: rep = "\""; break;
        case 0x2026: rep = "..."; break;
        case 0x2010: case 0x2011: case 0x2012: case 0x2013: case 0x2014: case 0x2015: case 0x2212: rep = "-"; break;
        case 0x2122: case 0x00AE: case 0x00A9: rep = ""; break;   /* (TM) (R) (C) */
        case 0x00A0: case 0x3000: rep = " "; break;
        }
        if (rep) { while (*rep && j < n - 1) out[j++] = *rep++; continue; }
        if (cp < 0x20) continue;                         /* control characters */
        if (cp < 0x80) { out[j++] = (char)cp; continue; }
        if (cp <= 0xFF) { out[j++] = (char)(0xC0 | (cp >> 6)); out[j++] = (char)(0x80 | (cp & 0x3F)); continue; }
        out[j++] = '?';
    }
    out[j] = 0;
    return out;
}

static void text(int x, int y, float s, unsigned c, const char *t)
{
    char buf[512];
    vita2d_pgf_draw_text(font, x, y, c, s, safe_text(t, buf, sizeof buf));
}
static int text_w(float s, const char *t)
{
    char buf[512];
    return vita2d_pgf_text_width(font, s, safe_text(t, buf, sizeof buf));
}
static void text_r(int xr, int y, float s, unsigned c, const char *t) { text(xr - text_w(s, t), y, s, c, t); }
static void text_c(int cx, int y, float s, unsigned c, const char *t) { text(cx - text_w(s, t) / 2, y, s, c, t); }

static void text_fit(int x, int y, float s, unsigned c, const char *t, int maxw)
{
    if (text_w(s, t) <= maxw) { text(x, y, s, c, t); return; }
    char buf[400];
    int n = snprintf(buf, sizeof buf - 4, "%s", t);
    if (n > (int)sizeof buf - 5) n = sizeof buf - 5;
    while (n > 0) {
        n--;
        while (n > 0 && ((unsigned char)buf[n] & 0xC0) == 0x80) n--;
        buf[n] = 0;
        char tmp[404];
        snprintf(tmp, sizeof tmp, "%s...", buf);
        if (text_w(s, tmp) <= maxw) { text(x, y, s, c, tmp); return; }
    }
}

static void rrect(int x, int y, int w, int h, int r, unsigned c)
{
    if (r * 2 > h) r = h / 2;
    if (r * 2 > w) r = w / 2;
    vita2d_draw_rectangle(x + r, y, w - 2 * r, h, c);
    vita2d_draw_rectangle(x, y + r, r, h - 2 * r, c);
    vita2d_draw_rectangle(x + w - r, y + r, r, h - 2 * r, c);
    vita2d_draw_fill_circle(x + r, y + r, r, c);
    vita2d_draw_fill_circle(x + w - r - 1, y + r, r, c);
    vita2d_draw_fill_circle(x + r, y + h - r - 1, r, c);
    vita2d_draw_fill_circle(x + w - r - 1, y + h - r - 1, r, c);
}

static void background(void)
{
    for (int y = 0; y < SCREEN_H; y += 8) {
        float t = (float)y / SCREEN_H;
        vita2d_draw_rectangle(0, y, SCREEN_W, 8, RGBA8((int)(16 - 8 * t), (int)(22 - 11 * t), (int)(38 - 18 * t), 255));
    }
}

/* The ring logo, spinning; falls back to a ring of dots. */
static void spinner(int cx, int cy, int size)
{
    if (logo) {
        float s = (float)size / vita2d_texture_get_width(logo);
        vita2d_draw_texture_scale_rotate(logo, cx, cy, s, s, (float)frame * 0.045f);
        return;
    }
    int phase = (int)(frame / 4) % 12;
    for (int i = 0; i < 12; i++) {
        float a = (float)i / 12.0f * 6.2832f;
        int d = (i - phase + 12) % 12;
        vita2d_draw_fill_circle(cx + cosf(a) * size * 0.4f, cy + sinf(a) * size * 0.4f, size / 14 + 1,
                                RGBA8(96, 165, 250, 255 - d * 18));
    }
}

/* Progress bar; indeterminate when frac < 0 (a sliding highlight). */
static void progress(int x, int y, int w, int h, float frac)
{
    rrect(x, y, w, h, h / 2, C_CARD);
    if (frac < 0) {
        int seg = w / 4;
        int pos = (int)(frame * 6) % (w + seg) - seg;
        int x0 = pos < 0 ? 0 : pos, x1 = pos + seg > w ? w : pos + seg;
        if (x1 - x0 > h) rrect(x + x0, y, x1 - x0, h, h / 2, C_ACCENT);
        return;
    }
    if (frac > 1) frac = 1;
    int fw = (int)(w * frac);
    if (fw >= h) rrect(x, y, fw, h, h / 2, C_ACCENT);
}

enum { B_CROSS, B_CIRCLE, B_SQUARE, B_TRIANGLE, B_START, B_LR };

/* Draws a button glyph plus label, ending at xr; returns the new right edge. */
static int hint(int xr, int y, int btn, const char *label)
{
    /* callers pass B_CROSS for "confirm" and B_CIRCLE for "back" */
    if (swap_ok && btn == B_CROSS) btn = B_CIRCLE;
    else if (swap_ok && btn == B_CIRCLE) btn = B_CROSS;
    int lw = text_w(0.85f, label);
    int x = xr - lw;
    text(x, y, 0.85f, C_DIM, label);
    if (btn == B_START || btn == B_LR) {
        const char *s = btn == B_START ? "START" : "L / R";
        int w = text_w(0.6f, s) + 14;
        x -= w + 8;
        rrect(x, y - 15, w, 20, 10, RGBA8(52, 64, 92, 255));
        text(x + 7, y, 0.6f, C_TEXT, s);
        return x - 22;
    }
    int cx = x - 16, cy = y - 6, r = 11;
    vita2d_draw_fill_circle(cx, cy, r, RGBA8(52, 64, 92, 255));
    if (btn == B_CROSS) {
        unsigned c = RGBA8(125, 170, 255, 255);
        for (int o = -1; o <= 0; o++) {
            vita2d_draw_line(cx - 5 + o, cy - 5, cx + 5 + o, cy + 5, c);
            vita2d_draw_line(cx + 5 + o, cy - 5, cx - 5 + o, cy + 5, c);
        }
    } else if (btn == B_CIRCLE) {
        vita2d_draw_fill_circle(cx, cy, 6, RGBA8(255, 105, 115, 255));
        vita2d_draw_fill_circle(cx, cy, 4, RGBA8(52, 64, 92, 255));
    } else if (btn == B_SQUARE) {
        unsigned c = RGBA8(240, 130, 210, 255);
        vita2d_draw_rectangle(cx - 5, cy - 5, 11, 2, c);
        vita2d_draw_rectangle(cx - 5, cy + 4, 11, 2, c);
        vita2d_draw_rectangle(cx - 5, cy - 5, 2, 11, c);
        vita2d_draw_rectangle(cx + 4, cy - 5, 2, 11, c);
    } else if (btn == B_TRIANGLE) {
        unsigned c = RGBA8(80, 220, 170, 255);
        for (int o = 0; o < 2; o++) {
            vita2d_draw_line(cx, cy - 6 + o, cx - 6 + o, cy + 4, c);
            vita2d_draw_line(cx, cy - 6 + o, cx + 6 - o, cy + 4, c);
            vita2d_draw_line(cx - 6, cy + 4 - o, cx + 6, cy + 4 - o, c);
        }
    }
    return cx - r - 22;
}

static void chevron(int x, int y, unsigned c)
{
    for (int o = 0; o < 2; o++) {
        vita2d_draw_line(x + o, y - 6, x + 6 + o, y, c);
        vita2d_draw_line(x + 6 + o, y, x + o, y + 6, c);
    }
}

static void footer_line(void) { vita2d_draw_rectangle(30, 506, SCREEN_W - 60, 1, C_LINE); }

/* ------------------------------------------------------------------ icons */

/* Debug log for tracking down GPU crashes: every line is written and closed
 * immediately so it survives the app being killed. Built only with -DDEBUG_LOG. */
#ifdef DEBUG_LOG
static void dlog(const char *fmt, ...)
{
    char line[400];
    va_list ap;
    va_start(ap, fmt);
    int l = vsnprintf(line, sizeof line - 2, fmt, ap);
    va_end(ap);
    if (l < 0) return;
    if (l > (int)sizeof line - 2) l = sizeof line - 2;
    line[l++] = '\n';
    SceUID f = sceIoOpen("ux0:data/Storage/debug.log", SCE_O_WRONLY | SCE_O_CREAT | SCE_O_APPEND, 0777);
    if (f >= 0) { sceIoWrite(f, line, l); sceIoClose(f); }
}
#else
#define dlog(...) ((void)0)
#endif

/* Decodes any PNG (interlaced, palette, grey, 16-bit, with or without alpha)
 * with libpng's simplified API and copies it row by row into a texture.
 * vita2d's own loader is avoided: some PSP ICON0.PNGs are interlaced, and a
 * bad decode there is the prime suspect for the GPU crashes. */
static vita2d_texture *png_to_texture(const uint8_t *data, uint32_t len)
{
    if (!data || len < 8 || memcmp(data, "\x89PNG", 4)) return NULL;
    png_image img;
    memset(&img, 0, sizeof img);
    img.version = PNG_IMAGE_VERSION;
    if (!png_image_begin_read_from_memory(&img, data, len)) return NULL;
    if (img.width == 0 || img.height == 0 || img.width > 512 || img.height > 512) { png_image_free(&img); return NULL; }
    img.format = PNG_FORMAT_RGBA;
    uint32_t w = img.width, h = img.height;
    uint8_t *px = malloc(PNG_IMAGE_SIZE(img));
    if (!px) { png_image_free(&img); return NULL; }
    if (!png_image_finish_read(&img, NULL, px, 0, NULL)) { free(px); png_image_free(&img); return NULL; }
    dlog("  decoded %ux%u, creating texture", (unsigned)w, (unsigned)h);
    vita2d_texture *t = vita2d_create_empty_texture(w, h);   /* A8B8G8R8: R,G,B,A bytes in memory */
    if (t) {
        uint8_t *dst = vita2d_texture_get_datap(t);
        unsigned stride = vita2d_texture_get_stride(t);
        dlog("  texture %p data %p stride %u", (void *)t, (void *)dst, stride);
        if (!dst || stride < w * 4) { vita2d_free_texture(t); t = NULL; }
        else for (uint32_t y = 0; y < h; y++) memcpy(dst + y * stride, px + y * w * 4, w * 4);
    } else dlog("  texture allocation FAILED");
    free(px);
    return t;
}

static vita2d_texture *png_file_to_texture(const char *path)
{
    uint32_t len = 0;
    uint8_t *buf = read_file(path, 1 << 20, &len);
    vita2d_texture *t = png_to_texture(buf, len);
    free(buf);
    return t;
}

static void load_icon(Item *it)
{
    dlog("icon kind=%d loaded=%d src=%s", it->icon_kind, icons_loaded, it->icon_src);
    it->icon_state = 2;
    uint8_t *buf = NULL;
    uint32_t len = 0;
    vita2d_texture *t = NULL;
    switch (it->icon_kind) {
    case ICON_FILE: {
        /* Retail Vita games are encrypted in ux0:app (and in ux0:appmeta), so
         * their icon is read only from the plain copy the system keeps in
         * ur0:appmeta. The encrypted files are never opened. */
        char id[32] = {0}, p[96];
        int retail = 0;
        if (!strncmp(it->icon_src, "ux0:app/", 8)) {
            snprintf(id, sizeof id, "%s", it->icon_src + 8);
            char *slash = strchr(id, '/');
            if (slash) *slash = 0;
            retail = is_vita_retail_id(id);
        }
        if (!retail) {
            dlog("  read %s", it->icon_src);
            t = png_file_to_texture(it->icon_src);
        }
        if (!t && id[0]) {
            snprintf(p, sizeof p, "ur0:appmeta/%s/icon0.png", id);
            dlog("  read %s", p);
            t = png_file_to_texture(p);
        }
        break;
    }
    case ICON_ISO:  buf = iso_read_file(it->icon_src, 0, "PSP_GAME", "ICON0.PNG", 1 << 20, &len); break;
    case ICON_CSO:  buf = iso_read_file(it->icon_src, 1, "PSP_GAME", "ICON0.PNG", 1 << 20, &len); break;
    case ICON_PBP:  buf = pbp_section(it->icon_src, 1, &len); break;
    default: return;
    }
    if (buf) {
        t = png_to_texture(buf, len);
        free(buf);
    }
    if (t) {
        vita2d_texture_set_filters(t, SCE_GXM_TEXTURE_FILTER_LINEAR, SCE_GXM_TEXTURE_FILTER_LINEAR);
        it->icon = t;
        it->icon_state = 1;
        icons_loaded++;
    }
    dlog("  -> %s", t ? "ok" : "no icon");
}

static int icon_budget;

/* Frees icons that aren't on screen once too many are loaded. Runs between
 * frames, after the GPU has finished with the last one. */
static void evict_icons(int list_top_, int rows, const int *idx, int n, int keep)
{
    if (icons_loaded <= MAX_ICONS) return;
    dlog("evicting: %d loaded", icons_loaded);
    vita2d_wait_rendering_done();
    for (int i = 0; i < nitems && icons_loaded > MAX_ICONS * 3 / 4; i++) {
        Item *it = &items[i];
        if (!it->icon || i == keep) continue;
        int visible = 0;
        for (int r = list_top_; r < list_top_ + rows && r < n; r++) if (idx[r] == i) { visible = 1; break; }
        if (visible) continue;
        vita2d_free_texture(it->icon);
        it->icon = NULL;
        it->icon_state = 0;   /* reload when it scrolls back into view */
        icons_loaded--;
    }
}

static void draw_icon(Item *it, int x, int y, int w, int h)
{
    if (it->icon_state == 0 && icon_budget > 0) { icon_budget--; load_icon(it); }
    if (it->icon) {
        float tw = vita2d_texture_get_width(it->icon), th = vita2d_texture_get_height(it->icon);
        float s = (float)w / tw < (float)h / th ? (float)w / tw : (float)h / th;
        rrect(x, y, w, h, 8, RGBA8(14, 18, 30, 255));
        vita2d_draw_texture_scale(it->icon, x + (w - tw * s) / 2, y + (h - th * s) / 2, s, s);
        return;
    }
    unsigned c = cat_rgb[it->cat];
    rrect(x, y, w, h, 10, RGB(c, 70));
    char ch[8] = {0};
    const unsigned char *n = (const unsigned char *)it->name;
    if (!strncmp(it->name, "Bubble: ", 8)) n += 8;
    while (*n && !isalnum(*n)) n++;
    ch[0] = *n ? (char)toupper(*n) : '?';
    float s = h >= 100 ? 2.6f : 1.3f;
    text(x + (w - text_w(s, ch)) / 2, y + h / 2 + (int)(8 * s), s, RGB(c, 255), ch);
}

/* ----------------------------------------------------------------- input */

static uint32_t btn_now, btn_prev;
static uint64_t rep_t0[32], rep_last[32];

static uint32_t poll_input(void)
{
    SceCtrlData pad;
    memset(&pad, 0, sizeof pad);
    sceCtrlPeekBufferPositive(0, &pad, 1);
    uint32_t b = pad.buttons;
    if (b & SCE_CTRL_L1) b |= SCE_CTRL_LTRIGGER;
    if (b & SCE_CTRL_R1) b |= SCE_CTRL_RTRIGGER;
    if (pad.ly < 50) b |= SCE_CTRL_UP;
    if (pad.ly > 205) b |= SCE_CTRL_DOWN;
    btn_prev = btn_now;
    btn_now = b;
    uint32_t out = b & ~btn_prev;
    uint64_t t = sceKernelGetProcessTimeWide();
    const uint32_t rep = SCE_CTRL_UP | SCE_CTRL_DOWN | SCE_CTRL_LTRIGGER | SCE_CTRL_RTRIGGER;
    for (int i = 0; i < 32; i++) {
        uint32_t m = 1u << i;
        if (!(rep & m)) continue;
        if (out & m) { rep_t0[i] = t; rep_last[i] = t; }
        else if ((b & m) && t - rep_t0[i] > 380000 && t - rep_last[i] > 65000) { out |= m; rep_last[i] = t; }
    }
    return out;
}

/* -------------------------------------------------------------- screens */

enum { SCR_SCAN, SCR_HOME, SCR_LIST, SCR_DETAIL };
enum { SORT_SIZE, SORT_NAME, SORT_PLAYED, NSORT };
static const char *sort_name[NSORT] = {"Size", "Name", "Last played"};

static int scr = SCR_SCAN, home_sel, cur_cat, list_sel, list_top, sort_mode, confirm, detail_idx;
static int list_idx[MAX_ITEMS], list_n;
static char toast[200];
static uint64_t toast_until;

static int cmp_items(const void *a, const void *b)
{
    const Item *x = &items[*(const int *)a], *y = &items[*(const int *)b];
    if (sort_mode == SORT_NAME) return strcasecmp(x->name, y->name);
    if (sort_mode == SORT_PLAYED && x->last_day != y->last_day) return y->last_day - x->last_day;
    if (x->size != y->size) return y->size > x->size ? 1 : -1;
    return strcasecmp(x->name, y->name);
}

static void build_list(void)
{
    list_n = 0;
    for (int i = 0; i < nitems; i++) if (items[i].cat == cur_cat) list_idx[list_n++] = i;
    qsort(list_idx, list_n, sizeof(int), cmp_items);
    if (list_sel >= list_n) list_sel = list_n ? list_n - 1 : 0;
}

static void show_toast(const char *msg)
{
    snprintf(toast, sizeof toast, "%s", msg);
    toast_until = sceKernelGetProcessTimeWide() + 3500000;
}

/* Scans into SM in the background. With a cache loaded the UI keeps showing it
 * (deletes wait) and swaps in the fresh results when the scan is done. */
static void start_scan(int full)
{
    if (scanning) return;
    g_full = full;
    SM.n = 0;
    SM.nb = 0;
    g_scan_done = 0;
    g_scanned_bytes = 0;
    g_files = 0;
    set_stage("Starting");
    query_space();
    scePowerSetArmClockFrequency(444);
    SceUID th = sceKernelCreateThread("scan", scan_thread, 0x10000100, 512 * 1024, 0, 0, NULL);
    if (th < 0) return;
    scanning = 1;
    sceKernelStartThread(th, 0, NULL);
    if (!UM.n) scr = SCR_SCAN;
}

static void apply_scan(void)
{
    dlog("apply_scan quick=%d new items=%d", g_quick, SM.n);
    if (g_quick) { /* nothing changed: keep what's shown, just re-date it */
        scanning = 0;
        patch_cache_header(1);
        scePowerSetArmClockFrequency(333);
        return;
    }
    char keep_path[320] = {0};
    int keep_cat = -1;
    if (scr == SCR_DETAIL && detail_idx < UM.n) { snprintf(keep_path, sizeof keep_path, "%s", UM.it[detail_idx].path); keep_cat = UM.it[detail_idx].cat; }

    /* carry over icons that are already loaded, free the rest */
    vita2d_wait_rendering_done();
    for (int i = 0; i < SM.n; i++)
        for (int j = 0; j < UM.n; j++)
            if (UM.it[j].icon && UM.it[j].icon_kind == SM.it[i].icon_kind && !strcmp(UM.it[j].icon_src, SM.it[i].icon_src)) {
                SM.it[i].icon = UM.it[j].icon; SM.it[i].icon_state = 1;
                UM.it[j].icon = NULL;
                break;
            }
    for (int j = 0; j < UM.n; j++) if (UM.it[j].icon) { vita2d_free_texture(UM.it[j].icon); UM.it[j].icon = NULL; icons_loaded--; }

    Model t = UM; UM = SM; SM = t;
    SM.n = SM.nb = 0;
    um_app_dirs = sm_app_dirs;
    Units tu = UO; UO = UN; UN = tu;
    UN.n = 0;
    UP.n = 0;
    scanning = 0;
    query_space();
    compute_totals();
    write_cache();
    scePowerSetArmClockFrequency(333);

    if (scr == SCR_SCAN) scr = SCR_HOME;
    if (scr == SCR_LIST) build_list();
    if (scr == SCR_DETAIL) {
        int found = -1;
        for (int i = 0; i < UM.n; i++) if (UM.it[i].cat == keep_cat && !strcmp(UM.it[i].path, keep_path)) { found = i; break; }
        if (found >= 0) detail_idx = found;
        else { scr = SCR_LIST; build_list(); }
    }
}

static void fmt_updated(char *out, int n)
{
    if (!have_cache) { out[0] = 0; return; }
    int diff = today_day - cache_day;
    if (diff <= 0) snprintf(out, n, "Updated today at %d:%02d", cache_hour, cache_min);
    else if (diff == 1) snprintf(out, n, "Updated yesterday");
    else snprintf(out, n, "Updated %d days ago", diff);
}

/* Small status chip under the header: refreshing, or when the numbers are from. */
static void draw_status(int xr, int y)
{
    char line[96];
    if (scanning) {
        uint64_t used = dev_max - dev_free;
        int pct = used ? (int)(100.0 * g_scanned_bytes / used) : 0;
        if (pct > 99) pct = 99;
        if (g_checking) snprintf(line, sizeof line, "Checking for changes...");
        else snprintf(line, sizeof line, "Refreshing... %d%%", pct);
        int w = text_w(0.75f, line);
        text(xr - w, y, 0.75f, C_ACCENT, line);
        spinner(xr - w - 14, y - 5, 18);
    } else {
        fmt_updated(line, sizeof line);
        text_r(xr, y, 0.75f, C_FAINT, line);
    }
}

static void busy_toast(void) { show_toast("Hang on, the scan is still refreshing. Deleting is paused until it's done."); }

static void draw_scan(void)
{
    char a[64], b[64], line[160];
    spinner(SCREEN_W / 2, 170, 150);
    text_c(SCREEN_W / 2, 300, 1.35f, C_TEXT, "Checking your memory card");
    uint64_t used = dev_max - dev_free;
    float f = used ? (float)g_scanned_bytes / (float)used : 0;
    progress(260, 324, 440, 10, f);
    text_c(SCREEN_W / 2, 368, 0.9f, C_DIM, g_stage[g_stage_idx]);
    fmt_size(g_scanned_bytes, a, sizeof a);
    fmt_size(used, b, sizeof b);
    snprintf(line, sizeof line, "%s of %s  ·  %d files", a, b, g_files);
    text_c(SCREEN_W / 2, 396, 0.8f, C_FAINT, line);
    text_c(SCREEN_W / 2, 446, 0.8f, C_DIM, "The first scan reads every file, so it takes the longest.");
    text_c(SCREEN_W / 2, 470, 0.8f, C_DIM, "After that, Storage Manager opens instantly and only checks what changed.");
    text_c(SCREEN_W / 2, 520, 0.75f, C_FAINT, "Vita Storage Manager");
}

static void draw_bar(int x, int y, int w, int h, int highlight)
{
    rrect(x, y, w, h, h / 2, RGBA8(44, 54, 78, 255));
    if (!dev_max) return;
    double px = x;
    for (int c = 0; c < NCAT; c++) {
        double cw = (double)cat_total[c] / (double)dev_max * w;
        if (cw < 0.5) continue;
        unsigned col = RGB(cat_rgb[c], (highlight < 0 || highlight == c) ? 255 : 110);
        int x0 = (int)px, x1 = (int)(px + cw);
        if (c == 0 || x0 <= x + h / 2) {
            vita2d_draw_fill_circle(x + h / 2, y + h / 2, h / 2, col);
            if (x0 < x + h / 2) x0 = x + h / 2;
        }
        if (x1 > x0) vita2d_draw_rectangle(x0, y, x1 - x0, h, col);
        px += cw;
    }
}

static void draw_home(void)
{
    char a[64], b[64], line[160];
    text(40, 62, 1.5f, C_TEXT, "Storage");
    text_r(920, 62, 0.85f, C_DIM, "Memory Card (ux0:)");
    draw_status(920, 84);

    uint64_t used = dev_max - dev_free;
    fmt_size(used, a, sizeof a);
    fmt_size(dev_max, b, sizeof b);
    text(40, 112, 1.35f, C_TEXT, a);
    snprintf(line, sizeof line, "used of %s", b);
    text(46 + text_w(1.35f, a), 112, 0.9f, C_DIM, line);
    fmt_size(dev_free, a, sizeof a);
    snprintf(line, sizeof line, "%s free", a);
    text_r(920, 112, 1.0f, dev_free < (2ULL << 30) ? RGBA8(251, 146, 60, 255) : RGBA8(134, 239, 172, 255), line);
    draw_bar(40, 126, 880, 16, home_sel);

    int y0 = 160, rh = 42;
    for (int c = 0; c < NCAT; c++) {
        int y = y0 + c * rh;
        if (c == home_sel) rrect(30, y, 900, rh - 4, 10, C_SEL);
        vita2d_draw_fill_circle(54, y + 19, 6, RGB(cat_rgb[c], 255));
        text(74, y + 26, 1.0f, C_TEXT, cat_name[c]);
        if (c != CAT_OTHER) {
            snprintf(line, sizeof line, cat_count[c] == 1 ? "%d item" : "%d items", cat_count[c]);
            text(330, y + 26, 0.8f, C_FAINT, line);
        }
        if (c == home_sel) text_fit(440, y + 26, 0.75f, C_DIM, cat_desc[c], 270);
        fmt_size(cat_total[c], a, sizeof a);
        text_r(c == CAT_OTHER ? 912 : 890, y + 26, 1.0f, C_TEXT, a);
        if (c != CAT_OTHER) chevron(902, y + 19, c == home_sel ? C_TEXT : C_FAINT);
    }
    footer_line();
    int x = 920;
    if (!scanning) x = hint(x, 532, B_START, "Rescan");
    if (home_sel != CAT_OTHER) x = hint(x, 532, B_CROSS, "Open");
}

#define LIST_Y 108
#define ROW_H 66
#define ROWS 6

static int has_action(const Item *it) { return can_uninstall(it) || it->del_kind != DEL_NONE; }
static const char *action_name(const Item *it) { return can_uninstall(it) ? "Uninstall" : "Delete"; }

static void draw_list(void)
{
    char a[64], line[200], ago[64];
    vita2d_draw_fill_circle(50, 52, 7, RGB(cat_rgb[cur_cat], 255));
    text(66, 62, 1.45f, C_TEXT, cat_name[cur_cat]);
    fmt_size(cat_total[cur_cat], a, sizeof a);
    text_r(920, 62, 1.3f, C_TEXT, a);
    snprintf(line, sizeof line, "%d %s  ·  Sorted by %s", list_n, list_n == 1 ? "item" : "items", sort_name[sort_mode]);
    text(42, 90, 0.8f, C_DIM, line);
    text_r(920, 90, 0.8f, C_FAINT, cat_desc[cur_cat]);

    if (list_n == 0) text_c(SCREEN_W / 2, 300, 1.2f, C_DIM, "Nothing here");
    if (list_sel < list_top) list_top = list_sel;
    if (list_sel >= list_top + ROWS) list_top = list_sel - ROWS + 1;
    uint64_t biggest = 1;
    for (int i = 0; i < list_n; i++) if (items[list_idx[i]].size > biggest) biggest = items[list_idx[i]].size;
    icon_budget = 2;
    for (int r = 0; r < ROWS && list_top + r < list_n; r++) {
        int k = list_top + r;
        Item *it = &items[list_idx[k]];
        int y = LIST_Y + r * ROW_H;
        if (k == list_sel) rrect(30, y, 886, ROW_H - 6, 12, C_SEL);
        int wide = it->icon_kind == ICON_ISO || it->icon_kind == ICON_CSO || it->icon_kind == ICON_PBP;
        int iw = wide ? 86 : 48;
        draw_icon(it, 42, y + 6, iw, 48);
        int tx = 42 + iw + 16;
        text_fit(tx, y + 27, 1.0f, C_TEXT, it->name, 690 - tx);
        if (it->cat == CAT_EXTRA || it->cat == CAT_MEDIA || (it->cat == CAT_HB && !it->installed))
            snprintf(line, sizeof line, "%s", it->note[0] ? it->note : it->path);
        else {
            fmt_ago(it->last_day, ago, sizeof ago);
            snprintf(line, sizeof line, "%s%s%s%s", it->id, it->id[0] ? "  ·  " : "", ago,
                     it->nbub ? "  ·  Has a bubble" : "");
        }
        text_fit(tx, y + 49, 0.75f, C_DIM, line, 700 - tx);
        fmt_size(it->size, a, sizeof a);
        text_r(900, y + 27, 1.0f, C_TEXT, a);
        int bw = (int)(140.0 * (double)it->size / (double)biggest);
        rrect(760, y + 40, 140, 5, 2, RGBA8(44, 54, 78, 255));
        if (bw >= 4) rrect(760, y + 40, bw, 5, 2, RGB(cat_rgb[cur_cat], 255));
    }
    if (list_n > ROWS) {
        int track = ROWS * ROW_H - 6, th = track * ROWS / list_n;
        if (th < 24) th = 24;
        int ty = LIST_Y + (track - th) * list_top / (list_n - ROWS);
        rrect(926, LIST_Y, 4, track, 2, RGBA8(36, 46, 70, 255));
        rrect(926, ty, 4, th, 2, C_DIM);
    }
    footer_line();
    int x = 920;
    x = hint(x, 532, B_CIRCLE, "Back");
    x = hint(x, 532, B_SQUARE, "Sort");
    if (list_n) {
        Item *sel = &items[list_idx[list_sel]];
        if (has_action(sel) && !scanning) x = hint(x, 532, B_TRIANGLE, action_name(sel));
        x = hint(x, 532, B_CROSS, "Details");
    }
    if (list_n > ROWS) x = hint(x, 532, B_LR, "Page");
}

static const char *type_label(const Item *it)
{
    switch (it->cat) {
    case CAT_VITA: return "PS Vita game";
    case CAT_HB: return it->installed ? "Homebrew app" : "Homebrew data";
    case CAT_PSP: return it->icon_kind == ICON_PBP ? "PSP title (EBOOT)" : (it->icon_kind == ICON_CSO ? "PSP game (CSO)" : "PSP game (ISO)");
    case CAT_PS1: return "PS1 Classic";
    case CAT_SAVE: return "Saved data";
    case CAT_MEDIA: return "Media";
    case CAT_EXTRA: return it->del_kind == DEL_APP ? "Orphaned bubble" : "Extra file";
    default: return "";
    }
}

static void draw_detail(void)
{
    char a[64], line[400], d1[64];
    Item *it = &items[detail_idx];
    text(42, 44, 0.8f, C_DIM, cat_name[it->cat]);
    icon_budget = 1;
    int wide = it->icon_kind == ICON_ISO || it->icon_kind == ICON_CSO || it->icon_kind == ICON_PBP;
    if (!wide) draw_icon(it, 40, 64, 160, 160);
    else draw_icon(it, 30, 84, 180, 100);

    int x = 236;
    text_fit(x, 92, 1.45f, C_TEXT, it->name, 920 - x);
    snprintf(line, sizeof line, "%s%s%s", type_label(it), it->id[0] ? "  ·  " : "", it->id);
    text(x, 122, 0.85f, C_DIM, line);
    if (it->del_kind == DEL_PREFIX) snprintf(line, sizeof line, "%s/%s*", it->path, it->id);
    else snprintf(line, sizeof line, "%s", it->path);
    text_fit(x, 146, 0.75f, C_FAINT, line, 920 - x);
    fmt_size(it->size, a, sizeof a);
    text(x, 196, 1.7f, C_TEXT, a);
    text(x + text_w(1.7f, a) + 10, 196, 0.85f, C_DIM, "on the memory card");

    int y = 230, game = it->cat == CAT_PSP || it->cat == CAT_PS1;
    struct { const char *label; uint64_t v; int show; } rows[] = {
        {game ? "Game" : "Application", it->part[P_APP], it->cat == CAT_VITA || game || (it->cat == CAT_HB && it->part[P_APP])},
        {"Update", it->part[P_UPD], it->cat == CAT_VITA},
        {"DLC", it->part[P_DLC], it->cat == CAT_VITA},
        {"App data", it->part[P_DATA], it->cat == CAT_HB},
        {it->nbub > 1 ? "Bubbles (Adrenaline)" : "Bubble (Adrenaline)", it->part[P_BUB], game},
        {"Saved data (listed under Saved Data)", it->part[P_SAVE], it->cat == CAT_VITA || it->cat == CAT_HB || game},
    };
    for (unsigned r = 0; r < sizeof rows / sizeof rows[0]; r++) {
        if (!rows[r].show) continue;
        vita2d_draw_rectangle(x, y, 920 - x, 1, C_LINE);
        text(x, y + 25, 0.9f, C_DIM, rows[r].label);
        fmt_size(rows[r].v, a, sizeof a);
        if (rows[r].v && rows[r].label[0] == 'B') {
            snprintf(line, sizeof line, "%s  ·  %s", it->bub_ids[0], a);
            text_r(920, y + 25, 0.9f, C_TEXT, it->nbub > 1 ? a : line);
        } else text_r(920, y + 25, 0.9f, rows[r].v ? C_TEXT : C_FAINT, rows[r].v ? a : "None");
        y += 34;
    }
    if (it->cat != CAT_EXTRA) {
        vita2d_draw_rectangle(x, y, 920 - x, 1, C_LINE);
        text(x, y + 25, 0.9f, C_DIM, it->cat == CAT_MEDIA ? "Last changed" : "Last played");
        fmt_date(it->last_day, d1, sizeof d1);
        if (it->last_day) { char ago[64]; fmt_ago(it->last_day, ago, sizeof ago); snprintf(line, sizeof line, "%s  (%s)", d1, ago + (strncmp(ago, "Played ", 7) ? 0 : 7)); }
        else snprintf(line, sizeof line, "%s", it->cat == CAT_MEDIA ? "Unknown" : "No saves or data found");
        text_r(920, y + 25, 0.9f, C_TEXT, line);
        y += 34;
    }
    if (it->ndata && it->installed) {
        vita2d_draw_rectangle(x, y, 920 - x, 1, C_LINE);
        text(x, y + 25, 0.9f, C_DIM, it->ndata > 1 ? "Data folders" : "Data folder");
        line[0] = 0;
        for (int k = 0; k < it->ndata; k++) {
            const char *fn = strrchr(it->data_paths[k], '/');
            char part[160];
            snprintf(part, sizeof part, "%s%s%s", k ? ", " : "", fn ? fn + 1 : it->data_paths[k], it->data_sure[k] ? "" : " (guessed)");
            strncat(line, part, sizeof line - strlen(line) - 1);
        }
        text_r(920, y + 25, 0.9f, C_TEXT, line);
        y += 34;
    }
    vita2d_draw_rectangle(x, y, 920 - x, 1, C_LINE);

    const char *note = it->note;
    if (it->installed && !it->protect && !uninstall_ok)
        note = "Uninstall isn't available; hold the bubble on the home screen and choose Delete.";
    if (note[0]) text_fit(x, y + 30, 0.8f, (it->cat == CAT_EXTRA || it->protect) ? C_WARN : C_DIM, note, 920 - x);

    footer_line();
    int hx = 920;
    hx = hint(hx, 532, B_CIRCLE, "Back");
    if (has_action(it) && !scanning) hint(hx, 532, B_TRIANGLE, action_name(it));
    else if (scanning) draw_status(hx, 532);
}

/* --------------------------------------------- confirm / checklist dialog */

enum { UR_APP, UR_UPD, UR_DLC, UR_DATA, UR_SAVE, UR_GAME, UR_BUBBLE, UR_PATH };
typedef struct {
    char label[112];
    char path[320];
    char id[24];          /* app/bubble ID, or save-folder prefix for PSP saves */
    uint64_t size;
    int kind, toggle, on, prefix;
} URow;
static URow urows[16];
static int nurows, ufocus, checklist_mode; /* 1 = uninstall an app, 2 = delete a PSP/PS1 game */
static int job_item;          /* index of the item being removed */
static char job_name[128];

static void urow(int kind, const char *label, const char *path, const char *id, uint64_t size, int toggle, int on)
{
    if (nurows >= 16) return;
    URow *r = &urows[nurows++];
    memset(r, 0, sizeof *r);
    snprintf(r->label, sizeof r->label, "%s", label);
    snprintf(r->path, sizeof r->path, "%s", path);
    snprintf(r->id, sizeof r->id, "%s", id ? id : "");
    r->size = size; r->kind = kind; r->toggle = toggle; r->on = on;
}

/* Opens the right dialog for the item: checklist for apps and PSP/PS1 games,
 * a simple confirm for everything else. */
static void open_remove(int idx)
{
    Item *it = &items[idx];
    char p[200], label[112];
    detail_idx = idx;
    nurows = 0;
    checklist_mode = 0;
    if (can_uninstall(it)) {
        checklist_mode = 1;
        urow(UR_APP, it->cat == CAT_VITA ? "Game and its bubble" : "App and its bubble", it->path, it->id, it->part[P_APP], 0, 1);
        snprintf(p, sizeof p, "ux0:patch/%s", it->id);
        if (it->part[P_UPD] || path_exists(p)) urow(UR_UPD, "Update", p, NULL, it->part[P_UPD], 0, 1);
        snprintf(p, sizeof p, "ux0:addcont/%s", it->id);
        if (it->part[P_DLC] || path_exists(p)) urow(UR_DLC, "DLC", p, NULL, it->part[P_DLC], 0, 1);
        for (int k = 0; k < it->ndata; k++) {
            const char *fn = strrchr(it->data_paths[k], '/');
            snprintf(label, sizeof label, "Data folder: %s%s", fn ? fn + 1 : it->data_paths[k], it->data_sure[k] ? "" : "  (guessed match)");
            urow(UR_DATA, label, it->data_paths[k], NULL, it->data_sizes[k], 1, it->data_sure[k]);
        }
        snprintf(p, sizeof p, "ux0:user/00/savedata/%s", it->id);
        if (it->part[P_SAVE] || path_exists(p)) urow(UR_SAVE, "Also delete saved data", p, NULL, it->part[P_SAVE], 1, 0);
    } else if ((it->cat == CAT_PSP || it->cat == CAT_PS1) && it->del_kind == DEL_PATH) {
        checklist_mode = 2;
        const char *gl = it->icon_kind == ICON_PBP ? "Game folder (EBOOT)" : (it->icon_kind == ICON_CSO ? "Game file (CSO)" : "Game file (ISO)");
        urow(UR_GAME, gl, it->path, NULL, it->part[P_APP], 0, 1);
        if (uninstall_ok)
            for (int k = 0; k < it->nbub; k++) {
                snprintf(label, sizeof label, "Bubble on the home screen: %s", it->bub_ids[k]);
                snprintf(p, sizeof p, "ux0:app/%s", it->bub_ids[k]);
                urow(UR_BUBBLE, label, p, it->bub_ids[k], it->bub_sizes[k], 1, 1);
            }
        if (it->part[P_SAVE]) {
            urow(UR_SAVE, "Also delete saved data", "ux0:pspemu/PSP/SAVEDATA", it->id, it->part[P_SAVE], 1, 0);
            urows[nurows - 1].prefix = 1;
        }
    } else if (it->del_kind == DEL_NONE) return;
    ufocus = nurows; /* the main button */
    confirm = 1;
}

#define KEEP_DIR "ux0:data/Storage/kept_saves"

/* Saves moved aside during an uninstall go back where they were. Also runs at
 * start-up in case the app was closed half-way through. */
static void restore_kept_saves(void)
{
    int n;
    char from[300], to[300];
    Ent *v = list_dir(KEEP_DIR, &n);
    for (int i = 0; i < n; i++) {
        if (!v[i].dir) continue;
        join(from, sizeof from, KEEP_DIR, v[i].name);
        join(to, sizeof to, "ux0:user/00/savedata", v[i].name);
        if (!path_exists(to)) sceIoRename(from, to);
    }
    free(v);
}

/* Drops cached measurements for a deleted path (or, with name_prefix, every
 * folder in path whose name starts with it), so the next refresh stays exact. */
static void units_forget(const char *path, const char *name_prefix)
{
    char pre[400];
    if (name_prefix) snprintf(pre, sizeof pre, "%s/%s", path, name_prefix);
    size_t l = strlen(name_prefix ? pre : path);
    for (int i = UO.n - 1; i >= 0; i--) {
        const char *u = UO.u[i].path;
        int hit = name_prefix ? !strncasecmp(u, pre, l) : (!strncasecmp(u, path, l) && (u[l] == 0 || u[l] == '/'));
        if (hit) UO.u[i] = UO.u[--UO.n];
    }
}

/* The system uninstaller also edits its own files (LiveArea metadata,
 * licences, the home-screen layout). Re-measure those so the next refresh's
 * free-space accounting still adds up. Runs on the worker thread. */
static void remeasure_system_units(void)
{
    for (int i = 0; i < UO.n; i++) {
        Unit *u = &UO.u[i];
        if (unit_class(u->path) != 30) continue;
        if (u->isfile) {
            SceIoStat st;
            if (sceIoGetstat(u->path, &st) >= 0) { u->size = st.st_size; u->alloc = round_cl(st.st_size); }
            continue;
        }
        Acc a = {0, 0, 0};
        walk(u->path, &a);
        u->size = a.size; u->alloc = a.alloc; u->newest = a.newest;
    }
}

/* ---- the worker: all file system work happens here, off the UI thread */

static int job_thread(SceSize args, void *argp)
{
    (void)args; (void)argp;
    Item *it = &items[job_item];
    job_ok = 1;
    job_app_gone = 0;
    job_err[0] = 0;

    if (!checklist_mode) {                  /* simple delete */
        job_total = it->size;
        if (it->del_kind == DEL_APP) {
            job_stage(1, "Removing the bubble...");
            int r = uninstall_app(it->id);
            if (r < 0) { job_ok = 0; snprintf(job_err, sizeof job_err, "Couldn't remove the bubble (0x%08X)", (unsigned)r); }
            else { job_stage(1, "Tidying up..."); remeasure_system_units(); }
        } else {
            job_stage(0, "Deleting %s...", job_name);
            job_ok = it->del_kind == DEL_PREFIX ? rm_prefix(it->path, it->id) : rm_rf(it->path);
            if (!job_ok) snprintf(job_err, sizeof job_err, "Couldn't delete everything in %.60s", job_name);
        }
        job_done = 1;
        sceKernelExitDeleteThread(0);
        return 0;
    }

    uint64_t total = 0;
    for (int r = 0; r < nurows; r++) if (urows[r].on) total += urows[r].size;
    job_total = total ? total : 1;

    URow *save = NULL;
    for (int r = 0; r < nurows; r++) if (urows[r].kind == UR_SAVE) save = &urows[r];

    /* 1. Vita saves being kept are moved out of harm's way first. */
    int moved = 0;
    char kept[300];
    if (checklist_mode == 1 && save && !save->on && path_exists(save->path)) {
        job_stage(1, "Protecting saved data...");
        sceIoMkdir("ux0:data/Storage", 0777);
        sceIoMkdir(KEEP_DIR, 0777);
        join(kept, sizeof kept, KEEP_DIR, it->id);
        if (path_exists(kept)) rm_rf(kept);
        if (sceIoRename(save->path, kept) < 0) {
            job_ok = 0;
            snprintf(job_err, sizeof job_err, "Couldn't protect the saved data, so nothing was removed");
            job_done = 1;
            sceKernelExitDeleteThread(0);
            return 0;
        }
        moved = 1;
    }

    /* 2. The app itself, through the system uninstaller. */
    for (int r = 0; r < nurows; r++) {
        if (urows[r].kind != UR_APP) continue;
        job_stage(1, "Uninstalling %s...", job_name);
        int res = uninstall_app(urows[r].id);
        if (res < 0) {
            if (moved) restore_kept_saves();
            job_ok = 0;
            snprintf(job_err, sizeof job_err, "Uninstall failed (0x%08X). Nothing else was removed.", (unsigned)res);
            job_done = 1;
            sceKernelExitDeleteThread(0);
            return 0;
        }
        job_bytes += urows[r].size;
        job_app_gone = 1;
    }

    /* 3. Files: game, update, DLC, data folders, saves. Byte-accurate progress. */
    for (int r = 0; r < nurows; r++) {
        URow *u = &urows[r];
        if (!u->on || u->kind == UR_APP || u->kind == UR_BUBBLE) continue;
        uint64_t start = job_bytes;
        job_stage(0, "Removing %s...", u->kind == UR_GAME ? "the game" : u->kind == UR_SAVE ? "saved data" : u->label);
        int ok = u->prefix ? rm_prefix(u->path, u->id) : (path_exists(u->path) ? rm_rf(u->path) : 1);
        if (!ok) { job_ok = 0; snprintf(job_err, sizeof job_err, "Some files in %.80s couldn't be deleted", u->path); }
        if (job_bytes < start + u->size) job_bytes = start + u->size; /* keep the bar honest if sizes drifted */
    }

    /* 4. Adrenaline bubbles for PSP/PS1 games. */
    for (int r = 0; r < nurows; r++) {
        URow *u = &urows[r];
        if (u->kind != UR_BUBBLE || !u->on) continue;
        job_stage(1, "Removing the bubble %s...", u->id);
        if (uninstall_app(u->id) < 0) { job_ok = 0; snprintf(job_err, sizeof job_err, "The bubble %s couldn't be removed", u->id); }
        job_bytes += u->size;
    }

    if (moved) restore_kept_saves();
    int used_promoter = job_app_gone;
    for (int r = 0; r < nurows; r++) if (urows[r].kind == UR_BUBBLE && urows[r].on) used_promoter = 1;
    if (used_promoter) { job_stage(1, "Tidying up..."); remeasure_system_units(); }
    job_done = 1;
    sceKernelExitDeleteThread(0);
    return 0;
}

static void start_job(void)
{
    job_item = detail_idx;
    snprintf(job_name, sizeof job_name, "%s", items[job_item].name);
    job_bytes = 0;
    job_total = 1;
    job_done = 0;
    job_stage(1, "Starting...");
    confirm = 0;
    SceUID th = sceKernelCreateThread("remove", job_thread, 0x10000100, 512 * 1024, 0, 0, NULL);
    if (th < 0) { show_toast("Couldn't start the delete"); return; }
    job_running = 1;
    sceKernelStartThread(th, 0, NULL);
}

static void remove_item(int idx)
{
    vita2d_wait_rendering_done();
    if (items[idx].icon) { vita2d_free_texture(items[idx].icon); icons_loaded--; }
    memmove(&items[idx], &items[idx + 1], sizeof(Item) * (nitems - idx - 1));
    nitems--;
}

/* Back on the UI thread: bring the lists in line with what was removed. */
static void finish_job(void)
{
    char msg[240], a[64];
    Item *it = &items[job_item];
    uint64_t before = dev_free;
    int was_cat = it->cat;
    job_running = 0;

    if (!job_ok && checklist_mode == 1 && !job_app_gone) { /* the uninstall itself failed: nothing changed */
        show_toast(job_err);
        checklist_mode = 0;
        return;
    }

    char id[24], name[128];
    snprintf(id, sizeof id, "%s", it->id);
    snprintf(name, sizeof name, "%s", it->name);

    /* forget measurements of what was removed */
    if (checklist_mode) {
        for (int r = 0; r < nurows; r++)
            if (urows[r].on) units_forget(urows[r].path, urows[r].prefix ? urows[r].id : NULL);
    } else if (job_ok) units_forget(it->path, it->del_kind == DEL_PREFIX ? it->id : NULL);
    URow *save = NULL;
    for (int r = 0; r < nurows; r++) if (urows[r].kind == UR_SAVE) save = &urows[r];

    if (checklist_mode) {
        /* leftovers the user chose to keep become Extra Files */
        for (int r = 0; r < nurows; r++) {
            URow *u = &urows[r];
            if (u->on) continue;
            if (u->kind == UR_DATA) {
                char nm[200], note[112];
                const char *fn = strrchr(u->path, '/');
                snprintf(nm, sizeof nm, "Leftover data: %s", fn ? fn + 1 : u->path);
                snprintf(note, sizeof note, "Data from %.60s, which was uninstalled", name);
                add_extra(u->path, nm, note, u->size);
            } else if (u->kind == UR_BUBBLE) add_orphan_bubble(u->id, name, u->size);
        }
        /* saves: removed with the game, or marked as orphaned */
        int pref = checklist_mode == 2;
        for (int i = nitems - 1; i >= 0; i--) {
            Item *s = &items[i];
            if (s->cat != CAT_SAVE || strcasecmp(s->id, id)) continue;
            if (pref != (s->del_kind == DEL_PREFIX)) continue;
            if (save && save->on) remove_item(i);
            else snprintf(s->note, sizeof s->note, "Save for a title that is not installed");
        }
        for (int i = 0; i < nitems; i++)
            if (items[i].cat == was_cat && !strcasecmp(items[i].id, id) && !strcmp(items[i].name, name)) { remove_item(i); break; }
    } else if (job_ok) {
        if (it->cat == CAT_SAVE) {
            Item *g = find_id(it->id, (1 << CAT_VITA) | (1 << CAT_HB) | (1 << CAT_PSP) | (1 << CAT_PS1));
            if (g) g->part[P_SAVE] = 0;
        }
        remove_item(job_item);
    }

    query_space();
    compute_totals();
    write_cache();
    fmt_size(dev_free > before ? dev_free - before : 0, a, sizeof a);
    if (!job_ok) snprintf(msg, sizeof msg, "%s", job_err);
    else snprintf(msg, sizeof msg, "%s %.60s  ·  %s freed", checklist_mode == 1 ? "Uninstalled" : "Deleted", name, a);
    show_toast(msg);
    checklist_mode = 0;
    scr = SCR_LIST;
    build_list();
}

static void draw_job(void)
{
    char a[64], b[64], line[200];
    vita2d_draw_rectangle(0, 0, SCREEN_W, SCREEN_H, RGBA8(0, 0, 0, 170));
    int w = 560, h = 250, x = (SCREEN_W - w) / 2, y = (SCREEN_H - h) / 2;
    rrect(x, y, w, h, 18, RGBA8(28, 37, 60, 255));
    spinner(SCREEN_W / 2, y + 66, 84);
    const char *label = job_label[job_li];
    char fit[200];
    snprintf(fit, sizeof fit, "%s", label);
    text_c(SCREEN_W / 2, y + 140, 1.0f, C_TEXT, fit);
    float f = job_indet ? -1.0f : (float)job_bytes / (float)job_total;
    progress(x + 40, y + 160, w - 80, 10, f);
    if (!job_indet) {
        fmt_size(job_bytes, a, sizeof a);
        fmt_size(job_total, b, sizeof b);
        int pct = (int)(100.0 * job_bytes / (job_total ? job_total : 1));
        if (pct > 100) pct = 100;
        snprintf(line, sizeof line, "%d%%  ·  %s of %s", pct, a, b);
    } else snprintf(line, sizeof line, "Working...");
    text_c(SCREEN_W / 2, y + 200, 0.8f, C_DIM, line);
    text_c(SCREEN_W / 2, y + 228, 0.7f, C_FAINT, "Please don't close Storage");
}

static void draw_checklist(void)
{
    char a[64], line[300];
    Item *it = &items[detail_idx];
    int app = checklist_mode == 1;
    vita2d_draw_rectangle(0, 0, SCREEN_W, SCREEN_H, RGBA8(0, 0, 0, 170));
    int rh = 38, w = 720, h = 176 + nurows * rh + 30, x = (SCREEN_W - w) / 2, y = (SCREEN_H - h) / 2;
    if (y < 8) y = 8;
    rrect(x, y, w, h, 18, RGBA8(28, 37, 60, 255));
    snprintf(line, sizeof line, "%s %s?", app ? "Uninstall" : "Delete", it->name);
    text_fit(x + 30, y + 46, 1.2f, C_TEXT, line, w - 60);
    text(x + 30, y + 74, 0.8f, C_DIM, "These will be removed:");

    uint64_t total = 0;
    for (int r = 0; r < nurows; r++) {
        URow *u = &urows[r];
        int ry = y + 88 + r * rh;
        if (u->on) total += u->size;
        if (ufocus == r) rrect(x + 16, ry, w - 32, rh - 4, 8, C_SEL);
        int bx = x + 30, by = ry + 9;
        if (u->toggle) {
            rrect(bx, by, 18, 18, 4, u->on ? C_ACCENT : RGBA8(70, 84, 116, 255));
            if (!u->on) rrect(bx + 2, by + 2, 14, 14, 3, RGBA8(28, 37, 60, 255));
            else for (int o = 0; o < 2; o++) {
                vita2d_draw_line(bx + 4, by + 9 + o, bx + 8, by + 13 + o, C_TEXT);
                vita2d_draw_line(bx + 8, by + 13 + o, bx + 14, by + 5 + o, C_TEXT);
            }
        } else vita2d_draw_fill_circle(bx + 9, by + 9, 4, C_DIM);
        text_fit(bx + 30, ry + 25, 0.9f, u->on ? C_TEXT : C_DIM, u->label, w - 220);
        fmt_size(u->size, a, sizeof a);
        text_r(x + w - 30, ry + 25, 0.9f, u->on ? C_TEXT : C_FAINT, a);
    }

    int ny = y + 88 + nurows * rh + 22;
    const char *warn = it->cat == CAT_VITA ? "To play it again you'll need to reinstall it (PKGj or your backup)."
                     : app ? "To use it again you'll need to reinstall its VPK."
                           : "The game file is deleted from the card.";
    text_fit(x + 30, ny, 0.8f, C_WARN, warn, w - 60);
    for (int r = 0; r < nurows; r++)
        if (urows[r].kind == UR_SAVE && !urows[r].on) { text_fit(x + 30, ny + 22, 0.75f, C_DIM, "Saved data will be kept.", w - 60); break; }

    int bw = 220, bh = 40, by = y + h - bh - 18, b1 = x + w - 30 - bw * 2 - 14, b2 = x + w - 30 - bw;
    fmt_size(total, a, sizeof a);
    snprintf(line, sizeof line, "%s  ·  %s", app ? "Uninstall" : "Delete", a);
    rrect(b1, by, bw, bh, 20, ufocus == nurows ? RGBA8(220, 70, 80, 255) : RGBA8(70, 40, 56, 255));
    text(b1 + (bw - text_w(0.9f, line)) / 2, by + 26, 0.9f, C_TEXT, line);
    rrect(b2, by, bw, bh, 20, ufocus == nurows + 1 ? RGBA8(70, 90, 130, 255) : RGBA8(40, 52, 80, 255));
    text(b2 + (bw - text_w(0.9f, "Cancel")) / 2, by + 26, 0.9f, C_TEXT, "Cancel");
}

static void draw_confirm(void)
{
    char a[64], line[300];
    Item *it = &items[detail_idx];
    vita2d_draw_rectangle(0, 0, SCREEN_W, SCREEN_H, RGBA8(0, 0, 0, 170));
    int w = 600, h = 230, x = (SCREEN_W - w) / 2, y = (SCREEN_H - h) / 2;
    rrect(x, y, w, h, 18, RGBA8(28, 37, 60, 255));
    snprintf(line, sizeof line, "Delete %s?", it->name);
    text_fit(x + 32, y + 52, 1.2f, C_TEXT, line, w - 64);
    fmt_size(it->size, a, sizeof a);
    snprintf(line, sizeof line, "This frees %s. It can't be undone.", a);
    text(x + 32, y + 92, 0.9f, C_DIM, line);
    const char *warn = "";
    if (it->cat == CAT_SAVE) warn = "Your saved progress for this game will be lost.";
    else if (it->cat == CAT_HB) warn = "Make sure no app still uses this folder.";
    else if (it->del_kind == DEL_APP) warn = "Removes the bubble from the home screen.";
    else if (it->cat == CAT_EXTRA) warn = "This is a leftover file. Installed apps are not affected.";
    text_fit(x + 32, y + 122, 0.85f, C_WARN, warn, w - 64);
    text_fit(x + 32, y + 150, 0.7f, C_FAINT, it->path, w - 64);
    int hx = x + w - 32;
    hx = hint(hx, y + h - 26, B_CIRCLE, "Cancel");
    hint(hx, y + h - 26, B_CROSS, "Delete");
}

static void draw_toast(void)
{
    if (sceKernelGetProcessTimeWide() > toast_until) return;
    int w = text_w(0.9f, toast) + 48;
    if (w > 900) w = 900;
    rrect((SCREEN_W - w) / 2, 452, w, 40, 20, RGBA8(46, 60, 96, 255));
    text_fit((SCREEN_W - w) / 2 + 24, 478, 0.9f, C_TEXT, toast, w - 48);
}

int main(void)
{
    UM.it = calloc(MAX_ITEMS, sizeof(Item));
    SM.it = calloc(MAX_ITEMS, sizeof(Item));
    UM.bub = calloc(MAX_BUBBLES, sizeof(Bubble));
    SM.bub = calloc(MAX_BUBBLES, sizeof(Bubble));
    UO.u = calloc(MAX_UNITS, sizeof(Unit));
    UN.u = calloc(MAX_UNITS, sizeof(Unit));
    UP.u = calloc(MAX_UNITS, sizeof(Unit));
    scePowerSetArmClockFrequency(444);
    sceCtrlSetSamplingMode(SCE_CTRL_MODE_ANALOG);
    {
        SceAppUtilInitParam ip;
        SceAppUtilBootParam bp;
        memset(&ip, 0, sizeof ip);
        memset(&bp, 0, sizeof bp);
        sceAppUtilInit(&ip, &bp);
        int enter = SCE_SYSTEM_PARAM_ENTER_BUTTON_CROSS;
        if (sceAppUtilSystemParamGetInt(SCE_SYSTEM_PARAM_ID_ENTER_BUTTON, &enter) >= 0 &&
            enter == SCE_SYSTEM_PARAM_ENTER_BUTTON_CIRCLE) {
            BTN_OK = SCE_CTRL_CIRCLE;
            BTN_BACK = SCE_CTRL_CROSS;
            swap_ok = 1;
        }
    }
    load_settings();
    SceDateTime now;
    sceRtcGetCurrentClockLocalTime(&now);
    today_day = dt_day(&now);

    vita2d_init();
    /* Textures stay in vita2d's default video memory (CDRAM). Tried and
     * rejected on hardware: cached main memory (USER_RW) showed stale pixels as
     * diagonal streaks, and uncached main memory (USER_RW_UNCACHE) crashed the
     * GPU. CDRAM blocks are 256 KB each, so at most MAX_ICONS icons are kept
     * loaded (about 16 MB). */
    dlog("==== start (texture memblock type 0x%08X)", (unsigned)vita2d_texture_get_alloc_memblock_type());
    vita2d_set_clear_color(RGBA8(8, 11, 20, 255));
    font = vita2d_load_default_pgf();
    dlog("font %p", (void *)font);
    logo = png_file_to_texture("app0:logo.png");
    dlog("logo %p", (void *)logo);
    if (logo) vita2d_texture_set_filters(logo, SCE_GXM_TEXTURE_FILTER_LINEAR, SCE_GXM_TEXTURE_FILTER_LINEAR);

    /* The system uninstaller (same route VitaShell uses): PAF first, then the promoter. */
    {
        uint32_t ptr[0x100] = {0};
        ptr[1] = (uint32_t)&ptr[0];
        uint32_t paf_args[] = {0x400000, 0xEA60, 0x40000, 0, 0};
        sceSysmoduleLoadModuleInternalWithArg(SCE_SYSMODULE_INTERNAL_PAF, sizeof paf_args, paf_args, (void *)ptr);
        if (sceSysmoduleLoadModuleInternal(SCE_SYSMODULE_INTERNAL_PROMOTER_UTIL) >= 0 && scePromoterUtilityInit() >= 0)
            uninstall_ok = 1;
    }
    restore_kept_saves();

    /* Show the last scan straight away, then refresh it in the background. */
    if (load_cache()) {
        query_space();
        compute_totals();
        scr = SCR_HOME;
    }
    dlog("cache: %d items, %d units; screen %d", UM.n, UO.n, scr);
    start_scan(0);

    int last_scr = -1;
    for (;;) {
        uint32_t in = poll_input();
        frame++;
        if (frame <= 3) dlog("frame %d", (int)frame);
        if (scr != last_scr) { dlog("screen %d cat %d", scr, cur_cat); last_scr = scr; }

        if (scanning && g_scan_done && !job_running && !confirm) apply_scan();

        if (job_running) {
            if (job_done) finish_job();
        } else if (scr == SCR_SCAN) {
            /* first-ever scan: nothing to show until it finishes */
        } else if (confirm && checklist_mode) {
            int nf = nurows + 2;
            if (in & SCE_CTRL_UP) ufocus = (ufocus + nf - 1) % nf;
            if (in & SCE_CTRL_DOWN) ufocus = (ufocus + 1) % nf;
            if (ufocus >= nurows && (in & SCE_CTRL_LEFT)) ufocus = nurows;
            if (ufocus >= nurows && (in & SCE_CTRL_RIGHT)) ufocus = nurows + 1;
            if (in & BTN_OK) {
                if (ufocus < nurows) { if (urows[ufocus].toggle) urows[ufocus].on ^= 1; }
                else if (ufocus == nurows) start_job();
                else { confirm = 0; checklist_mode = 0; }
            } else if (in & BTN_BACK) { confirm = 0; checklist_mode = 0; }
        } else if (confirm) {
            if (in & BTN_OK) start_job();
            else if (in & BTN_BACK) confirm = 0;
        } else if (scr == SCR_HOME) {
            if (in & SCE_CTRL_UP) home_sel = (home_sel + NCAT - 1) % NCAT;
            if (in & SCE_CTRL_DOWN) home_sel = (home_sel + 1) % NCAT;
            if ((in & BTN_OK) && home_sel != CAT_OTHER) {
                cur_cat = home_sel; list_sel = list_top = 0; build_list(); scr = SCR_LIST;
            }
            if (in & SCE_CTRL_START) start_scan(1); /* START always does a full rescan */
        } else if (scr == SCR_LIST) {
            if (list_n) {
                if (in & SCE_CTRL_UP) list_sel = (list_sel + list_n - 1) % list_n;
                if (in & SCE_CTRL_DOWN) list_sel = (list_sel + 1) % list_n;
                if (in & SCE_CTRL_LTRIGGER) { list_sel -= ROWS; if (list_sel < 0) list_sel = 0; }
                if (in & SCE_CTRL_RTRIGGER) { list_sel += ROWS; if (list_sel >= list_n) list_sel = list_n - 1; }
                if (in & BTN_OK) { detail_idx = list_idx[list_sel]; scr = SCR_DETAIL; }
                if ((in & SCE_CTRL_TRIANGLE) && has_action(&items[list_idx[list_sel]])) {
                    if (scanning) busy_toast(); else open_remove(list_idx[list_sel]);
                }
            }
            if (in & SCE_CTRL_SQUARE) {
                int keep = list_n ? list_idx[list_sel] : -1;
                sort_mode = (sort_mode + 1) % NSORT;
                build_list();
                for (int i = 0; i < list_n; i++) if (list_idx[i] == keep) list_sel = i;
            }
            if (in & BTN_BACK) scr = SCR_HOME;
        } else if (scr == SCR_DETAIL) {
            if ((in & SCE_CTRL_TRIANGLE) && has_action(&items[detail_idx])) {
                if (scanning) busy_toast(); else open_remove(detail_idx);
            }
            if (in & BTN_BACK) scr = SCR_LIST;
        }

        if (scr == SCR_LIST) evict_icons(list_top, ROWS, list_idx, list_n, -1);
        else evict_icons(0, 0, list_idx, 0, scr == SCR_DETAIL ? detail_idx : -1);

        /* vita2d reuses one buffer for every frame's vertices and doesn't wait
         * for the GPU between frames. Without this the CPU can overwrite the
         * previous frame's vertices while the GPU is still reading them:
         * diagonal streaks at best, a GPU crash at worst (seen when scrolling
         * fast, when each frame's geometry differs). */
        vita2d_wait_rendering_done();
        vita2d_start_drawing();
        vita2d_clear_screen();
        background();
        switch (scr) {
        case SCR_SCAN: draw_scan(); break;
        case SCR_HOME: draw_home(); break;
        case SCR_LIST: draw_list(); break;
        case SCR_DETAIL: draw_detail(); break;
        }
        if (job_running) draw_job();
        else if (confirm) { if (checklist_mode) draw_checklist(); else draw_confirm(); }
        draw_toast();
        vita2d_end_drawing();
        vita2d_swap_buffers();
    }
    return 0;
}
