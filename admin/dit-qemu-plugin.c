// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// The qemu plugin `admin/dit-qemu` loads into qemu-aarch64. It samples
// PSTATE.DIT (bit 24 of the `cpsr` register qemu exposes to plugins) at
// every instruction a thread executes inside a window, which
// `rind/src/low/entry/tests.rs` opens with `hint #84` and closes with
// `hint #85` around one public call, and between `hint #86` and `hint #87`
// leaves out the setup that call's inputs need. Every instruction counts,
// whichever function it belongs to: rind's, core's, or libc's `memcpy`.
//
// For each window it writes to `out` one line
//
//     W <on> <pre> <holes> <post>
//
// counting the instructions run with DIT set, those run clear before the
// first one set (the call's checks of public arguments, and the toggle
// itself), those run clear between two set ones, and those run clear after
// the last set one (the return to the test). A hole is a stretch of the call
// that ran without DIT after the call had started handling its secrets: a
// second toggle, or code that cleared DIT under a live `Entry`. Then one
// line `H <count> <symbol>` for each function a hole ran in, one line
// `P <count> <symbol>` for each function run before DIT was first set, and
// one line `T <count> <symbol>` for each function run clear after the last
// set one, so a call that clears DIT early and then does secret work before
// it returns shows up too.

#include <glib.h>
#include <qemu-plugin.h>
#include <stdio.h>
#include <string.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

// `hint #84` to `hint #87`, which execute as no-ops in A64.
#define MARK_OPEN 0xd5032a9fu
#define MARK_CLOSE 0xd5032abfu
#define MARK_PAUSE 0xd5032adfu
#define MARK_RESUME 0xd5032affu

#define PSTATE_DIT (1u << 24)
#define MAX_VCPUS 256

struct insn_info {
    uint64_t vaddr;
    const char *symbol;
};

struct window {
    uint64_t on, pre, holes, post_run;
    // Symbol to count, for the holes, the instructions before the first
    // set one, and the clear run since the last set one.
    GHashTable *hole_syms, *pre_syms, *run_syms;
};

static FILE *out;
static GMutex out_lock;
// 1 while a thread is inside a window and not paused: the condition every
// other instruction's sampling callback runs on.
static qemu_plugin_u64 sampling;
static struct qemu_plugin_register *cpsr[MAX_VCPUS];
static GByteArray *buf[MAX_VCPUS];
static struct window win[MAX_VCPUS];
static int open_windows[MAX_VCPUS];

static GHashTable *counts(void) {
    return g_hash_table_new_full(g_str_hash, g_str_equal, g_free, NULL);
}

static void bump(GHashTable *t, const char *sym, uint64_t by) {
    gpointer old = NULL;
    if (g_hash_table_lookup_extended(t, sym, NULL, &old)) {
        g_hash_table_replace(t, g_strdup(sym), GSIZE_TO_POINTER(GPOINTER_TO_SIZE(old) + by));
    } else {
        g_hash_table_insert(t, g_strdup(sym), GSIZE_TO_POINTER(by));
    }
}

static void merge(GHashTable *into, GHashTable *from) {
    GHashTableIter it;
    gpointer k, v;
    g_hash_table_iter_init(&it, from);
    while (g_hash_table_iter_next(&it, &k, &v)) {
        bump(into, k, GPOINTER_TO_SIZE(v));
    }
    g_hash_table_remove_all(from);
}

static void dump(char kind, GHashTable *t) {
    GHashTableIter it;
    gpointer k, v;
    g_hash_table_iter_init(&it, t);
    while (g_hash_table_iter_next(&it, &k, &v)) {
        fprintf(out, "%c %zu %s\n", kind, (size_t)GPOINTER_TO_SIZE(v), (const char *)k);
    }
}

static void vcpu_init(unsigned int vcpu, void *udata) {
    if (vcpu >= MAX_VCPUS) {
        return;
    }
    GArray *regs = qemu_plugin_get_registers();
    for (guint i = 0; i < regs->len; i++) {
        qemu_plugin_reg_descriptor *r = &g_array_index(regs, qemu_plugin_reg_descriptor, i);
        if (strcmp(r->name, "cpsr") == 0) {
            cpsr[vcpu] = r->handle;
        }
    }
    g_array_free(regs, TRUE);
    buf[vcpu] = g_byte_array_new();
    win[vcpu].hole_syms = counts();
    win[vcpu].pre_syms = counts();
    win[vcpu].run_syms = counts();
}

static void sample(unsigned int vcpu, void *udata) {
    struct insn_info *insn = udata;
    if (vcpu >= MAX_VCPUS || cpsr[vcpu] == NULL) {
        return;
    }
    struct window *w = &win[vcpu];
    g_byte_array_set_size(buf[vcpu], 0);
    qemu_plugin_read_register(cpsr[vcpu], buf[vcpu]);
    uint32_t pstate = 0;
    memcpy(&pstate, buf[vcpu]->data, MIN(buf[vcpu]->len, sizeof pstate));
    if (pstate & PSTATE_DIT) {
        w->on++;
        w->holes += w->post_run;
        w->post_run = 0;
        merge(w->hole_syms, w->run_syms);
    } else if (w->on == 0) {
        w->pre++;
        bump(w->pre_syms, insn->symbol, 1);
    } else {
        w->post_run++;
        bump(w->run_syms, insn->symbol, 1);
    }
}

static void mark(unsigned int vcpu, void *udata) {
    uint32_t word = (uint32_t)(uintptr_t)udata;
    if (vcpu >= MAX_VCPUS) {
        return;
    }
    struct window *w = &win[vcpu];
    switch (word) {
    case MARK_OPEN:
        w->on = w->pre = w->holes = w->post_run = 0;
        g_hash_table_remove_all(w->hole_syms);
        g_hash_table_remove_all(w->pre_syms);
        g_hash_table_remove_all(w->run_syms);
        open_windows[vcpu] = 1;
        qemu_plugin_u64_set(sampling, vcpu, 1);
        break;
    case MARK_CLOSE:
        qemu_plugin_u64_set(sampling, vcpu, 0);
        if (!open_windows[vcpu]) {
            break;
        }
        open_windows[vcpu] = 0;
        g_mutex_lock(&out_lock);
        fprintf(out, "W %llu %llu %llu %llu\n", (unsigned long long)w->on,
                (unsigned long long)w->pre, (unsigned long long)w->holes,
                (unsigned long long)w->post_run);
        dump('H', w->hole_syms);
        dump('P', w->pre_syms);
        dump('T', w->run_syms);
        fflush(out);
        g_mutex_unlock(&out_lock);
        break;
    case MARK_PAUSE:
        qemu_plugin_u64_set(sampling, vcpu, 0);
        break;
    case MARK_RESUME:
        qemu_plugin_u64_set(sampling, vcpu, open_windows[vcpu]);
        break;
    }
}

static void tb_trans(struct qemu_plugin_tb *tb, void *udata) {
    for (size_t i = 0; i < qemu_plugin_tb_n_insns(tb); i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint32_t word = 0;
        if (qemu_plugin_insn_size(insn) == 4) {
            qemu_plugin_insn_data(insn, &word, sizeof word);
        }
        if (word == MARK_OPEN || word == MARK_CLOSE || word == MARK_PAUSE ||
            word == MARK_RESUME) {
            qemu_plugin_register_vcpu_insn_exec_cb(insn, mark, QEMU_PLUGIN_CB_NO_REGS,
                                                   (void *)(uintptr_t)word);
            continue;
        }
        // An instruction's handle lasts only while it is translated, so what
        // the sample needs is copied. Translations are few beside executions,
        // and the run is short, so these are never freed.
        struct insn_info *info = g_new(struct insn_info, 1);
        info->vaddr = qemu_plugin_insn_vaddr(insn);
        const char *sym = qemu_plugin_insn_symbol(insn);
        info->symbol = sym ? g_strdup(sym) : g_strdup_printf("0x%llx", (unsigned long long)info->vaddr);
        qemu_plugin_register_vcpu_insn_exec_cond_cb(insn, sample, QEMU_PLUGIN_CB_R_REGS,
                                                    QEMU_PLUGIN_COND_NE, sampling, 0, info);
    }
}

static void at_exit(void *udata) {
    fclose(out);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                                           int argc, char **argv) {
    const char *path = NULL;
    for (int i = 0; i < argc; i++) {
        if (strncmp(argv[i], "out=", 4) == 0) {
            path = argv[i] + 4;
        }
    }
    if (strcmp(info->target_name, "aarch64") != 0) {
        fprintf(stderr, "dit-qemu-plugin: PSTATE.DIT is aarch64's, not %s's\n", info->target_name);
        return -1;
    }
    if (path == NULL || (out = fopen(path, "w")) == NULL) {
        fprintf(stderr, "dit-qemu-plugin: pass out=<path> to write the windows to\n");
        return -1;
    }
    sampling = qemu_plugin_scoreboard_u64(qemu_plugin_scoreboard_new(sizeof(uint64_t)));
    qemu_plugin_register_vcpu_init_cb(id, vcpu_init, NULL);
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_trans, NULL);
    qemu_plugin_register_atexit_cb(id, at_exit, NULL);
    return 0;
}
