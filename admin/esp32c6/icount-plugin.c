// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// A qemu-riscv32 plugin that lets a guest read how many instructions it has
// executed. When the guest executes the marker `slti x0, x0, 0x7a5` (a hint
// that does nothing), the plugin writes the count so far into a0 (low half)
// and a1 (high half), which the guest reads back as its clock. Counts are
// kept per translated instruction, so they are exact.
//
// With `prof=FILE` it also writes, at exit, every executed instruction's
// address and count, for a flat profile against the ELF's symbols.

#include <qemu-plugin.h>
#include <glib.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

// slti x0, x0, 0x7a5
#define MARK 0x7a502013u

static qemu_plugin_u64 count;
static struct qemu_plugin_register *a0, *a1;
static const char *prof;
static GHashTable *pcs; // pc -> uint64_t * (executions)
static GMutex lock;

static void on_mark(unsigned int vcpu, void *udata) {
    uint64_t n = qemu_plugin_u64_get(count, vcpu);
    GByteArray *b = g_byte_array_new();
    uint32_t lo = (uint32_t)n, hi = (uint32_t)(n >> 32);
    g_byte_array_append(b, (const guint8 *)&lo, 4);
    qemu_plugin_write_register(a0, b);
    g_byte_array_set_size(b, 0);
    g_byte_array_append(b, (const guint8 *)&hi, 4);
    qemu_plugin_write_register(a1, b);
    g_byte_array_free(b, TRUE);
}

static void on_insn_prof(unsigned int vcpu, void *udata) {
    (*(uint64_t *)udata)++;
}

static void on_tb(struct qemu_plugin_tb *tb, void *udata) {
    size_t n = qemu_plugin_tb_n_insns(tb);
    for (size_t i = 0; i < n; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint32_t op = 0;
        qemu_plugin_insn_data(insn, &op, sizeof op);
        if (op == MARK) {
            qemu_plugin_register_vcpu_insn_exec_cb(insn, on_mark, QEMU_PLUGIN_CB_RW_REGS, NULL);
        }
        qemu_plugin_register_vcpu_insn_exec_inline_per_vcpu(insn, QEMU_PLUGIN_INLINE_ADD_U64, count, 1);
        if (prof) {
            uint64_t pc = qemu_plugin_insn_vaddr(insn);
            g_mutex_lock(&lock);
            uint64_t *c = g_hash_table_lookup(pcs, &pc);
            if (!c) {
                uint64_t *k = g_new(uint64_t, 1);
                *k = pc;
                c = g_new0(uint64_t, 1);
                g_hash_table_insert(pcs, k, c);
            }
            g_mutex_unlock(&lock);
            qemu_plugin_register_vcpu_insn_exec_cb(insn, on_insn_prof, QEMU_PLUGIN_CB_NO_REGS, c);
        }
    }
}

static void on_vcpu_init(unsigned int vcpu, void *udata) {
    GArray *regs = qemu_plugin_get_registers();
    for (guint i = 0; i < regs->len; i++) {
        qemu_plugin_reg_descriptor *d = &g_array_index(regs, qemu_plugin_reg_descriptor, i);
        if (!strcmp(d->name, "a0") || !strcmp(d->name, "x10")) {
            a0 = d->handle;
        } else if (!strcmp(d->name, "a1") || !strcmp(d->name, "x11")) {
            a1 = d->handle;
        }
    }
    g_array_free(regs, TRUE);
    if (!a0 || !a1) {
        fprintf(stderr, "icount-plugin: no a0/a1 register\n");
        exit(1);
    }
}

static void at_exit(void *udata) {
    if (!prof) {
        return;
    }
    FILE *f = fopen(prof, "w");
    GHashTableIter it;
    gpointer k, v;
    g_hash_table_iter_init(&it, pcs);
    while (g_hash_table_iter_next(&it, &k, &v)) {
        if (*(uint64_t *)v) {
            fprintf(f, "%llx %llu\n", (unsigned long long)*(uint64_t *)k, (unsigned long long)*(uint64_t *)v);
        }
    }
    fclose(f);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info, int argc,
                                           char **argv) {
    for (int i = 0; i < argc; i++) {
        if (!strncmp(argv[i], "prof=", 5)) {
            prof = argv[i] + 5;
        }
    }
    pcs = g_hash_table_new(g_int64_hash, g_int64_equal);
    count = qemu_plugin_scoreboard_u64(qemu_plugin_scoreboard_new(sizeof(uint64_t)));
    qemu_plugin_register_vcpu_init_cb(id, on_vcpu_init, NULL);
    qemu_plugin_register_vcpu_tb_trans_cb(id, on_tb, NULL);
    qemu_plugin_register_atexit_cb(id, at_exit, NULL);
    return 0;
}
