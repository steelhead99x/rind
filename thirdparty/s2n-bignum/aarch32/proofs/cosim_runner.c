/*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* The AArch32 cosimulation executor: a freestanding static Linux program that
 * speaks common/cosim.ml's protocol 1 on its standard input and output, and
 * runs each instruction with cosim_start.S. A request's state words are
 *
 *   0-12   R0-R12
 *   13     LR
 *   14-17  N, Z, C, and V, each 0 or 1
 *   18     SP's offset into the scratch buffer
 *   19     PC's offset from the instruction, 0 on input
 *   20-83  the scratch buffer's 64 words
 *
 * and the reply's are the same after the instruction runs. SP points into the
 * 256-byte scratch buffer, so an instruction under test reaches memory only
 * through SP; the other registers take any value. A malformed request gets
 * ERROR, and a fault kills the executor, which the client reports. */

typedef unsigned int u32;

#define STATE_WORDS 84
#define SCRATCH_WORDS 64

extern u32 cosim_state[17];
extern u32 cosim_slot[1];
extern void cosim_enter(void);

static u32 scratch[SCRATCH_WORDS] __attribute__((aligned(256)));

static long syscall3(long number, long a, long b, long c) {
    register long r7 __asm__("r7") = number;
    register long r0 __asm__("r0") = a;
    register long r1 __asm__("r1") = b;
    register long r2 __asm__("r2") = c;
    __asm__ volatile("svc #0" : "+r"(r0) : "r"(r7), "r"(r1), "r"(r2) : "memory");
    return r0;
}

#define SYS_READ 3
#define SYS_WRITE 4
#define SYS_CACHEFLUSH 0x0f0002

static char input[4096];
static long input_start, input_end;

/* Reads one line into `line`, without its newline, returning its length, or
 * -1 at the end of the input or for a line longer than `size`. */
static long read_line(char *line, long size) {
    long length = 0;
    for (;;) {
        if (input_start == input_end) {
            long count = syscall3(SYS_READ, 0, (long)input, sizeof input);
            if (count <= 0) return -1;
            input_start = 0;
            input_end = count;
        }
        char c = input[input_start++];
        if (c == '\n') return length;
        if (length == size) return -1;
        line[length++] = c;
    }
}

static char output[2048];
static long output_length;

static void put(const char *text) {
    while (*text && output_length < (long)sizeof output) output[output_length++] = *text++;
}

static void put_u32(u32 value) {
    char digits[10];
    int count = 0;
    do {
        digits[count++] = (char)('0' + value % 10);
        value /= 10;
    } while (value);
    while (count && output_length < (long)sizeof output) output[output_length++] = digits[--count];
}

static void flush(void) {
    long done = 0;
    while (done < output_length) {
        long count = syscall3(SYS_WRITE, 1, (long)(output + done), output_length - done);
        if (count <= 0) break;
        done += count;
    }
    output_length = 0;
}

static int hex_digit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* Parses the space-separated request after "RUN ": four instruction bytes in
 * hex, then the state words in decimal. Returns 0 unless it is well formed. */
static int parse_request(const char *p, const char *end, u32 *instruction, u32 *state) {
    u32 word = 0;
    for (int i = 0; i < 4; i++) {
        if (end - p < 2) return 0;
        int high = hex_digit(p[0]), low = hex_digit(p[1]);
        if (high < 0 || low < 0) return 0;
        word |= (u32)(high * 16 + low) << (8 * i);
        p += 2;
    }
    *instruction = word;
    for (int i = 0; i < STATE_WORDS; i++) {
        if (p == end || *p != ' ') return 0;
        p++;
        if (p == end || *p < '0' || *p > '9') return 0;
        unsigned long long value = 0;
        while (p != end && *p >= '0' && *p <= '9') {
            value = value * 10 + (unsigned long long)(*p - '0');
            if (value > 0xffffffffull) return 0;
            p++;
        }
        state[i] = (u32)value;
    }
    return p == end;
}

static int run(u32 instruction, u32 *state) {
    for (int i = 14; i < 18; i++)
        if (state[i] > 1) return 0;
    if (state[18] > 4 * SCRATCH_WORDS || state[18] % 4 || state[19] != 0) return 0;
    for (int i = 0; i < 14; i++) cosim_state[i] = state[i];
    cosim_state[14] = state[14] << 31 | state[15] << 30 | state[16] << 29 | state[17] << 28;
    cosim_state[15] = (u32)(unsigned long)scratch + state[18];
    for (int i = 0; i < SCRATCH_WORDS; i++) scratch[i] = state[20 + i];
    cosim_slot[0] = instruction;
    syscall3(SYS_CACHEFLUSH, (long)cosim_slot, (long)(cosim_slot + 1), 0);
    cosim_enter();
    for (int i = 0; i < 14; i++) state[i] = cosim_state[i];
    for (int i = 0; i < 4; i++) state[14 + i] = cosim_state[14] >> (31 - i) & 1;
    state[18] = cosim_state[15] - (u32)(unsigned long)scratch;
    state[19] = cosim_state[16];
    for (int i = 0; i < SCRATCH_WORDS; i++) state[20 + i] = scratch[i];
    return 1;
}

int cosim_main(void) {
    static char line[2048];
    static u32 state[STATE_WORDS];
    put("READY 1 aarch32 84\n");
    flush();
    for (;;) {
        long length = read_line(line, sizeof line);
        if (length < 0) return 1;
        if (length == 4 && line[0] == 'Q' && line[1] == 'U' && line[2] == 'I' && line[3] == 'T') return 0;
        u32 instruction;
        if (length < 4 || line[0] != 'R' || line[1] != 'U' || line[2] != 'N' || line[3] != ' ' ||
            !parse_request(line + 4, line + length, &instruction, state) || !run(instruction, state)) {
            put("ERROR malformed request\n");
            flush();
            continue;
        }
        put("OK");
        for (int i = 0; i < STATE_WORDS; i++) {
            put(" ");
            put_u32(state[i]);
        }
        put("\n");
        flush();
    }
}
