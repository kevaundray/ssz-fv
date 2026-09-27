#!/usr/bin/env python3
"""Differentially execute original/lowered ARM instructions on QEMU.

Checks architectural results, all NZCV bits, non-destination GPRs, SP, and
ordinary-memory effects. This is hardware-model-independent regression evidence,
not a proof of the lowering pass or of SSZ.
"""
from pathlib import Path
import json
import subprocess
import tempfile

from lower_arm import lower
from native_build import ROOT

# mode: 1 ordinary memory, 2 signed memory index, 3 bounded SP destination.
# stack_bytes: trailing bytes below incoming SP that the original instruction uses.
CASES = [(op, 0, 0) for op in [
    "clz x0, x1", "clz x1, x1", "clz w0, w1", "rbit x0, x1", "rbit w1, w1",
    "umulh x0, x1, x2", "umulh x1, x1, x2", "umulh x2, x1, x2", "umulh x1, x1, x1",
    "smulh x0, x1, x2", "smulh x1, x1, x1", "msub x1, x1, x2, x3",
    "msub w3, w1, w2, w3", "mneg x2, x1, x2", "umull x1, w1, w2",
    "smull x2, w1, w2", "umaddl x3, w1, w2, x3", "smaddl x1, w1, w2, x3",
    "umsubl x1, w1, w2, x1", "smsubl x2, w1, w2, x2",
    "extr x1, x1, x2, #0", "extr x1, x1, x2, #63", "extr w2, w1, w2, #7",
    "ror x1, x1, #29", "ror w0, w1, #1", "udiv x0, x1, x2", "udiv w2, w1, w2",
    "add x1, x1, w2, sxtw #3", "adds x2, x1, w2, uxtw #2",
    "subs x1, x1, w2, sxth", "cmp x1, w2, sxtw", "cmn x1, w2, uxtw",
    "add x0, sp, w1, uxtw #2", "sub x0, sp, w1, sxtw #1",
]]
for cond in ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le"]:
    CASES.extend((op, 0, 0) for op in [
        f"cset w0, {cond}", f"csetm x0, {cond}", f"csinc x1, x1, x2, {cond}",
        f"csinv w2, w1, w2, {cond}", f"csneg x1, x1, x1, {cond}",
        f"ccmp x1, x2, #0, {cond}", f"ccmn w1, #7, #4, {cond}",
    ])
for literal in [0, 2, 3, 4, 6, 7, 8, 9, 10]:
    CASES.append((f"ccmp xzr, x1, #{literal}, eq", 0, 0))
for opcode, reg, bit in [("tbz", "x1", 63), ("tbnz", "w1", 0), ("tbz", "w1", 31)]:
    CASES.append((f"{opcode} {reg}, #{bit}, @TAKEN\nmov x0, #17\nb @DONE\n@TAKEN:\nmov x0, #29\n@DONE:", 0, 0))
CASES.extend([(op, 1, 0) for op in [
    "ldrh w0, [x1]", "ldrh w1, [x1, x2]", "strh w0, [x1, x2, lsl #1]",
    "ldrsb x0, [x1]", "ldrsb w0, [x1, x2]", "ldrsh x0, [x1, #1]",
    "ldrsw x0, [x1]", "ldur x0, [x1, #-8]", "stur x0, [x1, #-8]",
    "ldrb w0, [x1, #1]!", "strb w0, [x1, #-1]!", "str xzr, [x1], #8",
    "ldrb wzr, [x1]", "stp xzr, x0, [x1]", "ldp xzr, x0, [x1]",
    "ldpsw xzr, x0, [x1]",
]])
CASES.extend([
    ("ldrh w0, [x1, w2, sxtw #1]", 2, 0),
    ("ldr x0, [x1, w2, sxtw #3]", 2, 0),
    ("add sp, sp, x1", 3, 0), ("sub sp, sp, w1, uxtw", 3, 0),
    ("ldurh w0, [sp, #-2]", 0, 2), ("strh w0, [sp, #-2]", 0, 2),
    ("stp xzr, xzr, [sp, #-16]!", 0, 16),
])


def body(index, original, instruction):
    name = f"{'original' if original else 'lowered'}_{index}"
    instruction = instruction.replace("@TAKEN", f".Ltaken_{name}").replace("@DONE", f".Ldone_{name}")
    return f".global {name}\n.type {name},%function\n{name}:\n.Lbegin_{name}:\n{instruction}\n.Lend_{name}:\n"


# The monitor is not lowered: MSR/MRS deliberately inspect physical NZCV.
PROLOGUE = """
sub sp, sp, #64
stp x19, x20, [sp]
stp x21, x22, [sp, #16]
stp x23, x30, [sp, #32]
mov x19, x0
mov x20, x1
mov x22, sp
ldp x21, x23, [x19]
stp x21, x23, [sp, #-16]
ldr x21, [x19, #144]
msr nzcv, x21
""" + "".join(f"ldp x{i}, x{i+1}, [x19, #{i*8}]\n" for i in range(0, 18, 2))
EPILOGUE = "".join(f"stp x{i}, x{i+1}, [x20, #{i*8}]\n" for i in range(0, 18, 2)) + """
mrs x23, nzcv
str x23, [x20, #144]
mov x23, sp
str x23, [x20, #152]
ldp x21, x23, [x22, #-16]
stp x21, x23, [x20, #160]
mov sp, x22
ldp x23, x30, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp]
add sp, sp, #64
ret
"""


def main():
    snippets = "".join(body(i, False, op) for i, (op, _, _) in enumerate(CASES))
    assembly = ".text\n" + lower(snippets) + "".join(body(i, True, op) for i, (op, _, _) in enumerate(CASES))
    for i in range(len(CASES)):
        for prefix in ["original", "lowered"]:
            name = f"{prefix}_{i}"
            assembly = assembly.replace(f".Lbegin_{name}:\n", f".Lbegin_{name}:\n{PROLOGUE}")
            assembly = assembly.replace(f".Lend_{name}:\n", f".Lend_{name}:\n{EPILOGUE}")
    declarations = "\n".join(f"extern void {prefix}_{i}(const uint64_t *, uint64_t *);" for i in range(len(CASES)) for prefix in ["original", "lowered"])
    rows = ",\n".join(f"{{original_{i},lowered_{i},{mode},{stack},{json.dumps(op)}}}" for i, (op, mode, stack) in enumerate(CASES))
    source = """#include <stdint.h>
#include <stddef.h>
void smoke_write(const char *, size_t);
""" + declarations + """
typedef void (*operation)(const uint64_t *, uint64_t *);
static struct { operation original, lowered; unsigned mode, stack; const char *name; } cases[] = {
""" + rows + """
};
static uint64_t input[19], expected[22], actual[22];
static unsigned char memory[256], saved[256];
static const uint64_t edge[] = {0,1,2,0x7fffffffffffffffULL,0x8000000000000000ULL,~0ULL,0xffffffffULL,0x80000000ULL,0xffff0000ffff0000ULL};
static uint64_t random_state=0x3a59ec71942bd605ULL;
static uint64_t next(void) { random_state^=random_state<<13; random_state^=random_state>>7; random_state^=random_state<<17; return random_state; }
static void fill(unsigned sample) { for(unsigned j=0;j<256;j++) memory[j]=(unsigned char)((j*37)^(sample*19)); }
static int fail(const char *name) { size_t n=0; while(name[n])n++; smoke_write(name,n); smoke_write(" : lowering state mismatch\\n",27); return 1; }
int smoke_main(void) {
 for(unsigned c=0;c<sizeof(cases)/sizeof(cases[0]);c++)
  for(unsigned sample=0;sample<41;sample++) for(unsigned flags=0;flags<16;flags++) {
   for(unsigned j=0;j<18;j++) input[j]=sample<9?edge[(sample+j)%9]:next();
   input[18]=(uint64_t)flags<<28;
   if(cases[c].mode==1 || cases[c].mode==2) { input[1]=(uintptr_t)(memory+96); input[2]=cases[c].mode==2?(uint64_t)-2:2; }
   if(cases[c].mode==3) input[1]=(sample%3)*16;
   fill(sample); cases[c].original(input,expected);
   for(unsigned j=0;j<256;j++) saved[j]=memory[j];
   fill(sample); cases[c].lowered(input,actual);
   for(unsigned j=0;j<20;j++) if(expected[j]!=actual[j]) return fail(cases[c].name);
   for(unsigned j=0;j<256;j++) if(saved[j]!=memory[j]) return fail(cases[c].name);
   const unsigned char *a=(const unsigned char *)(actual+20), *b=(const unsigned char *)(expected+20);
   for(unsigned j=16-cases[c].stack;j<16;j++) if(a[j]!=b[j]) return fail(cases[c].name);
  }
 const char done[]="ARM lowering operand/flag/frame checks passed\\n";
 smoke_write(done,sizeof(done)-1); return 0;
}
"""
    with tempfile.TemporaryDirectory(prefix="ssz-arm-lowering-") as directory:
        temp = Path(directory)
        (temp / "cases.s").write_text(assembly)
        (temp / "main.c").write_text(source)
        libdir = Path(subprocess.check_output(["rustc", "+1.94.0", "--print", "target-libdir"], text=True).strip())
        linker = temp / "ld.lld"
        linker.symlink_to(libdir.parent / "bin/rust-lld")
        subprocess.run(["clang-18", "--target=aarch64-linux-gnu", f"-fuse-ld={linker}", "-std=c11", "-O2", "-ffreestanding", "-fno-builtin", "-fno-stack-protector", "-fno-pie", "-nostdlib", "-static", str(temp / "main.c"), str(temp / "cases.s"), str(ROOT / "native-ffi/tests/runtime.c"), *(str(ROOT / f"asm/arm/{kernel}.s") for kernel in ("memcpy", "memset", "memcmp", "memmove")), "-Wl,--no-undefined", "-Wl,-e,_start", "-o", str(temp / "check")], check=True)
        subprocess.run(["qemu-aarch64-static", str(temp / "check")], check=True, timeout=120)
    print(f"{len(CASES)*41*16} original/lowered executions agree on results, NZCV, registers, SP and addressed memory")


if __name__ == "__main__":
    main()
