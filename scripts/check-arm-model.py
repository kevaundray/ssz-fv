#!/usr/bin/env python3
"""Compare raw logical-immediate words in A64/QEMU and LNSym with bitwise results.

Does not prepare, patch, or otherwise change the pinned model. Run once before
and once after `make prepare-models`; the former must expose the Rn31 bug.
The generated Lean program imports only Arm.Exec, not the fixed-model theorem.
"""
from pathlib import Path
import struct
import subprocess
import tempfile

from native_build import ROOT


# 64-bit cases include the exact SSZ word 0xb27fefe9, whose immediate is
# 0x1ffffffffffffffe. The 32-bit mask also exercises the negative ANDS flag.
CASES = []
for width, immr, imms, mask in (
        (64, 63, 59, 0x1FFFFFFFFFFFFFFE),
        (32, 1, 28, 0x8FFFFFFF)):
    for opc, name in enumerate(("AND", "ORR", "EOR", "ANDS")):
        for rn in (31, 1):
            for rd in (9, 31):
                word = ((int(width == 64) << 31) | (opc << 29) | 0x12000000
                        | (int(width == 64) << 22) | (immr << 16)
                        | (imms << 10) | (rn << 5) | rd)
                CASES.append((word, width, opc, rn, rd, mask,
                              f"{name}{width} Rn={rn} Rd={rd}"))

# Both controlled stack values have high bits outside the actual SSZ mask.
# The real stack is restored before any memory operation or syscall.
SAMPLES = (
    (0xE123456789ABCDE0, 0xFFFFFFFFFFFFFFFF),
    (0xFEDCBA9876543210, 0xFEDCBA9887654321),
    (0xE123456789ABCDE0, 0),
    (0xFEDCBA9876543210, 0x000000000FFFFFFF),
)
SENTINEL = 0x0123456789ABCDEF


def expected(case, sp, source, flags):
    _, width, opc, rn, rd, mask, _ = case
    source = (0 if rn == 31 else source) & ((1 << width) - 1)
    result = (source & mask, source | mask, source ^ mask, source & mask)[opc]
    nzcv = flags
    if opc == 3:
        nzcv = ((result >> (width - 1)) << 3) | (int(result == 0) << 2)
    return (result if rd == 9 else SENTINEL,
            result if rd == 31 and opc != 3 else sp, nzcv)


def native_sources():
    assembly = [".text"]
    for index, (word, *_rest) in enumerate(CASES):
        assembly.append(f"""
.global case_{index}
.type case_{index}, %function
case_{index}:
    mov x16, sp
    movz x9, #0xcdef
    movk x9, #0x89ab, lsl #16
    movk x9, #0x4567, lsl #32
    movk x9, #0x0123, lsl #48
    msr nzcv, x2
    mov sp, x0
    .inst 0x{word:08x}
    mov x10, sp
    mrs x11, nzcv
    mov sp, x16
    stp x9, x10, [x3]
    lsr x11, x11, #28
    str x11, [x3, #16]
    ret
.size case_{index}, .-case_{index}
""")
    declarations = "\n".join(
        f"extern void case_{i}(uint64_t, uint64_t, uint64_t, uint64_t *);"
        for i in range(len(CASES)))
    functions = ",".join(f"case_{i}" for i in range(len(CASES)))
    samples = ",".join(f"{{{sp}ULL,{source}ULL}}" for sp, source in SAMPLES)
    source = f"""#include <stdint.h>
#include <stddef.h>
extern void smoke_write(const char *, size_t);
{declarations}
static void (*const cases[])(uint64_t,uint64_t,uint64_t,uint64_t *) = {{{functions}}};
static const uint64_t samples[][2] = {{{samples}}};
int smoke_main(void) {{
    uint64_t output[3];
    for (unsigned c = 0; c < {len(CASES)}; ++c)
        for (unsigned s = 0; s < {len(SAMPLES)}; ++s)
            for (unsigned f = 0; f < 16; ++f) {{
                cases[c](samples[s][0], samples[s][1], (uint64_t)f << 28, output);
                smoke_write((const char *)output, sizeof(output));
            }}
    return 0;
}}
"""
    return "\n".join(assembly), source


def model_source():
    words = ", ".join(f"0x{case[0]:08x}" for case in CASES)
    samples = ", ".join(f"({sp}, {source})" for sp, source in SAMPLES)
    return f"""import Arm.Exec

private def initial (sp source flags : Nat) : ArmState :=
  write_gpr 64 31#5 (BitVec.ofNat 64 sp) <|
  write_gpr 64 1#5 (BitVec.ofNat 64 source) <|
  write_gpr 64 9#5 {SENTINEL}#64 <|
  write_pstate (make_pstate (BitVec.ofNat 1 (flags / 8))
    (BitVec.ofNat 1 (flags / 4)) (BitVec.ofNat 1 (flags / 2))
    (BitVec.ofNat 1 flags)) ArmState.default

def main : IO Unit := do
  let words : List Nat := [{words}]
  let samples : List (Nat × Nat) := [{samples}]
  for word in words do
    for (sp, source) in samples do
      for flags in List.range 16 do
        let some instruction := decode_raw_inst (BitVec.ofNat 32 word)
          | throw (IO.userError s!"decode failed: {{word}}")
        let state := exec_inst instruction (initial sp source flags)
        unless read_err state == .None do
          throw (IO.userError s!"model error: {{reprStr (read_err state)}}")
        unless read_pc state == 4#64 do
          throw (IO.userError "model did not advance PC")
        let nzcv := (read_flag .N state).toNat * 8 +
          (read_flag .Z state).toNat * 4 +
          (read_flag .C state).toNat * 2 + (read_flag .V state).toNat
        IO.println s!"RESULT {{(read_gpr 64 9#5 state).toNat}} {{(read_gpr 64 31#5 state).toNat}} {{nzcv}}"
"""


def main():
    count = len(CASES) * len(SAMPLES) * 16
    with tempfile.TemporaryDirectory(prefix="ssz-arm-model-") as directory:
        temp = Path(directory)
        assembly, source = native_sources()
        (temp / "cases.s").write_text(assembly)
        (temp / "main.c").write_text(source)
        (temp / "Model.lean").write_text(model_source())
        libdir = Path(subprocess.check_output(
            ["rustc", "+1.94.0", "--print", "target-libdir"], text=True).strip())
        linker = temp / "ld.lld"
        linker.symlink_to(libdir.parent / "bin/rust-lld")
        subprocess.run([
            "clang-18", "--target=aarch64-linux-gnu", f"-fuse-ld={linker}",
            "-std=c11", "-O2", "-ffreestanding", "-fno-builtin",
            "-fno-stack-protector", "-fno-pie", "-nostdlib", "-static",
            str(temp / "main.c"), str(temp / "cases.s"),
            str(ROOT / "native-ffi/tests/runtime.c"),
            "-Wl,--no-undefined", "-Wl,-e,_start", "-o", str(temp / "check"),
        ], check=True)
        native = subprocess.run(["qemu-aarch64-static", str(temp / "check")],
                                check=True, capture_output=True, timeout=120)
        if len(native.stderr) != count * 24:
            raise RuntimeError(f"native output size {len(native.stderr)} != {count * 24}: "
                               f"{native.stderr[:200]!r}")
        native_rows = list(struct.iter_unpack("<QQQ", native.stderr))
        expected_rows = [expected(case, sp, source, flags)
                         for case in CASES for sp, source in SAMPLES
                         for flags in range(16)]
        check_rows("A64/QEMU", native_rows, expected_rows)
        print(f"PASS A64/QEMU: {count} executions, {len(CASES)} raw words", flush=True)
        backend = ROOT / "backends/arm"
        # Build only the upstream execution module: the fixed-model regression
        # theorem and the root library intentionally need not build on RED.
        subprocess.run(["lake", "--log-level=error", "build", "Arm.Exec"],
                       cwd=backend, check=True)
        model = subprocess.run(["lake", "env", "lean", "--run", str(temp / "Model.lean")],
                               cwd=backend, capture_output=True, text=True, timeout=120)
        if model.returncode:
            raise RuntimeError(f"Lean model runner failed:\n{model.stdout}\n{model.stderr}")
        rows = [tuple(map(int, line.split()[1:]))
                for line in model.stdout.splitlines() if line.startswith("RESULT ")]
        if len(rows) != count:
            raise RuntimeError(f"expected {count} model results, got {len(rows)}:\n{model.stdout}")
        check_rows("LNSym exec_inst/raw decode", rows, expected_rows)
        print(f"PASS LNSym/native/architectural agreement: {count} executions; "
              "Rn31, both widths, destination SP/ZR, all NZCV inputs and Rn1 controls")


def check_rows(label, rows, expected_rows):
    mismatches = []
    for index, (actual, wanted) in enumerate(zip(rows, expected_rows)):
        if actual != wanted:
            case = CASES[index // (len(SAMPLES) * 16)]
            sample = SAMPLES[(index // 16) % len(SAMPLES)]
            mismatches.append(
                f"{case[6]} word=0x{case[0]:08x} SP=0x{sample[0]:016x} "
                f"Rn1=0x{sample[1]:016x} NZCV={index % 16:x}: "
                f"actual={tuple(hex(x) for x in actual)} "
                f"expected={tuple(hex(x) for x in wanted)}")
    if mismatches:
        # Include one line per affected raw word, notably the actual SSZ opcode.
        unique = {}
        for row in mismatches:
            unique.setdefault(row.split(" SP=")[0], row)
        raise RuntimeError(f"FAIL {label}: {len(mismatches)} mismatches\n" +
                           "\n".join(unique.values()))


if __name__ == "__main__":
    main()
