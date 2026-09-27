#!/usr/bin/env python3
"""Exercise the actual unsigned-128 division kernels against independent answers.

CPU execution evidence, not an ISA proof. Zero divisors are outside the contract.
"""
from pathlib import Path
import os
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
WORD = (1 << 64) - 1
MAX = (1 << 128) - 1


def vectors():
    pairs = set()

    def add(a, d):
        if 0 <= a <= MAX and 0 < d <= MAX:
            pairs.add((a, d))

    for bit in range(128):
        for d in ((1 << bit) - 1, 1 << bit, (1 << bit) + 1):
            if not 0 < d <= MAX:
                continue
            for a in (0, 1, d - 1, d, d + 1, MAX - 1, MAX):
                add(a, d)
            for q in (1, 2, 3, (1 << 32) - 1, 1 << 32, WORD, 1 << 64):
                for r in (0, 1, d // 2, d - 1):
                    add(q * d + r, d)
            if d <= WORD:
                for hi in (0, d - 1, d, d + 1, WORD):
                    for lo in (0, 1, (1 << 63) - 1, 1 << 63, WORD):
                        add((hi << 64) | lo, d)

    rng = random.Random(0)
    for _ in range(20000):
        a = rng.getrandbits(128)
        # Full-width random pairs alone underexercise single-limb divisors.
        d = rng.getrandbits(rng.choice((8, 32, 64, 96, 128))) or 1
        add(a, d)
    return sorted(pairs)


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    pairs = vectors()
    with tempfile.TemporaryDirectory(prefix="ssz-division-") as directory:
        temp = Path(directory)
        rows = []
        for a, d in pairs:
            q = a // d
            words = (a & WORD, a >> 64, d & WORD, d >> 64, q & WORD, q >> 64)
            rows.append("    {" + ",".join(f"0x{word:016x}ULL" for word in words) + "},")
        (temp / "division-vectors.h").write_text(
            "static const DivisionCase cases[] = {\n" + "\n".join(rows) + "\n};\n")
        sysroot = subprocess.check_output(["rustc", "+1.94.0", "--print", "sysroot"], text=True).strip()
        linker = Path(sysroot) / "lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld"
        os.symlink(linker, temp / "ld.lld")
        flags = ["-O2", "-ffreestanding", "-fno-builtin", "-fno-stack-protector", "-fno-pie",
                 "-ffunction-sections", "-fdata-sections", f"-I{temp}"]
        for arch, compiler, runner in (("x86", ["cc"], []),
                ("arm", ["clang-18", "--target=aarch64-unknown-linux-gnu"], ["qemu-aarch64-static"])):
            binary = temp / arch
            link_flags = [] if arch == "x86" else ["-fuse-ld=lld", f"-B{temp}"]
            run(*compiler, *link_flags, *flags, "-nostdlib", "-static",
                "-Wl,--gc-sections,--no-undefined,-e,_start",
                str(ROOT / "native-ffi/tests/division.c"),
                str(ROOT / "native-ffi/tests/runtime.c"),
                str(ROOT / f"asm/{arch}/udivti3.s"), "-o", str(binary))
            subprocess.run([*runner, str(binary)], check=True, timeout=180)
            print(f"{arch}: actual __udivti3 passed {len(pairs)} full-width answers and 65280 word cases", flush=True)


if __name__ == "__main__":
    main()
