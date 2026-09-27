#!/usr/bin/env python3
"""Run the actual memory kernels and check ordering, overlap, byte/frame semantics.

This is CPU execution evidence; symbolic contracts reside in the ISA backends.
"""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]



def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-memory-") as directory:
        temp = Path(directory)
        sysroot = subprocess.check_output(["rustc", "+1.94.0", "--print", "sysroot"], text=True).strip()
        linker = Path(sysroot) / "lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld"
        os.symlink(linker, temp / "ld.lld")
        flags = ["-O2", "-ffreestanding", "-fno-builtin", "-fno-stack-protector", "-fno-pie",
                 "-ffunction-sections", "-fdata-sections"]
        for arch, compiler, runner in (("x86", ["cc"], []),
                ("arm", ["clang-18", "--target=aarch64-unknown-linux-gnu"], ["qemu-aarch64-static"])):
            runtime = temp / f"{arch}-runtime.o"
            run(*compiler, *flags, "-c",
                str(ROOT / "native-ffi/tests/runtime.c"), "-o", str(runtime))
            binary = temp / arch
            link_flags = [] if arch == "x86" else ["-fuse-ld=lld", f"-B{temp}"]
            run(*compiler, *link_flags, *flags, "-nostdlib", "-static", "-Wl,--gc-sections,--no-undefined,-e,_start",
                str(ROOT / "native-ffi/tests/memory.c"),
                *(str(ROOT / f"asm/{arch}/{kernel}.s") for kernel in ("memcpy", "memset", "memcmp", "memmove")),
                str(runtime), "-o", str(binary))
            subprocess.run([*runner, str(binary)], check=True, timeout=180)
            print(f"{arch}: actual memory-kernel assembly passed", flush=True)


if __name__ == "__main__":
    main()
