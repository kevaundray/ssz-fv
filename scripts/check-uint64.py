#!/usr/bin/env python3
"""Exercise the uint64 assembly, not Rust or a model, on x86 and ARM/QEMU.

Requires generated upstream fixtures, cc, clang-18, Rust 1.94.0's bundled lld,
and qemu-aarch64-static. Checks all alignments, input byte order, and write frames.
These are low-level kernels: rejecting non-eight-byte scopes belongs to callers.
"""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(*args):
    subprocess.run(args, check=True, cwd=ROOT)


def main():
    fixtures = sorted((ROOT / "vendor/ssz-specs/fixtures/ssz/uint64/valid").glob("*.json"))
    if not fixtures:
        raise SystemExit("missing upstream uint64 fixtures; generate them first")
    cases = []
    for path in fixtures:
        item = json.loads(path.read_text())
        encoded = bytes.fromhex(item["serialized"].removeprefix("0x"))
        if not item["valid"] or len(encoded) != 8:
            raise SystemExit(f"unexpected uint64 fixture: {path}")
        cases.append((int(item["value"]), encoded))
    # Distinct bytes detect byte-order mistakes that zero/max fixtures cannot.
    for value in (0x0123456789ABCDEF, 0xFEDCBA9876543210):
        cases.append((value, value.to_bytes(8, "little")))
    values = ",".join(f"0x{value:016x}ULL" for value, _ in cases)
    expected = ",".join("{" + ",".join(map(str, data)) + "}" for _, data in cases)
    source = r'''
#include "ssz_uint64.h"
static const uint64_t values[] = {VALUES};
static const uint8_t expected[][8] = {EXPECTED};
static int check(void) {
    uint8_t memory[40];
    for (unsigned c = 0; c < sizeof(values) / sizeof(values[0]); ++c) {
        for (unsigned offset = 8; offset < 24; ++offset) {
            for (unsigned i = 0; i < sizeof(memory); ++i) memory[i] = 0xa5;
            ssz_store_u64(memory + offset, values[c]);
            for (unsigned i = 0; i < sizeof(memory); ++i) {
                uint8_t want = i >= offset && i < offset + 8 ? expected[c][i-offset] : 0xa5;
                if (memory[i] != want) return 1;
            }
            if (ssz_load_u64(memory + offset) != values[c]) return 2;
            for (unsigned i = 0; i < sizeof(memory); ++i) {
                uint8_t want = i >= offset && i < offset + 8 ? expected[c][i-offset] : 0xa5;
                if (memory[i] != want) return 3;
            }
        }
    }
    // Independently construct every single-bit input, not only store/load round trips.
    for (unsigned bit = 0; bit < 64; ++bit) {
        for (unsigned i = 0; i < 8; ++i) memory[i] = 0;
        memory[bit / 8] = (uint8_t)(1u << (bit % 8));
        if (ssz_load_u64(memory) != (1ULL << bit)) return 4;
    }
    return 0;
}
void _start(void) {
    int result = check();
#if defined(__aarch64__)
    register long status __asm__("x0") = result;
    register long syscall_number __asm__("x8") = 93;
    __asm__ volatile ("svc #0" : : "r"(status), "r"(syscall_number) : "memory");
#elif defined(__x86_64__)
    __asm__ volatile ("syscall" : : "a"(60L), "D"((long)result) : "rcx", "r11", "memory");
#else
#error Unsupported architecture
#endif
    __builtin_unreachable();
}
'''.replace("VALUES", values).replace("EXPECTED", expected)
    with tempfile.TemporaryDirectory(prefix="ssz-uint64-") as directory:
        temp = Path(directory)
        target_libdir = Path(subprocess.check_output(
            ["rustc", "+1.94.0", "--print", "target-libdir"], text=True
        ).strip())
        linker = temp / "ld.lld"
        linker.symlink_to(target_libdir.parent / "bin/rust-lld")
        caller = temp / "caller.c"
        caller.write_text(source)
        common = ["-O2", "-ffreestanding", "-fno-builtin", "-fno-stack-protector", "-nostdlib", "-static", "-I", str(ROOT / "include"), str(caller)]
        for isa, compiler, runner in (
            ("x86", ["cc", "-fno-pie", "-no-pie"], []),
            ("arm", ["clang-18", "--target=aarch64-linux-gnu", f"-fuse-ld={linker}"], ["qemu-aarch64-static"]),
        ):
            binary = temp / isa
            run(*compiler, *common, str(ROOT / f"asm/{isa}/uint64.s"), "-o", str(binary))
            run(*runner, str(binary))
            print(f"{isa}: {len(fixtures)} upstream cases, byte-order cases, 16 offsets, single-bit loads and memory frames passed", flush=True)


if __name__ == "__main__":
    main()
