#!/usr/bin/env python3
"""Rebuild/bind instruction-lowered SSZ assembly and run it on x86-64 and ARM/QEMU.

Uses all six generated fixture formats from the source revision in
sources.lock.json, published SHA-256 answers, and independent hashlib Merkle
answers. Needs Rust 1.94.0 (x86_64-unknown-none/aarch64-unknown-none),
cc, clang-18, llvm-nm-18, and qemu-aarch64-static.
The C executable supplies real memory intrinsics and Linux entry/exit/write
syscalls: neither an external cross libc sysroot nor runtime stubs are used.
The freestanding Rust targets also supply freestanding integer builtins, avoiding
the hosted AArch64 builtins' unwinder dependency without a fake personality symbol.
This is executable ABI/conformance evidence, not a machine-code proof.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from native_build import ROOT, TARGETS, emit as emit_assembly
FORMATS = {
    "ssz_test": "FIX_CODEC",
    "ssz_json_test": "FIX_JSON",
    "ssz_gindex_test": "FIX_GINDEX",
    "ssz_type_rejection": "FIX_SCHEMA",
    "proof_test": "FIX_PROOF",
    "multiproof_test": "FIX_MULTI",
}


class Number(str):
    """Preserve a parsed JSON numeric token, including exponent and precision."""


class Emitter:
    def __init__(self):
        self.lines = []
        self.serial = 0

    def array(self, ctype, values):
        if not values:
            return "NULL"
        self.serial += 1
        name = f"fixture_data_{self.serial}"
        self.lines.append(f"static const {ctype} {name}[] = {{\n" + ",\n".join(values) + "\n};")
        return name

    def blob(self, data):
        name = self.array("uint8_t", [str(byte) for byte in data])
        return f"{{{name}, {len(data)}}}"

    def tree(self, value):
        if value is None:
            return "{.tag=SSZ_JSON_NULL}"
        if isinstance(value, bool):
            return f"{{.tag=SSZ_JSON_BOOL,.boolean={int(value)}}}"
        if isinstance(value, Number):
            return "{.tag=SSZ_JSON_NUMBER,.text=" + self.blob(value.encode()) + "}"
        if isinstance(value, str):
            return "{.tag=SSZ_JSON_STRING,.text=" + self.blob(value.encode()) + "}"
        if isinstance(value, list):
            name = self.array("ssz_json", [self.tree(item) for item in value])
            return f"{{.tag=SSZ_JSON_ARRAY,.items={name},.item_count={len(value)}}}"
        if isinstance(value, dict):
            fields = ["{" + self.blob(key.encode()) + "," + self.tree(item) + "}"
                      for key, item in value.items()]
            name = self.array("ssz_json_field", fields)
            return f"{{.tag=SSZ_JSON_OBJECT,.fields={name},.field_count={len(fields)}}}"
        raise ValueError(f"unhandled JSON value: {value!r}")

    def nat(self, value):
        number = int(value)
        if number < 0:
            raise ValueError("negative natural fixture claim")
        if number < 1 << 64:
            return f"{{UINT64_C({number}),NULL,0}}"
        limbs = []
        while number:
            limbs.append(f"UINT64_C({number & ((1 << 64) - 1)})")
            number >>= 64
        name = self.array("uint64_t", limbs)
        return f"{{0,{name},{len(limbs)}}}"

    def hex(self, value):
        if value is None:
            return "{NULL,0}"
        if not value.startswith("0x"):
            raise ValueError("fixture bytes lack 0x prefix")
        return self.blob(bytes.fromhex(value[2:]))


def fixtures_header():
    lock = json.loads((ROOT / "sources.lock.json").read_text())["ssz-specs"]
    upstream = ROOT / lock["path"]
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
    if revision != lock["rev"]:
        raise SystemExit(f"fixture source is {revision}, expected pinned {lock['rev']}")
    directory = upstream / "fixtures"
    manifest = json.loads((directory / "manifest.json").read_text())
    paths = sorted(path for path in directory.rglob("*.json")
                   if path.name not in ("index.json", "manifest.json"))
    if not paths or len(paths) != manifest["caseCount"]:
        raise SystemExit("missing/incomplete generated upstream fixtures; generate them first")
    emit = Emitter()
    cases = []
    counts = {kind: 0 for kind in FORMATS}
    max_encoded = 1
    for path in paths:
        data = json.loads(path.read_text(), parse_int=Number, parse_float=Number)
        kind = data["_info"]["fixtureFormat"]
        counts[kind] += 1
        reason = "SSZ_" + data["rejectionReason"] if "rejectionReason" in data else "SSZ_OK"
        values = [f'.name={json.dumps(str(path.relative_to(directory)))}',
                  f'.format={FORMATS[kind]}', f'.valid={int(data["valid"])}',
                  f'.reason={reason}', '.schema=' + emit.tree(data["typeDescriptor"]),
                  '.value=' + emit.tree(data.get("document", data.get("value"))),
                  '.path=' + emit.tree(data.get("path")),
                  '.encoded=' + emit.hex(data.get("serialized")),
                  '.root=' + emit.hex(data.get("root")),
                  '.leaf=' + emit.hex(data.get("leaf")),
                  '.index=' + emit.nat(data.get("index", data.get("gindex", "0")))]
        for field, source, ctype, convert in (
            ("nodes", "branch" if kind == "proof_test" else "proof", "ssz_bytes", emit.hex),
            ("leaves", "leaves", "ssz_bytes", emit.hex),
            ("indices", "indices", "ssz_nat", emit.nat),
            ("paths", "paths", "ssz_json", emit.tree),
        ):
            entries = data.get(source, [])
            array = emit.array(ctype, [convert(item) for item in entries])
            values.extend((f'.{field}={array}', f'.{field}_count={len(entries)}'))
        cases.append("{" + ",".join(values) + "}")
        max_encoded = max(max_encoded, len(data.get("serialized", "0x")) // 2 - 1)
    if not all(counts.values()):
        raise SystemExit("fixture set does not cover all six formats")
    emit.lines.append("static const struct fixture fixtures[] = {\n" + ",\n".join(cases) + "\n};")
    emit.lines.append(f"#define MAX_ENCODED {max_encoded}")

    # Small, direct reference trees independent of the Rust candidate.
    zero = bytes(32)
    pair = lambda left, right: hashlib.sha256(left + right).digest()
    chunks = [bytes([i]) * 32 for i in range(1, 7)]
    bounded = pair(pair(chunks[0], chunks[1]), pair(chunks[2], zero))
    left4 = pair(pair(chunks[1], chunks[2]), pair(chunks[3], chunks[4]))
    last16 = chunks[5]
    padding = zero
    for _ in range(4):
        last16 = pair(last16, padding)
        padding = pair(padding, padding)
    progressive = pair(chunks[0], pair(left4, pair(last16, zero)))
    wide_zero = zero
    for _ in range(75):
        wide_zero = pair(wide_zero, wide_zero)
    wide_list_root = pair(wide_zero, zero)
    for _ in range(5):
        wide_zero = pair(wide_zero, wide_zero)
    for name, answer in (("bounded_answer", bounded), ("progressive_answer", progressive),
                         ("wide_zero_answer", wide_zero), ("wide_list_answer", wide_list_root)):
        emit.lines.append(f"static const uint8_t {name}[32] = {{" + ",".join(map(str, answer)) + "};")
    return "\n".join(emit.lines) + "\n", counts


def run(*args):
    subprocess.run(args, check=True, cwd=ROOT)


def main():
    source, counts = fixtures_header()
    with tempfile.TemporaryDirectory(prefix="ssz-native-") as directory:
        temp = Path(directory)
        (temp / "fixtures.h").write_text(source)
        target_libdir = Path(subprocess.check_output(
            ["rustc", "+1.94.0", "--print", "target-libdir"], text=True).strip())
        linker = temp / "ld.lld"
        linker.symlink_to(target_libdir.parent / "bin/rust-lld")
        common = ["-std=c11", "-O2", "-ffreestanding", "-fno-builtin",
                  "-fno-stack-protector", "-fno-pie", "-nostdlib", "-static",
                  "-I", str(ROOT / "include"), "-I", str(temp),
                  str(ROOT / "native-ffi/tests/smoke.c"),
                  str(ROOT / "native-ffi/tests/runtime.c"),
                  "-Wl,--gc-sections", "-Wl,--no-undefined", "-Wl,-e,_start"]
        for architecture, target in TARGETS:
            compiler = ["cc", "-no-pie"] if architecture == "x86" else [
                "clang-18", "--target=aarch64-linux-gnu", f"-fuse-ld={linker}"]
            runner = [] if architecture == "x86" else ["qemu-aarch64-static"]
            regenerated = temp / f"{architecture}.s"
            emit_assembly(target, regenerated, temp / "cargo")
            shipped = ROOT / "asm" / architecture / "ssz.s"
            if shipped.read_bytes() != regenerated.read_bytes():
                raise SystemExit(f"{shipped}: differs from pinned whole-library build; regenerate with make asm")
            object_file = temp / f"{architecture}.o"
            assembler = ["clang-18"] if architecture == "x86" else ["clang-18", "--target=aarch64-linux-gnu"]
            run(*assembler, "-c", str(shipped), "-o", str(object_file))
            undefined = subprocess.check_output(["llvm-nm-18", "--undefined-only", str(object_file)], text=True)
            dependencies = {line.split()[-1] for line in undefined.splitlines() if line.strip()}
            runtime = {"memcpy", "memmove", "memset", "memcmp", "__udivti3"}
            if dependencies - runtime:
                raise SystemExit(f"{target}: assembly is not self-contained SSZ: {sorted(dependencies - runtime)}")
            # Link only shipped assembly: no SSZ operation or integer builtin
            # can silently fall back to the rebuilt archive.
            binary = temp / target
            run(*compiler, *common,
                *(str(ROOT / "asm" / architecture / f"{kernel}.s")
                  for kernel in ("memcpy", "memset", "memcmp", "memmove", "udivti3")),
                str(object_file), "-o", str(binary))
            run(*runner, str(binary))
            print(f"{target}: shipped assembly bound to Rust + lowering; {sum(counts.values())} pinned fixtures ({counts}); "
                  "SHA answers, raw calculators, Merkle trees, >64-bit metadata, "
                  "proof ordering, false/error results, and resource frames passed", flush=True)


if __name__ == "__main__":
    main()
