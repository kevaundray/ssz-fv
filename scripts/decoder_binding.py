"""Extract actual sparse blocks from pinned native functions and decoder helpers.

This is disassembly/artifact binding, not an execution or reachability proof.
Explicit terminal labels are excluded from the selected instructions; callers
must prove those frontiers unreachable under their machine preconditions.
"""
import json
from pathlib import Path
import re
import subprocess

from native_build import ROOT

FUNCTIONS = {
    "deserialize": {
        "x86": "_ZN13ssz_fv_native5codec11deserialize17h54fc44255b70a5bdE",
        "arm": "_ZN13ssz_fv_native5codec11deserialize17h539c5ca52740cbedE",
    },
    "nat_compare": {
        "x86": "_ZN13ssz_fv_native3nat3Nat7compare17h25caaab0e01dd727E",
        "arm": "_ZN13ssz_fv_native3nat3Nat7compare17h066191a25a9f736bE",
    },
    "decode_delimited": {
        "x86": "_ZN13ssz_fv_native5codec16decode_delimited17h6dfd933a7db96923E",
        "arm": "_ZN13ssz_fv_native5codec16decode_delimited17h0ab2ea8991fd33aeE",
    },
    "nat_add": {
        "x86": "_ZN13ssz_fv_native3nat3Nat3add17h3da88e6260e8092cE",
        "arm": "_ZN13ssz_fv_native3nat3Nat3add17h567a3b65c99417eaE",
    },
    "nat_div_rem_small": {
        "x86": "_ZN13ssz_fv_native3nat3Nat13div_rem_small17h502d1ce340c4e801E",
        "arm": "_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE",
    },
}


def output(*args, cwd=ROOT):
    try:
        return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError as error:
        print(error.output, end="", flush=True)
        raise


def extract(temp, arch, root, entries, terminals=(), calls=()):
    """Select reachable (local label, byte displacement) entries in a FUNCTIONS root.

    Return rows, entry offsets, linked function bytes, reached terminal offsets,
    and reached callee images. Only explicitly named direct callees are allowed.
    Every requested entry and terminal must be an actual instruction boundary.
    """
    symbol = FUNCTIONS[root][arch]
    target = "x86_64-unknown-linux-gnu" if arch == "x86" else "aarch64-linux-gnu"
    objects = []
    for name in ("ssz", "memcpy", "memset", "memcmp", "memmove", "udivti3"):
        obj = temp / f"{arch}-{name}.o"
        output("clang-18", f"--target={target}", "-Wa,-L", "-c",
               f"asm/{arch}/{name}.s", "-o", str(obj))
        objects.append(str(obj))
    libdir = Path(output("rustc", "+1.94.0", "--print", "target-libdir").strip())
    image = temp / f"{arch}.elf"
    output(str(libdir.parent / "bin" / "rust-lld"), "-flavor", "gnu", "-static",
           "--no-undefined", "-e", "0", *objects, "-o", str(image))
    symbols = output("llvm-nm-18", "-S", "--defined-only", str(image)).splitlines()

    def unique_symbol(name):
        matches = [line.split() for line in symbols if line.split()[-1] == name]
        if len(matches) != 1:
            raise ValueError(f"{arch}: missing/ambiguous symbol {name}")
        return matches[0]

    function = unique_symbol(symbol)
    if len(function) != 4 or function[-2] not in ("t", "T"):
        raise ValueError(f"{arch}: expected a sized text function: {function}")
    start, size = int(function[0], 16), int(function[1], 16)
    if size == 0:
        raise ValueError(f"{arch}: empty decoder function")
    entry_offsets = [int(unique_symbol(label)[0], 16) - start + displacement
                     for label, displacement in entries]
    terminal_offsets = {int(unique_symbol(label)[0], 16) - start for label in terminals}
    extent = [f"--start-address={start}", f"--stop-address={start + size}"]
    if arch == "x86":
        text = output("objdump", "-d", "-M", "att,suffix", "--insn-width=15",
                      "--disassemble-zeroes", *extent, str(image))
        pattern = r"\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)(\S.*)"
    else:
        text = output("llvm-objdump-18", "-d", "--disassemble-zeroes", *extent, str(image))
        pattern = r"\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S.*)"
    sections = re.split(r"^Disassembly of section ([^:]+):\n", text, flags=re.M)
    decoded_sections = [(sections[i], sections[i + 1])
                        for i in range(1, len(sections), 2)
                        if re.search(r"^\s*[0-9a-f]+:\s", sections[i + 1], re.M)]
    if len(decoded_sections) != 1:
        raise ValueError(f"{arch}: expected one disassembled function section")
    section, text = decoded_sections[0]
    headers = json.loads(output("llvm-readobj-18", "--sections", "--elf-output-style=JSON", str(image)))
    matching = [item["Section"] for item in headers[0]["Sections"]
                if item["Section"]["Name"]["Name"] == section]
    if len(matching) != 1:
        raise ValueError(f"{arch}: missing/ambiguous linked section {section}")
    section_start = matching[0]["Address"]
    raw_path = temp / f"{arch}.bin"
    output("llvm-objcopy-18", f"--dump-section={section}={raw_path}", str(image),
           str(temp / f"{arch}-copy.elf"))
    section_bytes = raw_path.read_bytes()

    def code_bytes(address, length):
        offset = address - section_start
        if offset < 0 or length <= 0 or offset + length > len(section_bytes):
            raise ValueError(f"{arch}: function outside linked section: {address}/{length}")
        return section_bytes[offset:offset + length]

    raw = code_bytes(start, size)
    callees, call_targets, reached_calls = {}, {}, set()
    for name in calls:
        callee = unique_symbol(name)
        if len(callee) != 4 or callee[-2] not in ("t", "T"):
            raise ValueError(f"{arch}: expected a sized callee: {callee}")
        address, length = int(callee[0], 16), int(callee[1], 16)
        call_targets[address - start] = name
        callees[name] = {"offset": address - start, "size": length,
                         "raw": code_bytes(address, length).hex()}
    rows, end = {}, 0
    for line in text.splitlines():
        if not re.match(r"\s*[0-9a-f]+:", line):
            continue
        match = re.fullmatch(pattern, line)
        if match is None:
            raise ValueError(f"{arch}: unparsed instruction: {line}")
        pc = int(match[1], 16) - start
        encoded = (bytes.fromhex(match[2]) if arch == "x86"
                   else int(match[2], 16).to_bytes(4, "little"))
        if pc != end or raw[pc:pc + len(encoded)] != encoded:
            raise ValueError(f"{arch}: disassembly/raw-byte extent mismatch at {pc}")
        rows[pc] = {"pc": pc, "width": len(encoded), "encoding": match[2].strip(), "asm": match[3].strip()}
        end += len(encoded)
    if end != size:
        raise ValueError(f"{arch}: disassembly does not cover function")
    for pc in [*entry_offsets, *terminal_offsets]:
        if pc not in rows:
            raise ValueError(f"{arch}: entry/terminal is not an instruction boundary: {pc}")
    pending, visited, reached = list(entry_offsets), set(), set()
    while pending:
        pc = pending.pop()
        if pc in terminal_offsets:
            reached.add(pc)
            continue
        if pc in visited:
            continue
        if pc not in rows:
            raise ValueError(f"{arch}: decoder edge leaves decoded function: {pc}")
        visited.add(pc)
        row = rows[pc]
        parts = row["asm"].split(None, 1)
        mnemonic, operands = parts[0], parts[1] if len(parts) == 2 else ""
        if arch == "x86" and mnemonic == "addr32":
            # LLD relaxes GOT-indirect calls to six-byte addr32 CALL rel32.
            # Keep the actual bytes/text, but classify the underlying call.
            parts = operands.split(None, 1)
            mnemonic, operands = parts[0], parts[1] if len(parts) == 2 else ""
        if mnemonic in ("ret", "retq"):
            continue
        branch = (mnemonic.startswith("j") if arch == "x86" else
                  mnemonic == "b" or mnemonic.startswith("b.") or mnemonic in ("cbz", "cbnz", "tbz", "tbnz"))
        if branch:
            match = re.search(r"(?:^|,\s*)(?:0x)?([0-9a-f]+)\s*(?:<|$)", operands)
            if match is None:
                raise ValueError(f"{arch}: indirect/unparsed decoder branch: {row}")
            row["target"] = int(match[1], 16) - start
            pending.append(row["target"])
            if mnemonic in ("jmp", "jmpq", "b"):
                continue
        if mnemonic.startswith("call") or mnemonic == "bl":
            match = re.fullmatch(r"(?:0x)?([0-9a-f]+)\s*(?:<[^>]+>)?", operands)
            target = int(match[1], 16) - start if match is not None else None
            if target not in call_targets:
                raise ValueError(f"{arch}: unexpected decoder call: {row}")
            row["target"], row["callee"] = target, call_targets[target]
            reached_calls.add(row["callee"])
        elif mnemonic in ("blr", "br"):
            raise ValueError(f"{arch}: indirect decoder edge: {row}")
        pending.append(pc + row["width"])
    return ([rows[pc] for pc in sorted(visited)], entry_offsets, raw, sorted(reached),
            {name: callees[name] for name in sorted(reached_calls)})


def linked_span(temp, arch, root, raw, callees):
    """Read the actual linked bytes spanning a root and its selected callees.

    The returned origin is relative to the root, as are callee offsets. Gaps
    retain their real bytes rather than inventing executable padding.
    """
    image = temp / f"{arch}.elf"
    symbols = output("llvm-nm-18", "-S", "--defined-only", str(image)).splitlines()
    matches = [line.split() for line in symbols
               if line.split()[-1] == FUNCTIONS[root][arch]]
    if len(matches) != 1:
        raise ValueError(f"{arch}: missing/ambiguous span root")
    start = int(matches[0][0], 16)
    low = min([0, *(callee["offset"] for callee in callees.values())])
    high = max([len(raw), *(callee["offset"] + callee["size"] for callee in callees.values())])
    headers = json.loads(output("llvm-readobj-18", "--sections", "--elf-output-style=JSON", str(image)))
    sections = [item["Section"] for item in headers[0]["Sections"]
                if item["Section"]["Address"] <= start + low
                and start + high <= item["Section"]["Address"] + item["Section"]["Size"]]
    if len(sections) != 1:
        raise ValueError(f"{arch}: root and callees do not occupy one linked section")
    section = sections[0]
    offset = section["Offset"] + start + low - section["Address"]
    span = image.read_bytes()[offset:offset + high - low]
    if len(span) != high - low or span[-low:len(raw) - low] != raw:
        raise ValueError(f"{arch}: linked span/root mismatch")
    for callee in callees.values():
        offset = callee["offset"] - low
        if span[offset:offset + callee["size"]].hex() != callee["raw"]:
            raise ValueError(f"{arch}: linked span/callee mismatch")
    return low, span
