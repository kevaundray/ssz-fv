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
    "nat_mul": {
        "x86": "_ZN13ssz_fv_native3nat3Nat3mul17ha2639a6aac923654E",
        "arm": "_ZN13ssz_fv_native3nat3Nat3mul17h5dc2c96f405496c8E",
    },
    "nat_mul_word": {
        "x86": "_ZN13ssz_fv_native3nat3Nat8mul_word17h0294313f2dc52cdfE",
        "arm": "_ZN13ssz_fv_native3nat3Nat8mul_word17h44eb4fbc8039a355E",
    },
    "nat_div_rem_small": {
        "x86": "_ZN13ssz_fv_native3nat3Nat13div_rem_small17h502d1ce340c4e801E",
        "arm": "_ZN13ssz_fv_native3nat3Nat13div_rem_small17he8c5c3bc7904fc5eE",
    },
    "nat_exact": {
        "x86": "_ZN13ssz_fv_native5codec5exact17h76158baa639106f6E",
        "arm": "_ZN13ssz_fv_native5codec5exact17hfce8663ef07a8e63E",
    },
    "nat_to_u128": {
        "x86": "_ZN13ssz_fv_native3nat3Nat7to_u12817h3fd207ea42c40ccfE",
        "arm": "_ZN13ssz_fv_native3nat3Nat7to_u12817h7b219376ab6746a8E",
    },
    "nat_from_u128": {
        "x86": "_ZN13ssz_fv_native3nat3Nat9from_u12817h8b0aeba422536ff0E",
        "arm": "_ZN13ssz_fv_native3nat3Nat9from_u12817h73292f97725c3b7dE",
    },
    "measure": {
        "x86": "_ZN13ssz_fv_native5codec7measure17hee937c471e44009dE",
        "arm": "_ZN13ssz_fv_native5codec7measure17h6f170d30c3984362E",
    },
    "emit": {
        "x86": "_ZN13ssz_fv_native5codec4emit17h6ae700472ba785eaE",
        "arm": "_ZN13ssz_fv_native5codec4emit17h0c79599762be27eaE",
    },
    "serialize": {
        "x86": "_ZN13ssz_fv_native5codec9serialize17h73686b9835ba9d12E",
        "arm": "_ZN13ssz_fv_native5codec9serialize17h0d728b7a742b35d3E",
    },
    "measure_parts": {
        "x86": "_ZN13ssz_fv_native5codec13measure_parts17he5c844ee13389e6aE",
        "arm": "_ZN13ssz_fv_native5codec13measure_parts17h3804244188cbc0c8E",
    },
    "measure_child": {
        "x86": "_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17h373c75853d801feeE",
        "arm": "_ZN13ssz_fv_native5codec13measure_parts28_$u7b$$u7b$closure$u7d$$u7d$17hbcad779f9c302ea9E",
    },
    "emit_parts": {
        "x86": "_ZN13ssz_fv_native5codec10emit_parts17hb772d37971238413E",
        "arm": "_ZN13ssz_fv_native5codec10emit_parts17h64cc0a69cd66c152E",
    },
    "is_fixed": {
        "x86": "_ZN13ssz_fv_native6schema8is_fixed17hd8d910a9f41be136E",
        "arm": "_ZN13ssz_fv_native6schema8is_fixed17h55046d992f15b227E",
    },
    "measure_fixed": {
        "x86": "_ZN13ssz_fv_native6schema13measure_fixed17h4fa86dcaf9bd6583E",
        "arm": "_ZN13ssz_fv_native6schema13measure_fixed17hd34cfd77f8373849E",
    },
    "decode_fixed": {
        "x86": "_ZN13ssz_fv_native5codec12decode_fixed17h3f666c8e8472e7e0E",
        "arm": "_ZN13ssz_fv_native5codec12decode_fixed17hd268ce61b5ac9b5fE",
    },
    "decode_offsets": {
        "x86": "_ZN13ssz_fv_native5codec14decode_offsets17h6fac02bf9c6f9009E",
        "arm": "_ZN13ssz_fv_native5codec14decode_offsets17h3986df5c439cd32dE",
    },
    "decode_list": {
        "x86": "_ZN13ssz_fv_native5codec11decode_list17h2353dfe59d6a29a4E",
        "arm": "_ZN13ssz_fv_native5codec11decode_list17h1123a2f8d52877c5E",
    },
    "read_offset": {
        "x86": "_ZN13ssz_fv_native5codec11read_offset17h0da3b64779397175E",
        "arm": "_ZN13ssz_fv_native5codec11read_offset17h14742c7c7578f3fcE",
    },
    "bounded": {
        "x86": "_ZN13ssz_fv_native5codec7bounded17hf9278acab7ca6324E",
        "arm": "_ZN13ssz_fv_native5codec7bounded17haa64e3a0177cad3fE",
    },
    "nat_cmp_usize": {
        "x86": "_ZN13ssz_fv_native3nat3Nat9cmp_usize17h9ed8a0ac7ca8d0ffE",
        "arm": "_ZN13ssz_fv_native3nat3Nat9cmp_usize17h857d9c8293a9444eE",
    },
    "plan_singleton": {
        "x86": "_ZN13ssz_fv_native5arena5Arena10slice_with17haa66d122e32a3a4fE",
        "arm": "_ZN13ssz_fv_native5arena5Arena10slice_with17h0d5d48f70484df3cE",
    },
    "decode_struct_values": {
        "x86": "_ZN13ssz_fv_native5arena5Arena10slice_with17h146db97d48ae213eE",
        "arm": "_ZN13ssz_fv_native5arena5Arena10slice_with17h0ed27805c5c943ffE",
    },
    "sha_compress": {
        "x86": "_ZN13ssz_fv_native4hash8compress17h8a841109f2045706E",
        "arm": "_ZN13ssz_fv_native4hash8compress17h2f0506da629ca044E",
    },
    "sha_finalize": {
        "x86": "_ZN13ssz_fv_native4hash6Sha2568finalize17h9f92626b8c567611E",
        "arm": "_ZN13ssz_fv_native4hash6Sha2568finalize17hc45a056ca54f57abE",
    },
    "sha_combine": {
        "x86": "_ZN13ssz_fv_native4hash7combine17hd199d01286f21673E",
        "arm": "_ZN13ssz_fv_native4hash7combine17hf6cdc4c975350651E",
    },
    "slice_index_fail": {
        "x86": "_ZN4core5slice5index16slice_index_fail17h3a8dac974e40bbe0E",
        "arm": "_ZN4core5slice5index16slice_index_fail17ha11ebec75b83c110E",
    },
    "panic_bounds_check": {
        "x86": "_ZN4core9panicking18panic_bounds_check17h238ef7d9b41c88d7E",
        "arm": "_ZN4core9panicking18panic_bounds_check17hfe133fc96452b1cfE",
    },
    "panic_on_ord_violation": {
        "x86": "_ZN4core5slice4sort6shared9smallsort22panic_on_ord_violation17h2989703bbf0af21dE",
        "arm": "_ZN4core5slice4sort6shared9smallsort22panic_on_ord_violation17h3e94085727ccf329E",
    },
    "memcpy": {"x86": "memcpy", "arm": "memcpy"},
    "memset": {"x86": "memset", "arm": "memset"},
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
    and reached callee images. Only explicitly named direct callees are allowed,
    including unconditional tail calls.
    Terminals accept either labels or (label, byte displacement) pairs.
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
    terminal_entries = [(item, 0) if isinstance(item, str) else item for item in terminals]
    terminal_offsets = {int(unique_symbol(label)[0], 16) - start + displacement
                        for label, displacement in terminal_entries}
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
            if mnemonic in ("jmp", "jmpq", "b") and row["target"] in call_targets:
                row["callee"] = call_targets[row["target"]]
                row["tail_call"] = True
                reached_calls.add(row["callee"])
                continue
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


def validate_nat_mul_image(arch, bodies, span, origin):
    """Pin the complete multiplication closure, including gaps and panic bytes."""
    from hashlib import sha256

    if arch == "x86":
        specs = {"nat_mul": (0, 218, 825), "nat_mul_word": (832, 221, 875),
                 "memset": (148928, 18, 63)}
        frontier = [814, 817]
        span_digest = "3d73dde8285914cb74679e21e894d0bebcfe1406fb322a393d0b87c0df76f809"
        selection_digest = "dc27e6b3bb1092e7e9ff4fd11ad4b9a513f8d1c09690a3b3ef07bb43da7ced96"
        from decoder_x86_binding import expression
    elif arch == "arm":
        specs = {"nat_mul": (0, 384, 1544), "nat_mul_word": (1544, 458, 1832),
                 "memset": (167060, 13, 52)}
        frontier = [1536]
        span_digest = "111b0d1704ef7d2a71026ef937a14869bd3881fcfb9563752becadf248ef0007"
        selection_digest = "db89fc28d95e12e30d5c29e864d43ec82969e280d70996cffe912da6d6cf6714"
    else:
        raise ValueError(f"unsupported multiplication architecture: {arch}")
    if (set(bodies) != set(specs) or type(origin) is not int or origin != 0
            or len(span) != specs["memset"][0] + specs["memset"][2]
            or sha256(span).hexdigest() != span_digest):
        raise ValueError(f"{arch}: multiplication linked image differs from pinned closure")
    selected = {}
    for key, (offset, count, size) in specs.items():
        rows, entries, raw, frontiers, callees = bodies[key]
        expected_callees = {
            FUNCTIONS[child][arch]: {
                "offset": specs[child][0], "size": specs[child][2],
                "raw": bodies[child][2].hex()}
            for child in ("nat_mul_word", "memset")
        } if key == "nat_mul" else {}
        if (entries != [0] or frontiers != (frontier if key == "nat_mul" else [])
                or not all(type(pc) is int for pc in entries + frontiers)
                or len(rows) != count or len(raw) != size
                or span[offset:offset + size] != raw or callees != expected_callees):
            raise ValueError(f"{arch}: unexpected multiplication component: {key}")
        selected[key] = [
            [row["pc"], row["width"], row["encoding"],
             expression(row) if arch == "x86" else None,
             row.get("target"), row.get("callee")]
            for row in rows]
    selection = json.dumps(selected, sort_keys=True, separators=(",", ":")).encode()
    if sha256(selection).hexdigest() != selection_digest:
        raise ValueError(f"{arch}: multiplication selected instructions differ from pinned closure")
