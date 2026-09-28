#!/usr/bin/env python3
"""Bind primitive measurement and its actual helper closure, not execution refinement."""
from pathlib import Path
import json
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from native_build import ROOT

TABLE = bytes.fromhex(
    "125d0100ff5f0100f55e01004c5f0100365d01005360010085600100"
    "a25f0100e66001006e5e0100b5600100245d01008c5d0100")
DESTINATIONS = [46, 795, 529, 616, 82, 879, 929, 702, 1026, 394, 977, 64, 168]
OFFSETS = {
    "x86": {"nat_compare": -32880, "nat_from_u128": -14704},
    "arm": {"nat_compare": -40272, "nat_from_u128": -15748, "memcpy": 123348},
}


def table_bytes(temp):
    elf = temp / "x86.elf"
    symbols = [line.split() for line in output(
        "llvm-nm-18", "-S", "--defined-only", str(elf)).splitlines()]

    def address(name):
        matches = [item for item in symbols if item[-1] == name]
        if len(matches) != 1:
            raise ValueError(f"x86: missing or ambiguous symbol {name}")
        return int(matches[0][0], 16)

    root, table = address(FUNCTIONS["measure"]["x86"]), address(".LJTI83_0")
    if table - root != -89316:
        raise ValueError("x86: unexpected measurement table location")
    headers = json.loads(output("llvm-readobj-18", "--sections",
                                "--elf-output-style=JSON", str(elf)))
    sections = [item["Section"] for item in headers[0]["Sections"]
                if item["Section"]["Address"] <= table
                and table + 52 <= item["Section"]["Address"] + item["Section"]["Size"]]
    if len(sections) != 1 or sections[0]["Name"]["Name"] != ".rodata":
        raise ValueError("x86: measurement table is not wholly read-only")
    section = sections[0]
    position = section["Offset"] + table - section["Address"]
    data = elf.read_bytes()[position:position + 52]
    destinations = [table - root + int.from_bytes(data[i:i + 4], "little", signed=True)
                    for i in range(0, 52, 4)]
    if data != TABLE or destinations != DESTINATIONS:
        raise ValueError("x86: actual measurement table bytes/destinations disagree")
    return data


def closure(temp, arch):
    symbol = FUNCTIONS["measure"][arch]
    helper_keys = OFFSETS[arch]
    calls = [FUNCTIONS[key][arch] for key in helper_keys]
    if arch == "x86":
        # Bootstrap the actual linked ELF before reading its dispatch table.
        extract(temp, arch, "measure", [])
        table = table_bytes(temp)
        entries = [(symbol, pc) for pc in [0, *DESTINATIONS[:7]]]
        terminals = [(symbol, 44)]
    else:
        table = None
        entries = [(symbol, 0)]
        # Only recursive/composite calls are frontiers; memcpy at1940 is retained.
        terminals = [(symbol, 1092), (symbol, 3108)]
    rows, starts, raw, frontiers, callees = extract(
        temp, arch, "measure", entries, terminals, calls)
    if arch == "x86":
        if frontiers != [44] or raw[44:46] != b"\xff\xe2":
            raise ValueError("x86: unexpected measurement indirect JMP")
        rows.append({"pc": 44, "width": 2, "encoding": "ffe2", "asm": "jmpq *%rdx"})
        rows.sort(key=lambda row: row["pc"])
        frontiers = []
        expected = ([0, *DESTINATIONS[:7]], 476, 3528, [])
    else:
        expected = ([0], 1030, 4352, [1092, 3108])
    if (starts, len(rows), len(raw), frontiers) != expected or set(callees) != set(calls):
        raise ValueError(f"{arch}: unexpected primitive measurement call closure")
    bodies = {"measure": (rows, starts, raw, frontiers, callees)}
    for key, offset in helper_keys.items():
        name = FUNCTIONS[key][arch]
        body = extract(temp, arch, key, [(name, 0)])
        metadata = callees[name]
        if (body[1] != [0] or body[3] or body[4] or metadata["offset"] != offset
                or metadata["size"] != len(body[2])
                or bytes.fromhex(metadata["raw"]) != body[2]):
            raise ValueError(f"{arch}: helper image/offset mismatch: {key}")
        bodies[key] = body
    origin, span = linked_span(temp, arch, "measure", raw, callees)
    expected_span = (-32880, 36408) if arch == "x86" else (-40272, 163676)
    if (origin, len(span)) != expected_span:
        raise ValueError(f"{arch}: unexpected joint measurement image extent")
    return bodies, span, origin, table


def main():
    import decoder_arm_binding
    import decoder_x86_binding

    with tempfile.TemporaryDirectory(prefix="ssz-measure-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, generate in (
                ("x86", "SszX86", decoder_x86_binding.measure_source),
                ("arm", "SszArm", decoder_arm_binding.measure_source)):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.MeasureImpl",
                   f"{namespace}.NatCompareImpl", f"{namespace}.NatFromU128Impl", cwd=backend)
            bodies, span, origin, table = closure(temp, arch)
            source = generate(bodies, span, origin=origin, table_bytes=table)
            proof = temp / f"{arch}-measure.lean"
            proof.write_text(source)
            output("lake", "env", "lean", str(proof), cwd=backend)
            helpers = ", ".join(f"{len(bodies[key][0])} {key} instructions"
                                for key in OFFSETS[arch])
            print(f"{arch} primitive measurement: {len(bodies['measure'][0])} actual caller "
                  f"instructions and {helpers} jointly bound (not an execution refinement)",
                  flush=True)


if __name__ == "__main__":
    main()
