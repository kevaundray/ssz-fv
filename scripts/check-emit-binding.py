#!/usr/bin/env python3
"""Bind primitive emitter instructions and linked memcpy, not execution refinement."""
from pathlib import Path
import json
import tempfile

from decoder_binding import FUNCTIONS, extract, linked_span, output
from decoder_arm_binding import emit_source as arm_source
from decoder_x86_binding import emit_source as x86_source
from native_build import ROOT


def table_bytes(temp):
    elf = temp / "x86.elf"
    symbols = [line.split() for line in output(
        "llvm-nm-18", "-S", "--defined-only", str(elf)).splitlines()]

    def address(name):
        matches = [item for item in symbols if item[-1] == name]
        if len(matches) != 1:
            raise ValueError(f"x86: missing or ambiguous symbol {name}")
        return int(matches[0][0], 16)

    root, table = address(FUNCTIONS["emit"]["x86"]), address(".LJTI84_0")
    if table - root != -92800:
        raise ValueError("x86: unexpected emitter jump-table location")
    headers = json.loads(output("llvm-readobj-18", "--sections",
                                "--elf-output-style=JSON", str(elf)))
    sections = [item["Section"] for item in headers[0]["Sections"]
                if item["Section"]["Address"] <= table
                and table + 16 <= item["Section"]["Address"] + item["Section"]["Size"]]
    if len(sections) != 1 or sections[0]["Name"]["Name"] != ".rodata":
        raise ValueError("x86: emitter jump table is not wholly read-only")
    section = sections[0]
    position = section["Offset"] + table - section["Address"]
    data = elf.read_bytes()[position:position + 16]
    destinations = [table - root + int.from_bytes(data[i:i + 4], "little", signed=True)
                    for i in range(0, 16, 4)]
    if destinations != [256, 414, 307, 347]:
        raise ValueError("x86: emitter value-tag destinations disagree with actual table")
    return data


def image(temp, arch):
    symbol = FUNCTIONS["emit"][arch]
    if arch == "arm":
        return extract(temp, arch, "emit", [(symbol, 0)],
                       [".LBB84_23", *(f".LBB84_{i}" for i in range(86, 92))],
                       ["memcpy"])
    rows, entries, raw, frontiers, callees = extract(
        temp, arch, "emit", [(symbol, 0), (".LBB84_14", 0), (".LBB84_25", 0)],
        [(symbol, 254), ".LBB84_17", ".LBB84_20",
         *(f".LBB84_{i}" for i in range(97, 105))], ["memcpy"])
    if 254 not in frontiers or raw[254:256] != b"\xff\xe1":
        raise ValueError("x86: unexpected emitter indirect JMP encoding")
    # Preserve the actual indirect instruction; its destination is not assumed.
    rows.append({"pc": 254, "width": 2, "encoding": raw[254:256].hex(),
                 "asm": "jmpq *%rcx"})
    rows.sort(key=lambda row: row["pc"])
    frontiers.remove(254)
    return rows, entries, raw, frontiers, callees


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-emit-binding-") as directory:
        temp = Path(directory)
        for arch, module in (("x86", "SszX86.EmitMemcpyEmbedded"),
                             ("arm", "SszArm.EmitImpl")):
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", module, cwd=backend)
            rows, entries, raw, frontiers, callees = image(temp, arch)
            if arch == "x86":
                table = table_bytes(temp)
                origin, linked = linked_span(temp, arch, "emit", raw, callees)
                if origin != 0:
                    raise ValueError("x86: unexpected joint emitter image origin")
                copy_rows, copy_entries, copy_raw, copy_frontiers, copy_callees = extract(
                    temp, arch, "memcpy", [("memcpy", 0)])
                if copy_entries != [0] or copy_frontiers or copy_callees:
                    raise ValueError("x86: memcpy is not a complete leaf image")
                source = x86_source(
                    rows, entries, raw, frontiers, callees, linked_bytes=linked,
                    memcpy_rows=copy_rows, memcpy_raw=copy_raw, table_bytes=table)
                detail = "19 memcpy instructions, 16 actual read-only table bytes"
            else:
                source = arm_source(rows, entries, raw, frontiers, callees)
                detail = "14 memcpy instructions"
            proof = temp / f"{arch}-emit.lean"
            proof.write_text(source)
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} primitive emitter: {len(rows)} actual instructions and {detail} "
                  "jointly bound (not an execution refinement)", flush=True)


if __name__ == "__main__":
    main()
