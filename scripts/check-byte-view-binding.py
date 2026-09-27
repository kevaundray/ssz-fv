#!/usr/bin/env python3
"""Bind ByteVector/ByteList decoder bodies, including real shared runtime calls.

The bounds-panic frontier requires a separate unreachability proof. A checked
instruction image alone does not establish deserialization refinement.
"""
from pathlib import Path
import tempfile

from decoder_binding import extract, output
from decoder_x86_binding import byte_view_source as x86_source
from decoder_arm_binding import byte_view_source as arm_source
from native_build import ROOT


def main():
    configurations = (
        ("x86", "SszX86",
         [(".LBB93_1", 0), (".LBB93_44", 0), (".LBB93_27", 0), (".LBB93_32", 0)],
         (".LBB93_318",), (), x86_source),
        ("arm", "SszArm",
         [(".LBB93_28", 0), (".LBB93_5", 20), (".LBB93_82", 0), (".LBB93_32", 0)],
         (".LBB93_319",), ("memcpy",), arm_source),
    )
    with tempfile.TemporaryDirectory(prefix="ssz-byte-view-binding-") as directory:
        temp = Path(directory)
        for arch, namespace, entries, terminals, calls, generate in configurations:
            backend = ROOT / f"backends/{arch}"
            output("lake", "--log-level=error", "build", f"{namespace}.ByteViewImpl", cwd=backend)
            rows, offsets, raw, frontier, callees = extract(temp, arch, "deserialize", entries, terminals, calls)
            proof = temp / f"{arch}.lean"
            proof.write_text(generate(rows, offsets, raw, frontier, callees))
            output("lake", "env", "lean", str(proof), cwd=backend)
            print(f"{arch} byte-view decoders: {len(rows)} linked body instructions, "
                  f"{len(callees)} runtime callees, and CodeAt witness checked; "
                  f"unreachable-frontier obligation {frontier} (not a refinement proof)", flush=True)


if __name__ == "__main__":
    main()
