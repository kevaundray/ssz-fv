#!/usr/bin/env python3
"""Check that raw zero-width vectors reserve storage before constructing windows."""
from pathlib import Path
import subprocess
import tempfile

from native_build import ROOT


SOURCE = r"""import SszCodecDecode

open SszNative

def checkFailure (outcome : CodecDecode.Outcome CodecDecode.Node) : IO Unit := do
  match outcome.result with
  | .error (.primitive (.arithmetic .scratchExhausted)) =>
      unless outcome.used == 0 do
        throw (IO.userError "failed reservation changed the cursor")
  | _ => throw (IO.userError "expected scratch exhaustion")

def checkSuccess (outcome : CodecDecode.Outcome CodecDecode.Node) : IO Unit := do
  match outcome.erase with
  | .ok (.ok value) =>
      unless Ssz.Value.beq value (.seq [.uint 0, .uint 0]) && outcome.used == 96 do
        throw (IO.userError "zero-width elements or allocation changed")
  | _ => throw (IO.userError "small zero-width vector was refused")

def main : IO Unit := do
  let requested ← IO.mkRef (2^63 : Nat)
  let count ← requested.get
  let element := Codec.Desc.primitive (.uint (.small 0))
  let huge := Codec.Desc.vector element (.small (BitVec.ofNat 64 count))
  checkFailure (CodecDecode.run huge #[] ⟨4096, 0, 0⟩)
  checkSuccess (CodecDecode.run (.vector element (.small 2)) #[] ⟨4096, 96, 0⟩)
  IO.println "PASS: reservation-first huge zero-width refusal and ordinary decoding"
"""


def main():
    with tempfile.TemporaryDirectory(prefix="ssz-decoder-reservation-") as directory:
        source = Path(directory) / "Regression.lean"
        source.write_text(SOURCE)
        for name in ("x86", "arm"):
            backend = ROOT / "backends" / name
            subprocess.run(
                ["lake", "--log-level=error", "build", "SszCodecDecode"],
                cwd=backend, check=True,
            )
            # GNU timeout terminates the process group, including Lean beneath Lake.
            # The old eager-window implementation never reaches the refusal.
            subprocess.run(
                ["timeout", "--kill-after=2s", "20s", "lake", "env", "lean",
                 "-j1", "-M2048", "--run", str(source)],
                cwd=backend, check=True,
            )
            print(f"PASS {name}: decoder reservation regression", flush=True)


if __name__ == "__main__":
    main()
