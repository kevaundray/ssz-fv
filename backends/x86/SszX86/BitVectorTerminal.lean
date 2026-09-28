import SszX86.BitVectorHelperFrames
import SszX86.BitVectorReturn

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- A completed native suffix, measured from the reached memory but tied to the
original output/source addresses and original physical activation at RET. -/
structure Terminal (s : MachineData) (saved : Saved) (before : DataMem)
    (data : Ssz.Bytes) (result : Except SszNative.BitVector.Error (BitVec 128))
    (t : MachineState) : Prop where
  observed : SszNative.BitVector.ResultAt (widthLoad t.1.dmem)
    s.regs.rdi.toNat s.regs.rdx.toNat data result
  returned : Body.Returned s saved t
  frame : RegionsFrame before t.1.dmem
    [(s.regs.rdi.toNat, 80), (workStart s, workSize)]

end SszX86.BitVector
