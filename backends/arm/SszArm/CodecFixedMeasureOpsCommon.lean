import SszArm.CodecFixedOps

namespace SszArm.Codec.Fixed.MeasureFixed

open Dispatch.Block (next put)

def call (delta : BitVec 64) (s : ArmState) : ArmState :=
  w .PC (read_pc s + delta) (w (.GPR 30#5) (read_pc s + 4#64) s)

def load32 (target address : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  put target ((read_mem_bytes 4 (r (.GPR address) s + offset) s).setWidth 64) s

def storePair (first second address : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 16 (r (.GPR address) s + offset)
    (r (.GPR second) s ++ r (.GPR first) s) s)

def storePair32 (first second address : BitVec 5) (offset : BitVec 64) (s : ArmState) : ArmState :=
  next (write_mem_bytes 8 (r (.GPR address) s + offset)
    ((r (.GPR second) s).setWidth 32 ++ (r (.GPR first) s).setWidth 32) s)

end SszArm.Codec.Fixed.MeasureFixed
