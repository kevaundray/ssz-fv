import SszArm.MeasureUintValueOps

namespace SszArm.Measure.Uint

open UintCodec

inductive CountOp where
  | p416 | p420 | p424 | p428 | p432 | p436 | p440 | p2192
  | p2196 | p2200 | p2204 | p2208 | p2212 | p2216 | p2220 | p2224
  | p2228 | p2232 | p2236 | p2240 | p2244 | p2248 | p2252 | p2256
  | p2260 | p2264 | p2268 | p2272 | p2276 | p2280 | p2284 | p2288
  | p2292 | p2296 | p2300 | p2304 | p2308 | p2312
  deriving DecidableEq

def CountOp.row : CountOp → Nat × BitVec 32
  | .p416 => (416, 0xd37ae548#32)
  | .p420 => (420, 0xd37afd49#32)
  | .p424 => (424, 0xf100e50a#32)
  | .p428 => (428, 0x92800008#32)
  | .p432 => (432, 0x9a080129#32)
  | .p436 => (436, 0xaa0b03e8#32)
  | .p440 => (440, 0x140001b9#32)
  | .p2192 => (2192, 0xaa1f03e9#32)
  | .p2196 => (2196, 0xb40010e8#32)
  | .p2200 => (2200, 0x528000ea#32)
  | .p2204 => (2204, 0xd10043ff#32)
  | .p2208 => (2208, 0xf90003e9#32)
  | .p2212 => (2212, 0xf90007ea#32)
  | .p2216 => (2216, 0xaa0803e9#32)
  | .p2220 => (2220, 0xd280080a#32)
  | .p2224 => (2224, 0xb4000089#32)
  | .p2228 => (2228, 0xd100054a#32)
  | .p2232 => (2232, 0xd341fd29#32)
  | .p2236 => (2236, 0xb5ffffc9#32)
  | .p2240 => (2240, 0xaa0a03e8#32)
  | .p2244 => (2244, 0xf94007ea#32)
  | .p2248 => (2248, 0xf94003e9#32)
  | .p2252 => (2252, 0x910043ff#32)
  | .p2256 => (2256, 0x5280080b#32)
  | .p2260 => (2260, 0x4b080168#32)
  | .p2264 => (2264, 0xab080148#32)
  | .p2268 => (2268, 0x54000062#32)
  | .p2272 => (2272, 0xaa0903e9#32)
  | .p2276 => (2276, 0x14000002#32)
  | .p2280 => (2280, 0x91000529#32)
  | .p2284 => (2284, 0xd10043ff#32)
  | .p2288 => (2288, 0xf90003ea#32)
  | .p2292 => (2292, 0xd343fd0a#32)
  | .p2296 => (2296, 0xaa09f548#32)
  | .p2300 => (2300, 0xf94003ea#32)
  | .p2304 => (2304, 0x910043ff#32)
  | .p2308 => (2308, 0xd343fd29#32)
  | .p2312 => (2312, 0x1400006a#32)

def CountOp.effect (base : BitVec 64) : CountOp → ArmState → ArmState
  | .p416, s => put 8 (r (.GPR 10#5) s <<< 6) s
  | .p420, s => put 9 (r (.GPR 10#5) s >>> 58) s
  | .p424, s => w (.GPR 10#5) (AddWithCarry (r (.GPR 8#5) s) (~~~57#64) 1#1).1
      (write_pstate (AddWithCarry (r (.GPR 8#5) s) (~~~57#64) 1#1).2 (next s))
  | .p428, s => put 8 (-1#64) s
  | .p432, s => put 9 (AddWithCarry (r (.GPR 9#5) s) (r (.GPR 8#5) s) (r (.FLAG .C) s)).1 s
  | .p436, s => put 8 (r (.GPR 11#5) s) s
  | .p440, s => w .PC (base + 2204#64) s
  | .p2192, s => put 9 0#64 s
  | .p2196, s => w .PC (if r (.GPR 8#5) s = 0#64 then base + 2736#64 else base + 2200#64) s
  | .p2200, s => put 10 7#64 s
  | .p2204, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p2208, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .p2212, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 8#64) (r (.GPR 10#5) s) s)
  | .p2216, s => put 9 (r (.GPR 8#5) s) s
  | .p2220, s => put 10 64#64 s
  | .p2224, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 2240#64 else base + 2228#64) s
  | .p2228, s => put 10 (r (.GPR 10#5) s - 1#64) s
  | .p2232, s => put 9 (r (.GPR 9#5) s >>> 1) s
  | .p2236, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 2240#64 else base + 2228#64) s
  | .p2240, s => put 8 (r (.GPR 10#5) s) s
  | .p2244, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s) s
  | .p2248, s => put 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p2252, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p2256, s => put 11 64#64 s
  | .p2260, s => put 8 (((r (.GPR 11#5) s).setWidth 32 - (r (.GPR 8#5) s).setWidth 32).setWidth 64) s
  | .p2264, s => w (.GPR 8#5) (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 8#5) s) 0#1).1
      (write_pstate (AddWithCarry (r (.GPR 10#5) s) (r (.GPR 8#5) s) 0#1).2 (next s))
  | .p2268, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 2280#64 else base + 2272#64) s
  | .p2272, s => put 9 (r (.GPR 9#5) s) s
  | .p2276, s => w .PC (base + 2284#64) s
  | .p2280, s => put 9 (r (.GPR 9#5) s + 1#64) s
  | .p2284, s => put 31 (r (.GPR 31#5) s - 16#64) s
  | .p2288, s => next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 10#5) s) s)
  | .p2292, s => put 10 (r (.GPR 8#5) s >>> 3) s
  | .p2296, s => put 8 (r (.GPR 10#5) s ||| (r (.GPR 9#5) s <<< 61)) s
  | .p2300, s => put 10 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .p2304, s => put 31 (r (.GPR 31#5) s + 16#64) s
  | .p2308, s => put 9 (r (.GPR 9#5) s >>> 3) s
  | .p2312, s => w .PC (base + 2736#64) s

end SszArm.Measure.Uint
