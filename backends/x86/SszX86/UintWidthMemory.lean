import SszX86.BoolExec
import SszNatMemory
import SszWidth

namespace SszX86.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

/-- Absolute unsigned observations of ordinary, mapped Kraken data memory. -/
def widthLoad (m : DataMem) (address width : Nat) : Option Nat :=
  (Mem.loadInt m (BitVec.ofNat 64 address) width).map Int.toNat

/-- `Int.toNat` loses no information on Kraken's unsigned little-endian loads. -/
theorem widthLoad_eq (m : DataMem) (address width value : Nat)
    (h : widthLoad m address width = some value) :
    Mem.loadInt m (BitVec.ofNat 64 address) width = some (value : Int) := by
  unfold widthLoad Mem.loadInt at *
  cases hb : Mem.loadBytes m (BitVec.ofNat 64 address) width with
  | none => simp [hb] at h
  | some bytes =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    have hn := Int.ofBytes_ge_zero bytes
    have he : Int.ofBytes bytes = (value : Int) := by omega
    simp only [Option.map_some, he]

/-- The natural-address and modular-address views agree, even before using
non-wrapping allocation bounds. -/
theorem width_address (p : BitVec 64) (offset : Nat) :
    BitVec.ofNat 64 (p.toNat + offset) = p + BitVec.ofNat 64 offset := by
  simp [BitVec.ofNat_add]

end SszX86.UintCodec
