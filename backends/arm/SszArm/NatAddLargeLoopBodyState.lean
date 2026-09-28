import SszArm.NatAddLargeLoopAdds

namespace SszArm.NatAdd.LargeLoop

open SszNative
open NatCompare (saved)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Small architectural observations, checked separately from execution and
memory ownership. Composing a loop body never unfolds its successor state. -/
theorem adds_pc (s : ArmState) (base left right : BitVec 64) (carry : Nat) :
    read_pc (addsResult s base left right carry) = base + 1628#64 := by
  simp [addsResult, state_simp_rules]

theorem adds_address (s : ArmState) (base left right : BitVec 64) (carry : Nat) :
    storeAddress (addsResult s base left right carry) .large = storeAddress s .large := by
  simp [storeAddress, StoreKind.index, addsResult, state_simp_rules]

theorem adds_word (s : ArmState) (base left right : BitVec 64) (carry : Nat) :
    r (.GPR 16#5) (addsResult s base left right carry) = (LimbAdd.step left right carry).1 := by
  simpa [addsResult, state_simp_rules] using add_low left right carry

theorem adds_register (s : ArmState) (base left right : BitVec 64) (carry : Nat)
    (reg : BitVec 5) (h12 : reg ≠ 12#5) (h16 : reg ≠ 16#5) (h17 : reg ≠ 17#5) :
    r (.GPR reg) (addsResult s base left right carry) = r (.GPR reg) s := by
  simp [addsResult, state_simp_rules, h12, h16, h17]

theorem stored_register (s : ArmState) (base : BitVec 64) (kind : StoreKind) (reg : BitVec 5) :
    r (.GPR reg) (storeResult s base kind) = r (.GPR reg) s := by
  simp [storeResult, storeMemory, saved, state_simp_rules]

theorem stored_pc (s : ArmState) (base : BitVec 64) :
    read_pc (storeResult s base .large) = base + 1660#64 := by
  simp [storeResult, StoreKind.start, state_simp_rules]

theorem stored_word (s : ArmState) (base : BitVec 64)
    (physical : (storeAddress s .large).toNat + 8 ≤ 2^64) :
    read_mem_bytes 8 (storeAddress s .large) (storeResult s base .large) = r (.GPR 16#5) s := by
  simp only [storeResult, read_mem_bytes_of_w, storeMemory, StoreKind.src]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same (saved s 10#5) 8 _ _ physical

theorem stored_adds_carry (s : ArmState) (base left right : BitVec 64) (carry : Nat)
    (bound : carry ≤ 1) :
    let t := storeResult (addsResult s base left right carry) base .large
    (if r (.FLAG .C) t = 1#1 then r (.GPR 17#5) t + 1#64 else r (.GPR 17#5) t) =
      BitVec.ofNat 64 (LimbAdd.step left right carry).2 := by
  have math := add_carry left right carry bound
  by_cases overflow : (AddWithCarry (BitVec.ofNat 64 carry + right) left 0#1).2.c = 1#1 <;>
    simpa [storeResult, storeMemory, saved, addsResult, state_simp_rules,
      carryWord, overflow] using math

end SszArm.NatAdd.LargeLoop
