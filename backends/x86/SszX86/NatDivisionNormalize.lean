import SszX86.NatDivisionNormalizeScan
import SszX86.NatDivisionOutput
import SszNatOperandNormalization

namespace SszX86.NatDivision
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Normal entry recovers the result pointer saved before the large division. -/
theorem normalize_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64)
    (loaded : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (out.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with rbx := UInt64.ofBitVec out}}, base + 496)) :
    Eventually (step e) P (s, base + 477) := by
  natdiv_step 124 using hc
  natdiv_load loaded
  natdiv_step 125 using hc
  natdiv_step 126 using hc
  exact next

/-- The sentinel entry is modeled too: it only installs the empty-slice sentinel.
The zero-count scan never dereferences this address. -/
theorem normalize_sentinel_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with regs := {s.regs with r14 := 8}}, base + 477)) :
    Eventually (step e) P (s, base + 471) := by
  natdiv_step 123 using hc
  exact next

/-- Common normalized-pair store sets reason zero and joins the real remainder
publication block. The quotient data buffer itself is never changed. -/
theorem normalize_publish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ResultMapped s) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with r14 := 0}
        status := flags
        dmem := resultPairMem s.dmem s.regs.rbx.toBitVec
          s.regs.r14.toBitVec s.regs.rax.toBitVec}, base + 372)) :
    Eventually (step e) P (s, base + 533) := by
  natdiv_result 139 at 0 width 8 using hc mapped hm
  natdiv_result 140 at 8 width 8 using hc mapped hm
  natdiv_step 141 using hc
  constructor <;> natdiv_step 142 using hc
  all_goals simpa [resultPairMem] using next _

theorem normalize_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with regs := {s.regs with rax := 0, r14 := 0}, status := flags}, base + 533)) :
    Eventually (step e) P (s, base + 528) := by
  natdiv_step 137 using hc
  constructor <;> natdiv_step 138 using hc
  all_goals constructor <;> exact next _

theorem normalize_one_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (loaded : Mem.loadInt s.dmem s.regs.r14.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with
        regs := {s.regs with rax := UInt64.ofBitVec limb, r14 := 0}
        status := flags}, base + 533)) :
    Eventually (step e) P (s, base + 523) := by
  natdiv_step 135 using hc
  natdiv_load loaded
  natdiv_step 136 using hc
  natdiv_step 138 using hc
  constructor <;> exact next _

/-- A nonzero scan result chooses exactly the native one-word or multiword arm. -/
theorem normalize_select_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (one : s.regs.rax.toBitVec = 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 523))
    (many : s.regs.rax.toBitVec ≠ 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 533)) :
    Eventually (step e) P (s, base + 517) := by
  have target := hc.targets ("natDivision_u533", 533) (by decide)
  natdiv_step 133 using hc
  natdiv_step 134 using hc
  by_cases single : s.regs.rax.toBitVec = 1#64
  · simpa [StatusFlags.from_result, single, Effects.All] using one single _
  · simpa [StatusFlags.from_result, single, target, Effects.All] using many single _

end SszX86.NatDivision
