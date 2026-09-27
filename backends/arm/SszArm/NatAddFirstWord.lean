import SszArm.NatAddOneWord
import SszArm.NatAddContract

namespace SszArm.NatAdd

open UintCodec
open Delimited (MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive FirstKind where
  | largeLarge | largeSmall | smallLarge
  deriving DecidableEq

def FirstKind.ops (kind : FirstKind) (overflow : Bool) : List Op :=
  [.p276] ++
    (if kind = .smallLarge then [.p1448, .p1452, .p1456, .p1460]
     else [.p280, .p284, .p288, .p1468]) ++
    (if kind = .largeSmall then
      [.p1488, .p1492, .p1496] ++
        (if overflow then [.p1508] else [.p1500, .p1504]) ++ [.p1512, .p1516]
     else (if kind = .largeLarge then [.p1472] else []) ++
      [.p1476, .p1480, .p1484, .p1524, .p1528] ++
        (if overflow then [.p1540] else [.p1532, .p1536]) ++ [.p1544, .p1548] ++
        (if kind = .largeLarge then [.p1552] else [])) ++
    (if kind = .smallLarge then [] else [.p1556, .p1560, .p1564, .p1568])

/-- The first word is stored before either general carry loop is entered. -/
structure FirstWordPost (kind : FirstKind) (s t : ArmState) (base a b : BitVec 64) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [11#5, 12#5, 13#5, 14#5, 15#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  first : r (.GPR 11#5) t = a + b
  carry : r (.GPR 12#5) t = if 2^64 ≤ a.toNat + b.toNat then 1#64 else 0#64
  flag : kind ≠ .smallLarge → r (.GPR 13#5) t = if kind = .largeSmall then 1#64 else 0#64
  remaining : kind ≠ .smallLarge → r (.GPR 14#5) t = r (.GPR 8#5) s
  index : kind ≠ .smallLarge → r (.GPR 15#5) t = 1#64
  pc : read_pc t = base + (if kind = .smallLarge then 1868#64 else 1692#64)
  stored : read_mem_bytes 8 (r (.GPR 9#5) s) t = a + b
  memory : MemoryFrame [((r (.GPR 9#5) s).toNat, 8)] s t

/-- All physically reachable first-word paths for the multiword branch. The
remaining Small/Small machine branch is excluded by the proven width classifier. -/
theorem first_word_run (s : ArmState) (base a b : BitVec 64) (kind : FirstKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 276#64)
    (physical : (r (.GPR 9#5) s).toNat + 8 ≤ 2^64)
    (leftKind : r (.GPR 1#5) s = 0#64 ↔ kind = .smallLarge)
    (rightKind : r (.GPR 3#5) s = 0#64 ↔ kind = .largeSmall)
    (left : if kind = .smallLarge then r (.GPR 2#5) s = a else
      r (.GPR 2#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 1#5) s) s = a)
    (right : if kind = .largeSmall then r (.GPR 4#5) s = b else
      r (.GPR 4#5) s ≠ 0#64 ∧ read_mem_bytes 8 (r (.GPR 3#5) s) s = b) :
    let ops := kind.ops (sumOverflow a b)
    let t := block base ops s
    run ops.length s = t ∧ FirstWordPost kind s t base a b := by
  have carry : (AddWithCarry a b 0#1).2.c = 1#1 ↔ 2^64 ≤ a.toNat + b.toNat := by
    simpa only [Udivti3.radix, BitVec.toNat_ofNat, Nat.add_zero] using Udivti3.adc_carry a b 0#1
  have hpc : r .PC s = base + 276#64 := hp
  have follow : Follows base (kind.ops (sumOverflow a b)) s := by
    cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp_all (config := {decide := true, instances := true})
        [FirstKind.ops, sumOverflow, Follows, Op.row, Op.effect, put, next,
          state_simp_rules, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follow, ?_⟩
  have memory : (block base (kind.ops (sumOverflow a b)) s).mem =
      (write_mem_bytes 8 (r (.GPR 9#5) s) (a+b) s).mem := by
    cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp_all (config := {decide := true, instances := true})
        [FirstKind.ops, sumOverflow, block, Op.effect, put, next,
          state_simp_rules, NatCompare.spill_mem_w, ArmState.mem_w_eq_mem]
  constructor
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp (disch := simp_all) [FirstKind.ops, sumOverflow, overflow, block,
        Op.effect, put, next, state_simp_rules]
  · intro reg
    cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp_all [FirstKind.ops, sumOverflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp_all [FirstKind.ops, sumOverflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp [FirstKind.ops, sumOverflow, overflow, block, Op.effect, put, next, state_simp_rules]
  · cases kind <;> by_cases overflow : 2^64 ≤ a.toNat + b.toNat <;>
      simp_all [FirstKind.ops, sumOverflow, block, Op.effect, put, next, state_simp_rules]
  · rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8 (r (.GPR 9#5) s)]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical
  · intro address outside
    rw [memory]
    exact (Delimited.store_frame s _ 8 _ physical) address outside

end SszArm.NatAdd
