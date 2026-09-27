import SszArm.NatCompareLength
import SszArm.NatCompareScanProofs

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def scanKind (left right : BitVec 64) : ScanKind :=
  if left = 0#64 then (if right = 0#64 then .smallSmall else .smallLarge)
  else (if right = 0#64 then .largeSmall else .largeLarge)

def scanEntryOps (left right : BitVec 64) : List Op :=
  [.p304] ++ if left = 0#64 then
    [.p588] ++ if right = 0#64 then [] else [.p592, .p596]
  else [.p308, .p312] ++ if right = 0#64 then [.p316] else []

theorem scan_entry (s : ArmState) (base : BitVec 64) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 304#64) (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 n) :
    let kind := scanKind (r (.GPR 0#5) s) (r (.GPR 2#5) s)
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 0#5) t = r (.GPR 0#5) s ∧
      r (.GPR 9#5) t = kind.index n ∧
      read_pc t = base + BitVec.ofNat 64 kind.head := by
  let ops := scanEntryOps (r (.GPR 0#5) s) (r (.GPR 2#5) s)
  let t := block base ops s
  have hpc : r .PC s = base + 304#64 := hp
  have hfollow : Follows base ops s := by
    by_cases hl : r (.GPR 0#5) s = 0#64 <;> by_cases hr : r (.GPR 2#5) s = 0#64 <;>
      simp [ops, scanEntryOps, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hl, hr, hpc, BitVec.add_assoc]
  refine ⟨ops.length, t, block_run base ops s hc he ha hfollow,
    readonly_frame base ops s ?_, block_zero base ops s ?_, ?_, ?_⟩
  · dsimp only [ops, scanEntryOps]; split <;> split <;> decide
  · dsimp only [ops, scanEntryOps]; split <;> split <;> decide
  all_goals
    by_cases hl : r (.GPR 0#5) s = 0#64 <;> by_cases hr : r (.GPR 2#5) s = 0#64 <;>
      simp [t, ops, scanEntryOps, scanKind, ScanKind.index, ScanKind.head,
        block, Op.effect, put, next, state_simp_rules, hl, hr, h9]

theorem scan_inputs (s : ArmState) (xs ys : List (BitVec 64))
    (hx : Operand s (r (.GPR 0#5) s) (r (.GPR 1#5) s) xs)
    (hy : Operand s (r (.GPR 2#5) s) (r (.GPR 3#5) s) ys) :
    ScanInputs s (scanKind (r (.GPR 0#5) s) (r (.GPR 2#5) s)) xs ys := by
  refine ⟨hx, hy, ?_, ?_⟩
  all_goals
    by_cases hl : r (.GPR 0#5) s = 0#64 <;> by_cases hr : r (.GPR 2#5) s = 0#64 <;>
      simp [scanKind, ScanKind.leftSmall, ScanKind.rightSmall, hl, hr]

/-- Operand observations follow a scratch-only execution while its input
pointer register has not yet been overwritten by the result. -/
theorem Frame.operands {s t : ArmState} (hf : Frame s t)
    (h0 : r (.GPR 0#5) t = r (.GPR 0#5) s) (xs ys : List (BitVec 64))
    (hx : Operand s (r (.GPR 0#5) s) (r (.GPR 1#5) s) xs)
    (hy : Operand s (r (.GPR 2#5) s) (r (.GPR 3#5) s) ys) :
    Operand t (r (.GPR 0#5) t) (r (.GPR 1#5) t) xs ∧
    Operand t (r (.GPR 2#5) t) (r (.GPR 3#5) t) ys := by
  simpa only [h0, hf.registers 1#5 (by decide), hf.registers 2#5 (by decide),
    hf.registers 3#5 (by decide)] using And.intro (hf.operand _ _ _ hx) (hf.operand _ _ _ hy)

end SszArm.NatCompare
