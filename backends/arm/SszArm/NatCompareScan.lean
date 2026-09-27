import SszArm.NatCompareTrim
import SszArm.NatCompareOrder

namespace SszArm.NatCompare

open UintCodec SszNative.Limbs SszNative.NatABI

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

inductive ScanKind where
  | largeLarge | largeSmall | smallLarge | smallSmall
  deriving DecidableEq

def ScanKind.head : ScanKind → Nat
  | .largeLarge => 364 | .largeSmall => 508 | .smallLarge => 612 | .smallSmall => 696

def ScanKind.leftSmall : ScanKind → Bool
  | .smallLarge | .smallSmall => true | _ => false

def ScanKind.rightSmall : ScanKind → Bool
  | .largeSmall | .smallSmall => true | _ => false

def ScanKind.index (kind : ScanKind) (n : Nat) : BitVec 64 :=
  if kind = .smallSmall then BitVec.ofNat 64 n else BitVec.ofNat 64 n - 1#64

def ScanInputs (s : ArmState) (kind : ScanKind) (xs ys : List (BitVec 64)) : Prop :=
  Operand s (r (.GPR 0#5) s) (r (.GPR 1#5) s) xs ∧
  Operand s (r (.GPR 2#5) s) (r (.GPR 3#5) s) ys ∧
  (r (.GPR 0#5) s = 0#64 ↔ kind.leftSmall = true) ∧
  (r (.GPR 2#5) s = 0#64 ↔ kind.rightSmall = true)

theorem ScanInputs.frame {s t : ArmState} {kind : ScanKind} {xs ys : List (BitVec 64)}
    (hf : Frame s t) (h0 : r (.GPR 0#5) t = r (.GPR 0#5) s)
    (hi : ScanInputs s kind xs ys) : ScanInputs t kind xs ys := by
  have h1 := hf.registers 1#5 (by decide)
  have h2 := hf.registers 2#5 (by decide)
  have h3 := hf.registers 3#5 (by decide)
  simpa only [ScanInputs, h0, h1, h2, h3] using
    And.intro (hf.operand _ _ _ hi.1) (And.intro (hf.operand _ _ _ hi.2.1) hi.2.2)

def ScanKind.emptyOps : ScanKind → List Op
  | .largeLarge => [.p364, .p368]
  | .largeSmall => [.p508, .p512]
  | .smallLarge => [.p612, .p616]
  | .smallSmall => [.p696]

theorem scan_empty (s : ArmState) (base : BitVec 64) (kind : ScanKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.head)
    (h9 : r (.GPR 9#5) s = kind.index 0) :
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧ read_pc t = r (.GPR 30#5) s ∧
      (r (.GPR 0#5) t).setWidth 8 = orderingByte .eq := by
  let u := block base kind.emptyOps s
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.head := hp
  have hfollow : Follows base kind.emptyOps s := by
    cases kind <;> simp_all [ScanKind.emptyOps, ScanKind.head, ScanKind.index,
      Follows, Op.row, Op.effect, next, state_simp_rules, BitVec.add_assoc]
  have hu := block_run base kind.emptyOps s hc he ha hfollow
  have huf : Frame s u := readonly_frame base _ _ (by cases kind <;> decide)
  have hup : read_pc u = base + 700#64 := by
    cases kind <;> simp_all [u, ScanKind.emptyOps, ScanKind.index, block,
      Op.effect, next, state_simp_rules]
  obtain ⟨fuel, t, ht, htf, htp, hret⟩ := return_equal u base
    (huf.code hc) (huf.error.trans he) (huf.aligned ha) hup
  refine ⟨kind.emptyOps.length + fuel, t, ?_, huf.trans htf,
    htp.trans (huf.registers 30#5 (by decide)), hret⟩
  rw [run_plus, hu, ht]

end SszArm.NatCompare
