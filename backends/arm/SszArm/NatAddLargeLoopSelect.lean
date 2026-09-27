import SszArm.NatAddLargeLoopArithmetic

namespace SszArm.NatAdd.LargeLoop

open NatCompare (saved read_spill_w)
open Delimited (Span MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Both copies of the actual right-word selection, after the left load or
its zero-extension path. The bit test is a lowered spill/test/restore block. -/
inductive GateKind where
  | loaded | zero
  deriving DecidableEq

def GateKind.start : GateKind → Nat
  | .loaded => 1732 | .zero => 1800

def gateOps (kind : GateKind) (within small : Bool) : List Op :=
  match kind with
  | .loaded =>
      [.p1732, .p1736] ++
      (if within then [.p1748] else [.p1740, .p1744]) ++
      [.p1752, .p1756, .p1760, .p1764] ++
      (if within && !small then [.p1780, .p1784, .p1788]
       else [.p1768, .p1772, .p1776, .p1792])
  | .zero =>
      [.p1800, .p1804] ++
      (if within then [.p1816] else [.p1808, .p1812]) ++
      [.p1820, .p1824, .p1828, .p1832] ++
      (if within && !small then [.p1848, .p1852, .p1856]
       else [.p1836, .p1840, .p1844])

def gateResult (s : ArmState) (base : BitVec 64) (within small : Bool) : ArmState :=
  w .PC (base + if within && !small then 1572#64 else 1860#64)
    (w (.GPR 17#5) (if within then (if small then 1#64 else 0#64) else 1#64)
      (saved (Udivti3.compare (r (.GPR 15#5) s) (r (.GPR 4#5) s) s) 9#5))

theorem gate_run (s : ArmState) (base : BitVec 64) (kind : GateKind) (small : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (h13 : r (.GPR 13#5) s = if small then 1#64 else 0#64) :
    let within := decide ((r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat)
    run (gateOps kind within small).length s = gateResult s base within small := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [saved] at hrestore
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hcflag := Udivti3.cmp_carry (r (.GPR 15#5) s) (r (.GPR 4#5) s)
  dsimp only
  have follows : Follows base
      (gateOps kind (decide ((r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat)) small) s := by
    by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
      cases kind <;> cases small <;>
      simp_all (config := {decide := true})
        [gateOps, GateKind.start, Follows, Op.row, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, state_simp_rules, read_spill_w,
          BitVec.sub_add_cancel, BitVec.add_assoc]
    all_goals omega
  rw [block_run base _ s hc he ha follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h9 : reg = 9#5 <;> by_cases h17 : reg = 17#5 <;>
        by_cases h31 : reg = 31#5 <;> (try subst reg) <;>
        by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
        cases kind <;> cases small <;>
        simp_all (config := {decide := true})
          [gateOps, gateResult, GateKind.start, block, Op.effect, put, next,
            Udivti3.compare, Udivti3.next, saved, state_simp_rules, read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
        cases kind <;> cases small <;>
        simp_all (config := {decide := true})
          [gateOps, gateResult, GateKind.start, block, Op.effect, put, next,
            Udivti3.compare, Udivti3.next, saved, state_simp_rules, read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
      all_goals omega
    | SFP reg =>
      cases kind <;> cases small <;>
        by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
        simp_all [gateOps, gateResult, block, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, saved, state_simp_rules]
    | FLAG flag =>
      cases kind <;> cases small <;>
        by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
        simp_all [gateOps, gateResult, block, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, saved, state_simp_rules]
    | ERR =>
      cases kind <;> cases small <;>
        by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
        simp_all [gateOps, gateResult, block, Op.effect, put, next,
          Udivti3.compare, Udivti3.next, saved, state_simp_rules]
  · cases kind <;> cases small <;>
      by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
      simp_all [gateOps, gateResult, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, saved, state_simp_rules]
  · intro n addr
    cases kind <;> cases small <;>
      by_cases hi : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
      simp_all [gateOps, gateResult, block, Op.effect, put, next,
        Udivti3.compare, Udivti3.next, saved, state_simp_rules, read_spill_w]

theorem gate_frame (s : ArmState) (base : BitVec 64) (within small : Bool)
    (writes : List Span) (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes) :
    LoopFrame writes s (gateResult s base within small) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [gateResult, saved, Udivti3.compare, Udivti3.next, state_simp_rules]
  · simp [gateResult, saved, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [gateResult, saved, Udivti3.compare,
      Udivti3.next, state_simp_rules]
  · intro reg
    simp [gateResult, saved, Udivti3.compare, Udivti3.next, state_simp_rules]
  · intro a outside
    have separate := outside _ slot
    simpa [gateResult, saved, Udivti3.compare, Udivti3.next, state_simp_rules] using
      BoolCodec.write_mem_bytes_frame s (r (.GPR 31#5) s - 16#64) 8
        (r (.GPR 9#5) s) a (by bv_omega) (by bv_omega)

end SszArm.NatAdd.LargeLoop
