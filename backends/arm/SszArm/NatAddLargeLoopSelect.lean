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

private theorem gate_flag_pc (s : ArmState) (flag : PFlag)
    (value : BitVec 1) (pc : BitVec 64) :
    w (.FLAG flag) value (w .PC pc s) = w .PC pc (w (.FLAG flag) value s) :=
  w_of_w_commute (by intro equal; cases equal)

/-- Control-flow evidence is proved without a code-image or execution hypothesis
in the simplifier context. The comparison is unsigned for all physical counts. -/
private theorem gate_follows (s : ArmState) (base : BitVec 64)
    (kind : GateKind) (small : Bool)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (h13 : r (.GPR 13#5) s = if small then 1#64 else 0#64)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 9#5) =
      r (.GPR 9#5) s) :
    Follows base (gateOps kind
      (decide ((r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat)) small) s := by
  have carry : (AddWithCarry (r (.GPR 15#5) s) (~~~r (.GPR 4#5) s) 1#1).2.c = 1#1 ↔
      ¬ (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat := by
    rw [Udivti3.cmp_carry]
    omega
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  simp only [saved] at restore
  by_cases within : (r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat <;>
    cases kind <;> cases small <;>
    simp [gateOps, GateKind.start, Follows, Op.row, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, state_simp_rules, load_store_field,
      load_gpr_pc, gate_flag_pc, restore, hpc, h13, carry, within,
      BitVec.sub_add_cancel, BitVec.add_assoc]

/-- The same opaque temporary-restoration algebra handles both copies and all
four bit choices; the instruction enum is never crossed with state components. -/
private theorem gate_effect (s : ArmState) (base : BitVec 64)
    (kind : GateKind) (within small : Bool)
    (h13 : r (.GPR 13#5) s = if small then 1#64 else 0#64)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 9#5) =
      r (.GPR 9#5) s) :
    block base (gateOps kind within small) s = gateResult s base within small := by
  let bit : BitVec 64 := if within then (if small then 1#64 else 0#64) else 1#64
  let body := w (.GPR 17#5) bit
    (saved (Udivti3.compare (r (.GPR 15#5) s) (r (.GPR 4#5) s) s) 9#5)
  have restored := store_restore_fields body 9#5 bit (by decide)
  have final := congrArg
    (w .PC (base + if within && !small then 1572#64 else 1860#64)) restored
  simp only [saved] at restore
  cases kind <;> cases within <;> cases small <;>
    simpa [gateOps, gateResult, bit, body, block, Op.effect, put, next,
      Udivti3.compare, Udivti3.next, saved, state_simp_rules,
      load_store_field, load_gpr_pc, gate_flag_pc, restore, h13,
      BitVec.sub_add_cancel, BitVec.add_assoc] using final

theorem gate_run (s : ArmState) (base : BitVec 64) (kind : GateKind) (small : Bool)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (h13 : r (.GPR 13#5) s = if small then 1#64 else 0#64) :
    let within := decide ((r (.GPR 15#5) s).toNat < (r (.GPR 4#5) s).toNat)
    run (gateOps kind within small).length s = gateResult s base within small := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s 9#5) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  dsimp only
  rw [block_run base _ s hc he ha (gate_follows s base kind small hp h13 restore)]
  exact gate_effect s base kind _ small h13 restore

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
    simpa [gateResult, saved, Udivti3.compare, Udivti3.next,
      state_simp_rules, NatCompare.spill_mem_w, ArmState.mem_w_eq_mem] using
      BoolCodec.write_mem_bytes_frame s (r (.GPR 31#5) s - 16#64) 8
        (r (.GPR 9#5) s) a (by bv_omega) (by bv_omega)

end SszArm.NatAdd.LargeLoop
