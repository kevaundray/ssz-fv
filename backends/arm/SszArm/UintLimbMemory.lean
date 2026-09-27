import SszArm.UintLimbExec
import SszArm.UintWidthMemory

namespace SszArm.UintCodec.Large

open SszNative.WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Only these loop temporaries die. The descriptor, x9, x0, source arguments,
x19--x30, and SP remain live. -/
def Live (i : BitVec 5) : Prop :=
  i ≠ 1#5 ∧ i ≠ 4#5 ∧ i ≠ 5#5 ∧ i ≠ 8#5 ∧ i ≠ 13#5 ∧
  i ≠ 14#5 ∧ i ≠ 16#5 ∧ i ≠ 17#5 ∧ i ≠ 18#5

instance (i : BitVec 5) : Decidable (Live i) := by unfold Live; infer_instance

/-- `lo,hi` are absolute bounds of the writable destination suffix. -/
structure Stable (lo hi : Nat) (s t : ArmState) : Prop where
  program : t.program = s.program
  err : read_err t = read_err s
  regs : ∀ i, Live i → r (.GPR i) t = r (.GPR i) s
  simd : ∀ i, r (.SFP i) t = r (.SFP i) s
  frame : ∀ a : BitVec 64, (a.toNat < lo ∨ hi ≤ a.toNat) →
    (a.toNat < (r (.GPR 31) s).toNat - 16 ∨ (r (.GPR 31) s).toNat ≤ a.toNat) →
    t.mem a = s.mem a

theorem Stable.refl (lo hi : Nat) (s : ArmState) : Stable lo hi s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem Stable.trans {lo hi : Nat} {s t u : ArmState}
    (h : Stable lo hi s t) (g : Stable lo hi t u) : Stable lo hi s u := by
  refine ⟨g.program.trans h.program, g.err.trans h.err,
    fun i hi => (g.regs i hi).trans (h.regs i hi),
    fun i => (g.simd i).trans (h.simd i), ?_⟩
  intro a hd hs
  exact (g.frame a hd (by simpa only [h.regs 31 (by decide)] using hs)).trans (h.frame a hd hs)

theorem Stable.enlarge {lo hi lo' hi' : Nat} {s t : ArmState}
    (h : Stable lo hi s t) (hl : lo' ≤ lo) (hh : hi ≤ hi') : Stable lo' hi' s t := by
  refine ⟨h.program, h.err, h.regs, h.simd, ?_⟩
  intro a hd hs
  exact h.frame a (by omega) hs

theorem Stable.allow {s t : ArmState} (h : Stable 0 0 s t) (lo hi : Nat) :
    Stable lo hi s t :=
  ⟨h.program, h.err, h.regs, h.simd, fun a _ hs => h.frame a (Or.inr (Nat.zero_le _)) hs⟩

theorem Stable.code {lo hi : Nat} {s t : ArmState} {base : BitVec 64}
    (h : Stable lo hi s t) (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem Stable.aligned {lo hi : Nat} {s t : ArmState}
    (h : Stable lo hi s t) (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, bitvec_rules, minimal_theory,
    h.regs 31#5 (by decide)] using ha

/-- A caller-owned allocation; arena metadata is deliberately absent. The loop
writes only this region and its lowering spill. -/
structure Area (s : ArmState) (data : Ssz.Bytes) (pointer : BitVec 64) (count : Nat) : Prop where
  input : Small.Input s data
  nonnull : 0 < pointer.toNat
  aligned : pointer.toNat % 8 = 0
  range : pointer.toNat + 8 * ((count+7)/8) ≤ 2^64
  source : pointer.toNat + 8 * ((count+7)/8) ≤ (r (.GPR 2) s).toNat ∨
    (r (.GPR 2) s).toNat + data.size ≤ pointer.toNat
  scratch : pointer.toNat + 8 * ((count+7)/8) ≤ (r (.GPR 31) s).toNat - 16 ∨
    (r (.GPR 31) s).toNat ≤ pointer.toNat

theorem Stable.area {lo hi count : Nat} {s t : ArmState} {data : Ssz.Bytes}
    {pointer : BitVec 64} (h : Stable lo hi s t) (a : Area s data pointer count)
    (hl : pointer.toNat ≤ lo) (hh : hi ≤ pointer.toNat + 8*((count+7)/8)) :
    Area t data pointer count := by
  have h2 := h.regs 2 (by decide)
  have h3 := h.regs 3 (by decide)
  have h31 := h.regs 31 (by decide)
  refine ⟨?_, a.nonnull, a.aligned, a.range, ?_, ?_⟩
  · refine ⟨h3.trans a.input.length, a.input.bounded, ?_, ?_, ?_, ?_⟩
    · simpa only [h2] using a.input.range
    · simpa only [h31] using a.input.stack
    · simpa only [h2, h31] using a.input.separated
    · intro i hin
      rw [h2, BoolCodec.read_one]
      change t.mem (r (.GPR 2) s + BitVec.ofNat 64 i) = _
      rw [h.frame _ (by have := a.source; have := a.input.range; bv_omega)
        (by have := a.input.separated; have := a.input.range; bv_omega)]
      simpa only [BoolCodec.read_one, read_mem, read_store] using a.input.bytes i hin
  · simpa only [h2] using a.source
  · simpa only [h31] using a.scratch

/-- Recursive presentation of the same absolute word observer as `wordsAt`. -/
def Stored (s : ArmState) (address : Nat) : List (BitVec 64) → Prop
  | [] => True
  | word :: words => read_mem_bytes 8 (BitVec.ofNat 64 address) s = word ∧
      Stored s (address+8) words

theorem Stored.wordsAt {s : ArmState} {address : Nat} {ws : List (BitVec 64)}
    (h : Stored s address ws) : SszNative.NatMemory.wordsAt (widthLoad s) address ws := by
  induction ws generalizing address with
  | nil => intro i; exact Fin.elim0 i
  | cons w ws ih =>
    intro i
    rcases h with ⟨hw, ht⟩
    cases i using Fin.cases with
    | zero => simpa [widthLoad] using congrArg (fun x : BitVec 64 => some x.toNat) hw
    | succ i =>
      change widthLoad s (address + 8 * (i.val + 1)) 8 = some ws[i].toNat
      have := ih ht i
      simpa only [widthLoad, Fin.val_succ, List.getElem_cons_succ,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Every byte of a framed read remains identical. -/
theorem Stable.read {lo hi : Nat} {s t : ArmState} (h : Stable lo hi s t)
    (address : Nat) (width : Nat) (hrange : address + width ≤ 2^64)
    (hd : address + width ≤ lo ∨ hi ≤ address)
    (hs : address + width ≤ (r (.GPR 31) s).toNat - 16 ∨
      (r (.GPR 31) s).toNat ≤ address) :
    read_mem_bytes width (BitVec.ofNat 64 address) t =
      read_mem_bytes width (BitVec.ofNat 64 address) s := by
  apply BoolCodec.read_bytes_congr
  intro i hi
  apply h.frame <;> bv_omega

/-- Register writes do not change the spill's memory image. -/
theorem spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n*8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem :=
  mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

theorem read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m*8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (spill_mem_w s f v m dst value)) n addr

end SszArm.UintCodec.Large
