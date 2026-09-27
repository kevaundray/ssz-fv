import SszArm.UintBodyMemory

namespace SszArm.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- A returned upstream result, measured against the original body activation. -/
def Completed (s t : ArmState) (width : Nat) (data : Ssz.Bytes) : Prop :=
  Tail.Returned s t ∧ read_err t = .None ∧
  SszNative.UintCodec.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
    (Ssz.deserialize (.uint width) data)

/-- The only unfinished continuation after scope and Small tails are discharged.
The descriptor width matched, and the full significant prefix requires allocation. -/
def AwaitAllocation (s t : ArmState) (base : BitVec 64) (width : Nat)
    (data : Ssz.Bytes) : Prop :=
  width = data.size ∧ 8 < SszNative.WordDecode.significantBytes data data.size ∧
  Small.Stable s t ∧ CodeAt t base ∧ read_err t = .None ∧
  CheckSPAlignment t ∧ Small.Input t data ∧
  read_pc t = base + 4764#64 ∧
  r (.GPR 8#5) t = BitVec.ofNat 64 (SszNative.WordDecode.significantBytes data data.size - 1) ∧
  r (.GPR 9#5) t = BitVec.ofNat 64 (SszNative.WordDecode.significantBytes data data.size)

/-- Execute the arbitrary-precision width check and trimming, and discharge both
nonallocating return paths. No bound on descriptor magnitude or trailing zeros
is imposed; the Large continuation retains the original source and activation. -/
theorem prefix_finish_or_allocate (s : ArmState) (base : BitVec 64)
    (width : Nat) (data : Ssz.Bytes) (hc : CodeAt s base)
    (hp : read_pc s = base + 148#64) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hspill : WidthScratchSeparated s) (hwidth : WidthPair s width)
    (hi : Small.Input s data) (hs : Tail.Separated s) :
    ∃ fuel t, run fuel s = t ∧
      (((width ≠ data.size ∨ SszNative.WordDecode.significantBytes data data.size ≤ 8) ∧
        Completed s t width data) ∨ AwaitAllocation s t base width data) := by
  obtain ⟨fuel, t, hrun, hstable, hcode, herr, halign, hinput, hexit⟩ :=
    prefix_runs s base width data hc hp he ha hheader hspill
      (width_at_of_pair s width hwidth) hi
  have hout := hstable.regs 0#5 (by decide)
  have hsep := hstable.tail_separated hs
  by_cases hmatch : width = data.size
  · have hsmall := hexit
    simp only [PrefixExit, hmatch, ↓reduceIte, Small.Exit] at hsmall
    by_cases hcount : SszNative.WordDecode.significantBytes data data.size ≤ 8
    · simp only [hcount, ↓reduceIte] at hsmall
      obtain ⟨hpc, hpointer, _, hvalue⟩ := hsmall
      have hn : Tail.NatPair t (r (.GPR 12#5) t) (r (.GPR 10#5) t)
          (Ssz.readUint data 0 data.size) := Or.inl ⟨hpointer, hvalue⟩
      obtain ⟨hreturn, herror, hresult⟩ := Tail.success_correct t base
        (Ssz.readUint data 0 data.size) hcode hpc herr halign hsep hn
      refine ⟨fuel + 22, run 22 t, ?_,
        Or.inl ⟨Or.inr hcount, hstable.returned hs hreturn, herror, ?_⟩⟩
      · rw [run_plus, hrun]
      · apply SszNative.UintCodec.result_refines width data
        simpa only [SszNative.WordDecode.outcome, hmatch,
          SszNative.WordDecode.decode_value, ↓reduceIte, hout] using hresult
    · simp only [hcount, ↓reduceIte] at hsmall
      refine ⟨fuel, t, hrun, Or.inr ?_⟩
      exact ⟨hmatch, by omega, hstable, hcode, herr, halign, hinput, hsmall⟩
  · simp only [PrefixExit, hmatch, ↓reduceIte] at hexit
    obtain ⟨hpc, h8, h9⟩ := hexit
    have hn : Tail.NatPair t (r (.GPR 8#5) t) (r (.GPR 9#5) t) width := by
      rw [h8, h9]
      exact hstable.nat_pair _ _ width hwidth
    have hlen : (r (.GPR 3#5) t).toNat = data.size := by
      have hl := hinput.length
      change r (.GPR 3#5) t = BitVec.ofNat 64 data.size at hl
      rw [hl]
      exact Nat.mod_eq_of_lt (by have := hinput.bounded; omega)
    obtain ⟨hreturn, herror, hresult⟩ := Tail.scope_correct t base width
      hcode hpc herr halign hsep hn
    refine ⟨fuel + 55, run 55 t, ?_,
      Or.inl ⟨Or.inl hmatch, hstable.returned hs hreturn, herror, ?_⟩⟩
    · rw [run_plus, hrun]
    · apply SszNative.UintCodec.result_refines width data
      simpa only [SszNative.WordDecode.outcome, Ne.symm hmatch,
        ↓reduceIte, hout, hlen] using hresult

end SszArm.UintCodec
