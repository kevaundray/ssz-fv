import SszX86.NatDivisionNormalize
import SszX86.NatDivisionOutputMemory

namespace SszX86.NatDivision
open SszNative
open SszNative.Limbs
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The machine retains the complete buffer; only the returned pair is trimmed. -/
def normalizedResultState (s : MachineData) (words : List (BitVec 64))
    (flags : StatusFlags) : MachineData :=
  let quotient := NatOperand.fromWords s.regs.r14.toBitVec words
  {s with
    regs := {s.regs with
      rax := 16
      r13 := UInt64.ofBitVec (BitVec.ofNat 64 (max 1 (sigWords words)))
      r14 := 0}
    status := flags
    dmem := resultSuccessMem s.dmem s.regs.rbx.toBitVec
      quotient.pointer quotient.payload s.regs.r15.toBitVec}

private theorem fromWords_zero (pointer : BitVec 64) (words : List (BitVec 64))
    (zero : sigWords words = 0) : NatOperand.fromWords pointer words = .small 0 := by
  have empty : trim words = [] := List.eq_nil_of_length_eq_zero (by rw [trim_length, zero])
  simp [NatOperand.fromWords, empty]

/-- Complete normalization from PC496 through the two-field publication, reason
zero, and remainder stores. Zero-, one-, and multiword representations all use
NatOperand.fromWords without changing the original written-list resource. -/
theorem normalize_result_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length+1 < 2^64) (hout : ResultMapped s)
    (hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (normalizedResultState s words flags, base + 456)) :
    Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (words.length+1)) s.regs.rax.toBitVec s.status,
        base + 496) := by
  apply normalize_scan e base hc s words bound hm P words.length (by omega)
  · intro temporary flags zero
    have hz : sigWords words = 0 := zero
    apply normalize_zero_cps e base hc
    intro flags
    apply normalize_publish_cps e base hc
    · exact hout
    intro flags
    apply result_success_tail_cps e base hc
    · repeat' first | exact hout | apply Large.mapped_store
    · rfl
    · simpa [normalizedResultState, normalizeScanState, fromWords_zero _ _ hz,
        resultSuccessMem, resultPairMem, NatOperand.pointer, NatOperand.payload, hz] using next flags
  · intro positive flags
    change Eventually (step e) P
      (normalizeScanState s (BitVec.ofNat 64 (sigWords words))
        (BitVec.ofNat 64 (sigWords words)) flags, base + 517)
    have hp : sigWords words ≠ 0 := positive
    have hsig := sigWords_le_length words
    have hmax : max 1 (sigWords words) = sigWords words := Nat.max_eq_right (by omega)
    apply normalize_select_cps e base hc
    · intro single flags
      have hsingle : sigWords words = 1 := by
        change BitVec.ofNat 64 (sigWords words) = 1#64 at single
        bv_omega
      have hword : Mem.loadInt s.dmem s.regs.r14.toBitVec 8 =
          some ((words[0]?.getD 0).toNat : Int) := by
        simpa [List.getElem?_eq_getElem (show 0 < words.length by omega)] using hm ⟨0, by omega⟩
      apply normalize_one_cps e base hc _ (words[0]?.getD 0)
      · exact hword
      intro flags
      apply normalize_publish_cps e base hc
      · exact hout
      intro flags
      apply result_success_tail_cps e base hc
      · repeat' first | exact hout | apply Large.mapped_store
      · rfl
      · simpa [normalizedResultState, normalizeScanState, resultSuccessMem, resultPairMem,
          NatOperand.fromWords_pointer, NatOperand.fromWords_payload, hsingle] using next flags
    · intro multiple flags
      have hmultiple : ¬ sigWords words ≤ 1 := by
        intro small
        have single : sigWords words = 1 := by omega
        apply multiple
        change BitVec.ofNat 64 (sigWords words) = 1#64
        rw [single]
      apply normalize_publish_cps e base hc
      · exact hout
      intro flags
      apply result_success_tail_cps e base hc
      · repeat' first | exact hout | apply Large.mapped_store
      · rfl
      · simpa [normalizedResultState, normalizeScanState, resultSuccessMem, resultPairMem,
          NatOperand.fromWords_pointer, NatOperand.fromWords_payload, hmultiple, hmax] using next flags

/-- Observation theorem includes the full quotient's stored ownership; its
normalized representation alone does not define the memory-write footprint. -/
theorem normalized_result_observed (s : MachineData) (words : List (BitVec 64))
    (flags : StatusFlags)
    (stored : (NatOperand.large s.regs.r14.toBitVec words).At
      (widthLoad (normalizedResultState s words flags).dmem)) :
    NatArithmetic.DivisionResultAt (widthLoad (normalizedResultState s words flags).dmem)
      s.regs.rbx.toNat (.ok (NatOperand.fromWords s.regs.r14.toBitVec words, s.regs.r15.toBitVec)) := by
  exact result_success_observed s.dmem s.regs.rbx.toBitVec s.regs.r15.toBitVec
    (NatOperand.fromWords s.regs.r14.toBitVec words)
    (NatOperand.fromWords_at _ _ _ stored)

end SszX86.NatDivision
