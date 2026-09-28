import SszX86.NatMulWordResultFinish
import SszNatOperandNormalization

namespace SszX86.NatMulWord
open SszNative UintCodec

/-- Scan the full written allocation and recover the canonical result pair,
reloading its low limb from the preserved local spill exactly as the image does. -/
theorem normalize_result_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length+1 < 2^64)
    (counter : s.regs.rbx.toBitVec = BitVec.ofNat 64 (words.length+1))
    (lowLoad : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some ((words[0]?.getD 0).toNat : Int))
    (stored : NatMemory.wordsAt (widthLoad s.dmem) s.regs.r14.toNat words)
    (P : MachineState → Prop)
    (next : ∀ t, t.dmem = s.dmem → t.regs.rsp = s.regs.rsp → t.regs.rdi = s.regs.rdi →
      t.zmms = s.zmms →
      t.regs.r14.toBitVec = (NatOperand.fromWords s.regs.r14.toBitVec words).pointer →
      t.regs.rax.toBitVec = (NatOperand.fromWords s.regs.r14.toBitVec words).payload →
      Eventually (step e) P (t, base+799)) :
    Eventually (step e) P (s, base+741) := by
  let seed : MachineData := {s with regs := {s.regs with rax := 0}}
  have hm : ∀ i : Fin words.length,
      Mem.loadInt seed.dmem (seed.regs.r14.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    have observed := stored i
    change widthLoad s.dmem (s.regs.r14.toBitVec.toNat+8*i.val) 8 = some words[i].toNat at observed
    simpa only [seed, width_address] using widthLoad_eq s.dmem _ _ _ observed
  have scanned (flags : StatusFlags) : Eventually (step e) P
      (resultNormalizeState seed (BitVec.ofNat 64 (words.length+1)) s.regs.rcx.toBitVec flags, base+752) := by
    apply result_normalize_scan e base hc seed words bound hm P words.length (by omega)
    · intro d flags zero
      have nil : Limbs.trim words = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa only [Limbs.trim_length, Limbs.sigWords] using zero
      have normalized : NatOperand.fromWords s.regs.r14.toBitVec words = .small 0#64 := by
        simp only [NatOperand.fromWords, nil]
      apply result_normalize_zero e base hc
      intro flags
      apply next
      · rfl
      · rfl
      · rfl
      · rfl
      · simp only [normalized, NatOperand.pointer, UInt64.toBitVec_ofNat]
      · simp only [normalized, NatOperand.payload, resultNormalizeState, seed, UInt64.toBitVec_ofNat]
    · intro nonzeroCount flags
      have positive : 0 < Limbs.sigWords words := by
        change Limbs.sigWords words ≠ 0 at nonzeroCount
        omega
      have countBound : Limbs.sigWords words < 2^64 := by
        have := Limbs.sigWords_le_length words
        omega
      apply result_normalize_publish e base hc seed _ (BitVec.ofNat 64 (Limbs.sigWords words))
        (words[0]?.getD 0) flags lowLoad
      intro flags
      apply next
      · rfl
      · rfl
      · rfl
      · rfl
      · simp only [resultPairState, seed, NatOperand.fromWords_pointer]
        by_cases one : Limbs.sigWords words = 1
        · simp [one]
        · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
          have notOne : BitVec.ofNat 64 (Limbs.sigWords words) ≠ 1#64 := by bv_omega
          simp [many, notOne]
      · simp only [resultPairState, UInt64.toBitVec_ofBitVec, seed, NatOperand.fromWords_payload]
        by_cases one : Limbs.sigWords words = 1
        · simp only [one, Nat.le_refl, ↓reduceIte]
        · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
          have notOne : BitVec.ofNat 64 (Limbs.sigWords words) ≠ 1#64 := by bv_omega
          simp [many, notOne]
  apply result_normalize_entry e base hc s P
  intro flags
  simpa only [resultNormalizeState, seed, ← counter, UInt64.ofBitVec_toBitVec] using scanned flags

end SszX86.NatMulWord
