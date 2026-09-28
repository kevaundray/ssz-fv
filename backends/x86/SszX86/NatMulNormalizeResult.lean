import SszX86.NatMulScanResult
import SszNatOperandNormalization

namespace SszX86.NatMul
open SszNative
open UintCodec

def resultPairState (s : MachineData) (p v : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rdx := UInt64.ofBitVec p, rcx := UInt64.ofBitVec v}, status := flags}

theorem result_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (resultPairState s 0 0 flags, base + 727)) :
    Eventually (step e) P (s, base + 723) := by
  natmul_step 6 row 11 using hc
  constructor <;> natmul_step 6 row 12 using hc
  all_goals constructor <;> simpa [resultPairState] using next _

theorem result_nonzero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (count : Nat) (positive : 0 < count) (bound : count < 2^64)
    (counter : s.regs.rcx.toBitVec = BitVec.ofNat 64 count - 1)
    (limb : BitVec 64)
    (first : count = 1 → Mem.loadInt s.dmem s.regs.rdx.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (resultPairState s (if count = 1 then 0 else s.regs.rdx.toBitVec)
        (if count = 1 then limb else BitVec.ofNat 64 count) flags, base + 727)) :
    Eventually (step e) P (s, base + 693) := by
  have target := hc.targets ("natMul_u727", 727) (by decide)
  have increment : s.regs.rcx + 1 = (OfNat.ofNat count : UInt64) := by
    apply UInt64.toBitVec_inj.1
    change s.regs.rcx.toBitVec + 1#64 = BitVec.ofNat 64 count
    rw [counter]
    bv_omega
  natmul_step 6 row 1 using hc
  simp only [increment]
  natmul_step 6 row 2 using hc
  natmul_step 6 row 3 using hc
  by_cases one : count = 1
  · have eqOne : BitVec.ofNat 64 count = 1#64 := by simp [one]
    simp [StatusFlags.from_result, eqOne, Effects.All]
    natmul_step 6 row 4 using hc
    natmul_load (first one)
    natmul_step 6 row 5 using hc
    natmul_step 6 row 12 using hc
    constructor <;> simpa [resultPairState, one] using next _
  · have neOne : BitVec.ofNat 64 count ≠ 1#64 := by bv_omega
    simpa [StatusFlags.from_result, neOne, target, resultPairState, one, Effects.All] using next _

theorem normalize_result_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64)) (bound : words.length < 2^64)
    (counter : s.regs.rbp.toBitVec = BitVec.ofNat 64 words.length - 1)
    (stored : NatMemory.wordsAt (widthLoad s.dmem) s.regs.rdx.toNat words)
    (P : MachineState → Prop)
    (next : ∀ t, t.dmem = s.dmem → t.regs.rsp = s.regs.rsp → t.regs.rax = s.regs.rax →
      t.zmms = s.zmms →
      t.regs.rdx.toBitVec = (NatOperand.fromWords s.regs.rdx.toBitVec words).pointer →
      t.regs.rcx.toBitVec = (NatOperand.fromWords s.regs.rdx.toBitVec words).payload →
      Eventually (step e) P (t, base + 727)) :
    Eventually (step e) P (s, base + 674) := by
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    have observed := stored i
    change widthLoad s.dmem (s.regs.rdx.toBitVec.toNat + 8*i.val) 8 = some words[i].toNat at observed
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ observed
  have scanned := result_scan e base hc s words bound hm P words.length (by omega)
    s.regs.rcx.toBitVec s.status
  have initial : resultScanState s (BitVec.ofNat 64 words.length - 1) s.regs.rcx.toBitVec s.status = s := by
    rw [← counter]
    simp only [resultScanState, UInt64.ofBitVec_toBitVec]
  rw [← initial]
  apply scanned
  · intro c flags zero
    have nil : Limbs.trim words = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa only [Limbs.trim_length, Limbs.sigWords] using zero
    have normalized : NatOperand.fromWords s.regs.rdx.toBitVec words = .small 0#64 := by
      simp only [NatOperand.fromWords, nil]
    apply result_zero_cps e base hc
    intro flags
    apply next
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [normalized, NatOperand.pointer, resultPairState, UInt64.toBitVec_ofBitVec]
      rfl
    · simp only [normalized, NatOperand.payload, resultPairState, UInt64.toBitVec_ofBitVec]
      rfl
  · intro nonzero flags
    have positive : 0 < Limbs.sigWords words := by
      change Limbs.sigWords words ≠ 0 at nonzero
      omega
    have countBound : Limbs.sigWords words < 2^64 := by
      have := Limbs.sigWords_le_length words
      omega
    apply result_nonzero_cps e base hc _ (Limbs.sigWords words) positive countBound rfl
      (words[0]?.getD 0)
    · intro one
      have nonempty : 0 < words.length := by
        have := Limbs.sigWords_le_length words
        omega
      have loaded := hm ⟨0, nonempty⟩
      change Mem.loadInt s.dmem (s.regs.rdx.toBitVec + 0#64) 8 = some (words[0].toNat : Int) at loaded
      simpa only [resultScanState, List.getElem?_eq_getElem nonempty, Option.getD_some,
        BitVec.add_zero] using loaded
    intro flags
    apply next
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [resultPairState, resultScanState, UInt64.toBitVec_ofBitVec,
        NatOperand.fromWords_pointer]
      by_cases one : Limbs.sigWords words = 1
      · simp [one]
      · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
        simp [one, many]
    · simp only [resultPairState, resultScanState, UInt64.toBitVec_ofBitVec,
        NatOperand.fromWords_payload]
      by_cases one : Limbs.sigWords words = 1
      · simp [one]
      · have many : ¬ Limbs.sigWords words ≤ 1 := by omega
        simp [one, many]

end SszX86.NatMul
