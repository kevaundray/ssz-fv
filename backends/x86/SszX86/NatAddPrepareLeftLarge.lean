import SszX86.NatAddPrepareRightLarge
import SszX86.NatAddPrepareRightSmall

namespace SszX86.NatAdd
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

private theorem scanned_dispatch (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (large : s.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 141))
    (small : s.regs.rcx.toBitVec = 0#64 → ∀ flags,
      Eventually (step e) P ({s with status := flags}, base + 96)) :
    Eventually (step e) P (s, base + 53) ∧ Eventually (step e) P (s, base + 91) := by
  have target := hc.targets ("natAdd_u141", 141) (by decide)
  constructor
  · natadd_step 17 using hc
    constructor <;> natadd_step 18 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simp [StatusFlags.from_result, zero, Effects.All]
        natadd_step 19 using hc
        exact small zero _
      · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _
  · natadd_step 29 using hc
    constructor <;> natadd_step 30 using hc
    all_goals
      by_cases zero : s.regs.rcx.toBitVec = 0#64
      · simpa [StatusFlags.from_result, zero, Effects.All] using small zero _
      · simpa [StatusFlags.from_result, zero, target, Effects.All] using large zero _

/-- The complete left-Large prefix observes its original physical list, then
routes the original right representation to its exact Small or Large path. -/
theorem prepare_left_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (p : BitVec 64) (words : List (BitVec 64)) (right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = p)
    (leftPayload : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (leftAt : (NatOperand.large p words).At (widthLoad s.dmem))
    (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s (.large p words) right base) (s, base + 15) := by
  have positive := leftAt.1
  have extent := leftAt.2.2.1
  have bound : words.length+1 < 2^64 := by omega
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [leftPointer]
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (leftAt.2.2.2 i)
  have dispatched (flags : StatusFlags) :
      Eventually (step e) (Prepared s (.large p words) right base)
        (countState s (BitVec.ofNat 64 (Limbs.sigWords words))
          (BitVec.ofNat 64 (Limbs.sigWords words+1)) s.regs.r11.toBitVec flags,
          if Limbs.sigWords words = 0 then base + 91 else base + 53) := by
    let u := countState s (BitVec.ofNat 64 (Limbs.sigWords words))
      (BitVec.ofNat 64 (Limbs.sigWords words+1)) s.regs.r11.toBitVec flags
    have next := scanned_dispatch e base hc u (Prepared s (.large p words) right base)
    have large : u.regs.rcx.toBitVec ≠ 0#64 → ∀ flags,
        Eventually (step e) (Prepared s (.large p words) right base)
          ({u with status := flags}, base + 141) := by
      intro nonzero flags
      cases right with
      | small limb => exact False.elim (nonzero rightPointer)
      | large q limbs =>
        have phase := prepare_right_large e base hc {u with status := flags} (.large p words) q limbs
          leftPointer leftPayload rightPointer rightPayload rfl leftAt rightAt
        exact eventually_weaken _ _ _ _
          (fun _ h => Prepared.rebase (s := s) (u := {u with status := flags})
            ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
    have small : u.regs.rcx.toBitVec = 0#64 → ∀ flags,
        Eventually (step e) (Prepared s (.large p words) right base)
          ({u with status := flags}, base + 96) := by
      intro zero flags
      cases right with
      | small limb =>
        have phase := prepare_right_small_scanned e base hc {u with status := flags} (.large p words) limb
          leftPointer leftPayload rightPayload rfl rfl leftAt
        exact eventually_weaken _ _ _ _
          (fun _ h => Prepared.rebase (s := s) (u := {u with status := flags})
            ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
      | large q limbs =>
        have positive := rightAt.1
        have qZero : q = 0#64 := rightPointer.symm.trans zero
        simp [qZero] at positive
    have phase := next large small
    by_cases zero : Limbs.sigWords words = 0
    · rw [ite_eq_left zero]
      exact phase.2
    · rw [ite_eq_right zero]
      exact phase.1
  have scanned := left_count e base hc s s.regs.r11.toBitVec words bound hm
    (Prepared s (.large p words) right base) words.length (by omega)
    s.regs.r10.toBitVec s.status dispatched
  apply left_count_entry_cps e base hc s
  simpa only [countState, leftPayload, BitVec.ofNat_add,
    UInt64.ofBitVec_toBitVec] using scanned

end SszX86.NatAdd
