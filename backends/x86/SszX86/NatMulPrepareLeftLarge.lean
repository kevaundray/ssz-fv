import SszX86.NatMulPrepareDispatch

namespace SszX86.NatMul
open SszNative
open UintCodec

theorem prepare_left_large (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (p : BitVec 64) (words : List (BitVec 64)) (right : NatOperand)
    (leftPointer : s.regs.rsi.toBitVec = p)
    (leftPayload : s.regs.rdx.toBitVec = BitVec.ofNat 64 words.length)
    (rightPointer : s.regs.rcx.toBitVec = right.pointer)
    (rightPayload : s.regs.r8.toBitVec = right.payload)
    (counter : s.regs.r12.toBitVec = BitVec.ofNat 64 (words.length+1))
    (leftAt : (NatOperand.large p words).At (widthLoad s.dmem))
    (rightAt : right.At (widthLoad s.dmem)) :
    Eventually (step e) (Prepared s (.large p words) right base) (s, base + 32) := by
  have extent := leftAt.2.2.1
  have bound : words.length+1 < 2^64 := by omega
  have hm : ∀ i : Fin words.length,
      Mem.loadInt s.dmem (s.regs.rsi.toBitVec + BitVec.ofNat 64 (8*i.val)) 8 =
        some (words[i].toNat : Int) := by
    intro i
    rw [leftPointer]
    simpa only [width_address] using widthLoad_eq s.dmem _ _ _ (leftAt.2.2.2 i)
  have scanned := left_scan e base hc s words bound hm
    (Prepared s (.large p words) right base) words.length (by omega)
    s.regs.r10.toBitVec s.status
  have initial : leftScanState s s.regs.r10.toBitVec (BitVec.ofNat 64 (words.length+1)) s.status = s := by
    rw [← counter]
    simp only [leftScanState, UInt64.ofBitVec_toBitVec]
  rw [← initial]
  apply scanned
  · intro flags zero
    have phase := prepare_zero_dispatch e base hc (leftScanState s 1 1 flags) (.large p words) right
      leftPointer leftPayload rightPointer rightPayload zero
      (by simpa only [NatOperand.wordCount, NatOperand.words, Limbs.sigWords, zero]) leftAt rightAt
    exact eventually_weaken _ _ _ _
      (fun _ h => Prepared.rebase ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase
  · intro nonzero flags
    have phase := prepare_scanned_dispatch e base hc
      (leftScanState s (BitVec.ofNat 64 (Limbs.sigWords words+1))
        (BitVec.ofNat 64 (Limbs.sigWords words)) flags) (.large p words) right
      leftPointer leftPayload rightPointer rightPayload rfl rfl leftAt rightAt
    exact eventually_weaken _ _ _ _
      (fun _ h => Prepared.rebase ⟨rfl, rfl, rfl, rfl, rfl⟩ h) phase

end SszX86.NatMul
