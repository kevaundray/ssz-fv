import SszX86.NatAddCarryPairLoop
import SszX86.NatAddCarryTail

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def Retained (s t : MachineData) : Prop :=
  t.regs.rax = s.regs.rax ∧ t.regs.r9 = s.regs.r9 ∧ t.regs.r10 = s.regs.r10 ∧
  t.regs.rdi = s.regs.rdi ∧ t.regs.rsp = s.regs.rsp ∧ t.zmms = s.zmms

theorem fill_mapped (m : DataMem) (dst : BitVec 64) (index capacity : Nat)
    (limbs : List (BitVec 64)) (hmapped : Large.Mapped m dst capacity) :
    Large.Mapped (Large.fillMem m dst index limbs) dst capacity := by
  induction limbs generalizing m index with
  | nil => exact hmapped
  | cons first rest ih =>
    exact ih _ _ (Large.mapped_store _ _ _ _ _ _ hmapped)

/-- All paired iterations and the parity tail write exactly `count` remaining
limbs, retaining the redundant final word also when its value is zero. -/
theorem small_loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer dst : BitVec 64) (right : List (BitVec 64))
    (count carry : Nat) (wide : 2 ≤ count) (physical : count+1 < 2^64) (carryBound : carry ≤ 1)
    (owned : (NatOperand.large pointer right).At (widthLoad s.dmem))
    (apart : Apart (.large pointer right) dst (8*(count+1)))
    (hmapped : Large.Mapped s.dmem dst (8*(count+1)))
    (rax : get s .rax = BitVec.ofNat 64 count)
    (rcx : get s .rcx = pointer) (r8 : get s .r8 = BitVec.ofNat 64 right.length)
    (r10 : get s .r10 = dst) (rbx : get s .rbx = dst+8#64)
    (rsi : get s .rsi = 1#64) (r11 : get s .r11 = BitVec.ofNat 64 (2*(count/2)))
    (r14 : get s .r14 = BitVec.ofNat 64 carry)
    (P : MachineState → Prop)
    (hp : ∀ t, Retained s t →
      t.dmem = Large.fillMem s.dmem dst 1 (LimbAdd.loop count [] (right.drop 1) carry).1 →
      Eventually (step e) P (t, base+1325)) :
    Eventually (step e) P (s, base+1252) := by
  apply Pair.loop_cps e base hc pointer dst right (count+1) apart physical P (count/2)
    (by omega) 1 (by omega) (by omega) s carry carryBound rcx r8 rbx rsi
  · simpa using r11
  · exact r14
  · exact owned
  · exact hmapped
  intro t stable lastIndex lastCarry memory
  change get t .rdx = BitVec.ofNat 64 (1+2*(count/2)-2) at lastIndex
  change get t .r14 = BitVec.ofNat 64 (LimbAdd.loop (2*(count/2)) [] (right.drop 1) carry).2 at lastCarry
  have retained : Retained s t :=
    ⟨stable.1, stable.2.2.2.1, stable.2.2.2.2.1, stable.2.2.2.2.2.2.2.1,
      stable.2.2.2.2.2.2.2.2.1, stable.2.2.2.2.2.2.2.2.2⟩
  have tRax : get t .rax = BitVec.ofNat 64 count := by
    simpa only [get, Reg64s.get64, stable.1] using rax
  by_cases even : count%2 = 0
  · have countEven : 2*(count/2) = count := by omega
    apply Pair.even_tail_cps e base hc t
    · rw [tRax]
      exact (parity_test count).mpr even
    intro flags
    apply hp {t with status := flags} retained
    simpa only [countEven] using memory
  · have countOdd : 2*(count/2)+1 = count := by omega
    let consumed := LimbAdd.loop (2*(count/2)) [] (right.drop 1) carry
    let limb := limbAt right count
    have nextIndex : get t .rdx + 2#64 = BitVec.ofNat 64 count := by
      rw [lastIndex]
      bv_omega
    have tRcx : get t .rcx = pointer := by
      simpa only [get, Reg64s.get64, stable.2.1] using rcx
    have tR8 : get t .r8 = BitVec.ofNat 64 right.length := by
      simpa only [get, Reg64s.get64, stable.2.2.1] using r8
    have tR10 : get t .r10 = dst := by
      simpa only [get, Reg64s.get64, stable.2.2.2.2.1] using r10
    have tOwned : (NatOperand.large pointer right).At (widthLoad t.dmem) := by
      rw [memory]
      apply fill_preserves s.dmem (.large pointer right) dst 1 (8*(count+1))
        _ owned apart
      rw [LimbAdd.loop_length]
      omega
    have tMapped : Large.Mapped t.dmem dst (8*(count+1)) := by
      rw [memory]
      exact fill_mapped _ _ _ _ _ hmapped
    apply Pair.odd_tail_cps e base hc t limb
    · rw [tRax]
      exact fun h => even ((parity_test count).mp h)
    · have h := fetch_word t.dmem (.large pointer right) count tOwned (by omega) (by omega)
      simpa [nextIndex, tRcx, tR8, isSmall, NatOperand.pointer, NatOperand.payload,
        NatOperand.words, limb] using h
    · rw [nextIndex, tR10]
      simpa [BitVec.ofNat_mul, Nat.mul_comm] using
        Large.mapped_load t.dmem dst (8*(count+1)) (8*count) 8 tMapped (by omega)
    intro flags
    apply hp (Pair.tailState t limb flags)
    · simpa [Retained, Pair.tailState] using retained
    have arithmetic := one_add limb consumed.2 (LimbAdd.loop_carry_le _ _ _ carry carryBound)
    have low : limb + get t .r14 = (LimbAdd.step 0 limb consumed.2).1 := by
      rw [lastCarry]
      simpa [consumed, BitVec.add_comm] using arithmetic.1
    have splitLoop := loop_split (2*(count/2)) 1 1 [] right carry
    simp only [List.drop_nil] at splitLoop
    rw [countOdd] at splitLoop
    rw [show 1+2*(count/2) = count by omega] at splitLoop
    simp only [LimbAdd.loop, List.head?_nil, Option.getD_none,
      List.head?_drop] at splitLoop
    change Mem.storeInt t.dmem (get t .r10 + (get t .rdx+2#64)*8#64) 8
      (limb+get t .r14).toInt = _
    rw [nextIndex, tR10, low, memory, splitLoop, fill_append]
    simp [consumed, limb, limbAt, Large.fillMem, LimbAdd.loop_length,
      show 1+2*(count/2) = count by omega, BitVec.ofNat_mul, Nat.mul_comm]

end SszX86.NatAdd.Carry
