import SszX86.NatAddCarrySmallEntry
import SszX86.NatAddCarrySmallLoop
import SszX86.NatAddCarryPost

namespace SszX86.NatAdd.Carry
open SszNative
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Complete Small-left/Large-right allocation-success phase. Only the original
physical representation supplies loads; significant count controls the writes. -/
theorem small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (left pointer dst : BitVec 64) (right : List (BitVec 64))
    (owned : (NatOperand.large pointer right).At (widthLoad s.dmem))
    (wide : 2 ≤ SszNative.NatAdd.count (.small left) (.large pointer right))
    (mapped : Large.Mapped s.dmem dst
      (8*(SszNative.NatAdd.count (.small left) (.large pointer right)+1)))
    (apart : Apart (.large pointer right) dst
      (8*(SszNative.NatAdd.count (.small left) (.large pointer right)+1)))
    (bound : dst.toNat + 8*(SszNative.NatAdd.count (.small left) (.large pointer right)+1) ≤ 2^64)
    (rsi : get s .rsi = 0) (rdx : get s .rdx = left)
    (rcx : get s .rcx = pointer) (r8 : get s .r8 = BitVec.ofNat 64 right.length)
    (rax : get s .rax = BitVec.ofNat 64 (SszNative.NatAdd.count (.small left) (.large pointer right)))
    (r10 : get s .r10 = dst) (rbx : get s .rbx = dst)
    (r11 : get s .r11 = 2305843009213693950#64)
    (P : MachineState → Prop)
    (hp : ∀ t, Post s (.small left) (.large pointer right) dst t →
      Eventually (step e) P (t, base+1325)) :
    Eventually (step e) P (s, base+536) := by
  let count := SszNative.NatAdd.count (.small left) (.large pointer right)
  let limb := limbAt right 0
  let next := LimbAdd.step left limb 0
  have countBound : count < 2^61 := by dsimp [count]; omega
  have countPhysical : count+1 < 2^64 := by omega
  have rightPhysical : right.length < 2^64 := by have := owned.2.2.1; omega
  have lengthPositive : 0 < right.length := by
    have significant := Limbs.sigWords_le_length right
    simp only [SszNative.NatAdd.count, NatOperand.wordCount, NatOperand.words,
      NatCompare.single_sig] at wide
    split at wide <;> omega
  have nonzeroPointer : get s .rcx ≠ 0 := by
    rw [rcx]
    intro zero
    have positive := owned.1
    simp [zero] at positive
  have nonzeroLength : get s .r8 ≠ 0 := by rw [r8]; bv_omega
  have countNeOne : get s .rax ≠ 1#64 := by rw [rax]; dsimp [count] at countBound; bv_omega
  have load : Mem.loadInt s.dmem (get s .rcx) 8 = some (limb.toNat : Int) := by
    have h := widthLoad_eq s.dmem _ _ _ (owned.2.2.2 ⟨0,lengthPositive⟩)
    simpa [rcx, width_address, limb, limbAt, List.getElem?_eq_getElem lengthPositive] using h
  have low : left+limb = next.1 := by
    simpa [next, BitVec.add_comm] using (two_adds left limb 0 (by omega)).1
  have high : (Udivti3.addFlags left limb).cf.toNat = next.2 := by
    rw [Udivti3.addFlags_cf]
    simp only [next, LimbAdd.step, Nat.add_zero, Udivti3.radix]
    have hl := left.isLt
    have hr := limb.isLt
    by_cases overflow : 2^64 ≤ left.toNat+limb.toNat <;> simp [overflow] <;> omega
  apply Pair.small_entry_cps e base hc s limb rsi nonzeroPointer nonzeroLength countNeOne load
  · rw [r10]
    exact Delimited.mapped_load_zero _ _ _ 8 mapped (by omega)
  intro flags
  let head := Pair.headState s limb flags
  have headMemory : head.dmem = Large.fillMem s.dmem dst 0 [next.1] := by
    simp [head, Pair.headState, Pair.get, r10, rdx, low, Large.fillMem]
  apply small_loop_cps e base hc head pointer dst right count next.2 wide countPhysical
    (LimbAdd.step_carry_le left limb 0 (by omega))
  · rw [headMemory]
    exact fill_preserves s.dmem (.large pointer right) dst 0 (8*(count+1))
      [next.1] owned apart (by simp; omega)
  · exact apart
  · rw [headMemory]
    exact Large.mapped_store _ _ _ _ _ _ mapped
  · simpa [head, Pair.headState, Pair.get, get, count] using rax
  · simpa [head, Pair.headState, Pair.get, get] using rcx
  · simpa [head, Pair.headState, Pair.get, get] using r8
  · simpa [head, Pair.headState, Pair.get, get] using r10
  · simp [head, Pair.headState, Pair.get, get, rbx]
  · simp [head, Pair.headState, Pair.get, get]
  · simpa [head, Pair.headState, Pair.get, get, r11, rax, count] using even_mask count countBound
  · simp [head, Pair.headState, Pair.get, get, rdx, high]
  intro final retained finalMemory
  apply hp final
  apply post_of_fill s final (.small left) (.large pointer right) dst (by trivial)
    owned (by trivial) apart bound
  · simpa only [retained.1, head, Pair.headState] using rax
  · simpa only [retained.2.2.1, head, Pair.headState] using r10
  · simp [retained.2.1, head, Pair.headState, Pair.get, rdx, low, next,
      NatOperand.words, limbAt, limb]
  · exact retained.2.2.2.1
  · exact retained.2.2.2.2.1
  · exact retained.2.2.2.2.2
  · rw [finalMemory, headMemory, SszNative.NatAdd.writtenWords_native_loop]
    change Large.fillMem (Large.fillMem s.dmem dst 0 [next.1]) dst 1
      (LimbAdd.loop count [] (right.drop 1) next.2).1 =
        Large.fillMem s.dmem dst 0 (LimbAdd.loop (count+1) [left] right 0).1
    simp [Large.fillMem, LimbAdd.loop, next, limb, limbAt, List.drop_succ]

end SszX86.NatAdd.Carry
