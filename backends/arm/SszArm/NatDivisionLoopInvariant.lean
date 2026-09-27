import SszArm.NatDivisionLoopIteration

namespace SszArm.NatDivision

open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem loopFrame_prefix {sp pointer : BitVec 64} {small large : Nat} {s t : ArmState}
    (frame : LoopFrame (loopWrites sp pointer small) s t) (h : small ≤ large) :
    LoopFrame (loopWrites sp pointer large) s t := by
  refine ⟨frame.program, frame.error, frame.registers, frame.sfp, ?_⟩
  intro a outside
  apply frame.memory a
  intro span member
  simp only [loopWrites, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [loopWrites])
  · have := outside (pointer.toNat, 8 * large) (by simp [loopWrites])
    simp only [Prod.fst, Prod.snd] at *
    omega

theorem loopIteration_full_frame (s : ArmState) (base : BitVec 64) (count i : Nat)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
    (hi : i < count) (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * i)) :
    LoopFrame (loopWrites (r (.GPR 31#5) s) (r (.GPR 24#5) s) count)
      s (loopIteration s base) := by
  have frame := loopIteration_frame s base count i space hi index
  refine ⟨frame.program, frame.error, frame.registers, frame.sfp, ?_⟩
  intro a outside
  apply frame.memory a
  intro span member
  simp only [loopRoundWrites, List.mem_cons, List.mem_singleton] at member
  rcases member with rfl | rfl
  · exact outside _ (by simp [loopWrites])
  · have := outside ((r (.GPR 24#5) s).toNat, 8 * count) (by simp [loopWrites])
    simp only [Prod.fst, Prod.snd, loopAddress, index, space.address hi] at *
    omega

theorem loopIteration_lower (s : ArmState) (base : BitVec 64)
    (low : List (BitVec 64)) (word : BitVec 64)
    (space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 24#5) s) (low.length + 1))
    (index : r (.GPR 23#5) s = BitVec.ofNat 64 (8 * low.length))
    (words : LoopWords s (r (.GPR 24#5) s) (low ++ [word])) :
    LoopWords (loopIteration s base) (r (.GPR 24#5) s) low := by
  have frame := loopIteration_frame s base (low.length + 1) low.length space (by omega) index
  have old := ((LoopWords.append s _ low [word]).mp words).1
  intro i hi
  rw [frame.memory.read]
  · exact old i hi
  · rw [space.address (by omega : i < low.length + 1)]
    have := space.physical; omega
  · right
    intro span member
    simp only [loopRoundWrites, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp only [Prod.fst, Prod.snd]
      rw [space.address (by omega : i < low.length + 1)]
      have := space.apart; omega
    · simp only [Prod.fst, Prod.snd, loopAddress, index,
        space.address (by omega : i < low.length + 1),
        space.address (by omega : low.length < low.length + 1)]
      omega

theorem loopFrame_upper {s t : ArmState} {sp pointer : BitVec 64} {count : Nat}
    (space : LoopSpace sp pointer (count + 1))
    (frame : LoopFrame (loopWrites sp pointer count) s t) :
    read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * count)) t =
      read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * count)) s := by
  apply frame.memory.read
  · rw [space.address (by omega : count < count + 1)]
    have := space.physical; omega
  · right
    intro span member
    simp only [loopWrites, List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl
    · simp only [Prod.fst, Prod.snd]
      rw [space.address (by omega : count < count + 1)]
      have := space.apart; omega
    · simp only [Prod.fst, Prod.snd]
      rw [space.address (by omega : count < count + 1)]
      omega

/-- Reverse induction exposes the exact next high limb, without imposing a
fixed upper limit on the number of limbs. -/
theorem loop_reverse_induction {P : List (BitVec 64) → Prop}
    (nil : P []) (snoc : ∀ low word, P low → P (low ++ [word])) (words : List (BitVec 64)) :
    P words := by
  have h : ∀ rev : List (BitVec 64), P rev.reverse := by
    intro rev
    induction rev with
    | nil => simpa using nil
    | cons word rev ih => simpa only [List.reverse_cons] using snoc rev.reverse word ih
  simpa using h words.reverse

end SszArm.NatDivision
