import SszArm.NatMulWordLargeFrame

namespace SszArm.NatMulWord.Large

open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame Returned)
open SszNative.NatArithmetic

def activeWrites (s : ArmState) (reservation : SszNative.Arena.Reservation)
    (words : List (BitVec 64)) : List Delimited.Span :=
  localWrites s (committed reservation words) ++ [(reservation.pointer, 8 * words.length)]

theorem active_to_full (s : ArmState) (reservation : SszNative.Arena.Reservation)
    (words : List (BitVec 64)) :
    ∀ span ∈ activeWrites s reservation words, span ∈ writesFor s (committed reservation words) := by
  intro span member
  simpa [activeWrites, writesFor, localWrites, committed, or_assoc, or_left_comm, or_comm] using
    (Or.inr member : span = ((r (.GPR 4#5) s).toNat + 16, 8) ∨ span ∈ activeWrites s reservation words)

theorem allocation_header_active (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s operand factor) (reservation : SszNative.Arena.Reservation)
    (model : outcome s operand factor = committed reservation (SszNative.NatMul.wordWritten operand factor)) :
    Protected (activeWrites s reservation (SszNative.NatMul.wordWritten operand factor))
      (r (.GPR 4#5) s).toNat 24 := by
  have localOwned := owned.arenaLocal
  have fresh := owned.fresh reservation (by rw [model]; rfl)
  rw [model] at localOwned fresh
  right
  intro span member
  simp only [activeWrites, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · rcases localOwned with empty | separate
    · omega
    · exact separate span member
  · rcases fresh with empty | separate
    · simp only [committed, SszNative.NatMul.wordWritten_length] at empty
      omega
    · have apart := separate ((r (.GPR 4#5) s).toNat, 24) (by simp)
      simp only [committed, Prod.fst, Prod.snd] at apart ⊢
      omega

theorem allocation_header_prefix (s : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s operand factor) (reservation : SszNative.Arena.Reservation)
    (model : outcome s operand factor = committed reservation (SszNative.NatMul.wordWritten operand factor)) :
    Protected (writesFor s (outcome s operand factor)) (r (.GPR 4#5) s).toNat 16 := by
  have active := allocation_header_active s operand factor owned reservation model
  right
  intro span member
  rw [model] at member
  simp only [writesFor, committed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | rfl | rfl
  · rcases active with empty | apart
    · omega
    · have sep := apart span (by simp [activeWrites, member])
      omega
  · simp only [Prod.fst, Prod.snd]
    exact Or.inl (Nat.le_refl _)
  · rcases active with empty | apart
    · omega
    · have sep := apart (reservation.pointer, 8 * (SszNative.NatMul.wordWritten operand factor).length)
        (by simp [activeWrites])
      omega

theorem allocation_post (s t : ArmState) (operand : SszNative.NatOperand) (factor : BitVec 64)
    (owned : Owned s operand factor) (reservation : SszNative.Arena.Reservation)
    (model : outcome s operand factor = committed reservation (SszNative.NatMul.wordWritten operand factor))
    (returned : Returned s t)
    (image : SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
      (.ok (SszNative.NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer)
        (SszNative.NatMul.wordWritten operand factor))))
    (written : NatCompare.Words t (BitVec.ofNat 64 reservation.pointer)
      (SszNative.NatMul.wordWritten operand factor))
    (cursor : (read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t).toNat = reservation.used)
    (frame : MemoryFrame (writesFor s (outcome s operand factor)) s t) :
    Post s t operand factor := by
  have protected := allocation_header_prefix s operand factor owned reservation model
  have physical := owned.arenaBound
  have capAddress : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
  have sameBase := frame.read (r (.GPR 4#5) s) 8 (by omega)
    (by simpa using protected.subspan 0 8 (by decide))
  have sameCapacity := frame.read (r (.GPR 4#5) s + 8#64) 8 (by rw [capAddress]; omega)
    (by rw [capAddress]; exact protected.subspan 8 8 (by decide))
  refine ⟨returned, ?_, ?_, ?_, frame,
    NatAdd.operand_preserved frame operand owned.operandAt owned.inputOwned,
    sameBase, sameCapacity⟩
  · simpa only [model, committed] using image
  · intro actual allocated
    have equal : reservation = actual := by simpa only [model, committed, Option.some.injEq] using allocated
    subst actual
    intro i
    have word := congrArg (fun value : BitVec 64 => some value.toNat) (written i)
    simpa only [model, committed, widthLoad, BitVec.ofNat_add] using word
  · simpa only [model, committed] using cursor

theorem loop_frame_active (s u t : ArmState) (reservation : SszNative.Arena.Reservation)
    (words : List (BitVec 64)) (bound : reservation.pointer < 2^64)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s)
    (frame : MemoryFrame (NatMul.loopWrites (r (.GPR 31#5) u)
      (BitVec.ofNat 64 reservation.pointer) words.length) u t) :
    MemoryFrame (activeWrites s reservation words) u t := by
  apply frame.weaken
  intro span member
  simp only [NatMul.loopWrites, sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [activeWrites, localWrites, committed]

theorem protected_subset {small large : List Delimited.Span} {address bytes : Nat}
    (owned : Protected large address bytes) (subset : ∀ span ∈ small, span ∈ large) :
    Protected small address bytes := by
  rcases owned with empty | separate
  · exact Or.inl empty
  · exact Or.inr (fun span member => separate span (subset span member))

theorem loop_writes_subset (s u : ArmState) (reservation : SszNative.Arena.Reservation)
    (words : List (BitVec 64)) (bound : reservation.pointer < 2^64)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s) :
    ∀ span ∈ NatMul.loopWrites (r (.GPR 31#5) u) (BitVec.ofNat 64 reservation.pointer) words.length,
      span ∈ writesFor s (committed reservation words) := by
  intro span member
  simp only [NatMul.loopWrites, sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [writesFor, localWrites, committed]

theorem allocation_normalize_owned (s u : ArmState) (operand : SszNative.NatOperand)
    (factor : BitVec 64) (owned : Owned s operand factor)
    (reservation : SszNative.Arena.Reservation) (abi : SmallABI s u)
    (space : AllocationSpace s reservation (operand.wordCount + 1)) :
    NormalizeOwned u (BitVec.ofNat 64 reservation.pointer)
      (SszNative.NatMul.wordWritten operand factor) := by
  have pointer : (BitVec.ofNat 64 reservation.pointer).toNat = reservation.pointer :=
    Nat.mod_eq_of_lt space.pointerBound
  refine ⟨abi.return_owned owned.return_owned, ?_, ?_, ?_, ?_⟩
  · simpa only [pointer] using space.positive
  · simpa only [pointer] using space.aligned
  · simpa only [pointer, SszNative.NatMul.wordWritten_length] using space.physical
  · rw [pointer, SszNative.NatMul.wordWritten_length]
    rcases space.separate with empty | separate
    · exact Or.inl empty
    · right
      have work := separate ((r (.GPR 31#5) s).toNat - 48, 48)
        (by simp [localWrites, committed])
      have result := separate ((r (.GPR 0#5) s).toNat, 16)
        (by simp [localWrites, committed])
      have status := separate ((r (.GPR 0#5) s).toNat + 64, 4)
        (by simp [localWrites, committed])
      intro span member
      simp only [valueWrites, NatAdd.valueWrites, abi.sp, abi.out,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;>
        have bound := owned.stackBound <;> omega

end SszArm.NatMulWord.Large
