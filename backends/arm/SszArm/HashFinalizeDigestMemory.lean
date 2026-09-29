import SszArm.HashFinalizeShift
import SszArm.HashFinalizeControl

namespace SszArm.Hash.Finalize

open Delimited (Span Protected MemoryFrame)

theorem pair32_read (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 8 address s =
      read_mem_bytes 4 (address + 4#64) s ++ read_mem_bytes 4 address s := by
  simp only [read_mem_bytes, BitVec.cast_eq, BitVec.append_assoc, BitVec.add_assoc]
  rfl

theorem chaining_pair (s : ArmState) (address : BitVec 64) (words : Vector UInt32 8)
    (chaining : ChainingAt s address words) (pair : Fin 4) :
    read_mem_bytes 8 (address + BitVec.ofNat 64 (8 * pair.val)) s =
      words[2 * pair.val + 1].toBitVec ++ words[2 * pair.val].toBitVec := by
  rw [pair32_read]
  have first := chaining ⟨2 * pair.val, by have := pair.isLt; omega⟩
  have second := chaining ⟨2 * pair.val + 1, by have := pair.isLt; omega⟩
  have low : 8 * pair.val = 4 * (2 * pair.val) := by omega
  have high : address + BitVec.ofNat 64 (8 * pair.val) + 4#64 =
      address + BitVec.ofNat 64 (4 * (2 * pair.val + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [high, second, low, first]

def digestOctet (words : Vector UInt32 8) (i : Fin 32) : BitVec 8 :=
  (reverse32 words[i.val / 4].toBitVec).extractLsByte (i.val % 4)

def emitMemory (initial current : ArmState) (words : Vector UInt32 8)
    (indices : List (Fin 32)) : ArmState :=
  indices.foldl (fun t i =>
    write_mem_bytes 1 (outputPtr initial + BitVec.ofNat 64 i.val) (digestOctet words i) t) current

def DigestAt (s t : ArmState) (words : Vector UInt32 8) (written : List (Fin 32)) : Prop :=
  ∀ i : Fin 32, i ∈ written →
    t.mem (outputPtr s + BitVec.ofNat 64 i.val) = digestOctet words i

theorem emitMemory_frame (s t : ArmState) (words : Vector UInt32 8)
    (indices : List (Fin 32)) (physical : (outputPtr s).toNat + 32 ≤ 2^64) :
    MemoryFrame [((outputPtr s).toNat, 32)] t (emitMemory s t words indices) := by
  induction indices generalizing t with
  | nil => exact MemoryFrame.refl _ _
  | cons i indices ih =>
    have inside := i.isLt
    have position : (outputPtr s + BitVec.ofNat 64 i.val).toNat = (outputPtr s).toNat + i.val := by bv_omega
    have first : MemoryFrame [((outputPtr s).toNat, 32)] t
        (write_mem_bytes 1 (outputPtr s + BitVec.ofNat 64 i.val) (digestOctet words i) t) := by
      intro address outside
      have apart := outside ((outputPtr s).toNat, 32) (by simp)
      apply BoolCodec.write_mem_bytes_frame
      · rw [position]; omega
      · rw [position]; omega
    exact first.trans (ih _)

theorem DigestAt.emitMemory {s t : ArmState} {words : Vector UInt32 8}
    {written : List (Fin 32)} (stored : DigestAt s t words written)
    (indices : List (Fin 32)) (physical : (outputPtr s).toNat + 32 ≤ 2^64) :
    DigestAt s (emitMemory s t words indices) words (written ++ indices) := by
  induction indices generalizing t written with
  | nil => simpa only [emitMemory, List.foldl_nil, List.append_nil] using stored
  | cons i indices ih =>
    let u := write_mem_bytes 1 (outputPtr s + BitVec.ofNat 64 i.val) (digestOctet words i) t
    have inside := i.isLt
    have position : (outputPtr s + BitVec.ofNat 64 i.val).toNat = (outputPtr s).toNat + i.val := by bv_omega
    have one : DigestAt s u words (written ++ [i]) := by
      intro j member
      have jInside := j.isLt
      have jPosition : (outputPtr s + BitVec.ofNat 64 j.val).toNat = (outputPtr s).toNat + j.val := by bv_omega
      by_cases same : j = i
      · subst j
        dsimp [u]
        rw [Memory.write_mem_bytes_eq_mem_write_bytes,
          Memory.write_bytes_eq_extractLsByte (by omega) (by rw [position]; omega)
            (by rw [position]; omega)]
        simp [BitVec.extractLsByte]
      · have different : j.val ≠ i.val := fun h => same (Fin.ext h)
        have original : j ∈ written := by simpa [same] using member
        dsimp [u]
        rw [BoolCodec.write_mem_bytes_frame _ _ 1 _ _ (by rw [position]; omega)
          (by rw [position, jPosition]; omega)]
        exact stored j original
    have final := ih one
    simpa only [emitMemory, List.foldl_cons, List.append_assoc, List.singleton_append] using final

theorem Live.emitMemory {s t u : ArmState} {words : Vector UInt32 8}
    {changed : List (BitVec 5)} (live : Live s t) (g : Geometry s)
    (scalar : ScalarFrame changed t u)
    (kept : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 29 → reg ∉ changed)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) t)
    (indices : List (Fin 32)) (memory : u.mem = (emitMemory s t words indices).mem) :
    Live s u := by
  have frame : MemoryFrame [((outputPtr s).toNat, 32)] t u := by
    intro address outside
    rw [memory]
    exact emitMemory_frame s t words indices g.outputBound address outside
  apply live.advance g scalar kept sp frame
  · intro span member
    simp only [List.mem_singleton] at member
    subst span
    exact g.output_subspan (outputPtr s) 32 (Nat.le_refl _) (Nat.le_refl _)
  · apply g.saved_protected
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right; right
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem ChainingAt.emitMemory {s t u : ArmState} {words : Vector UInt32 8}
    (chaining : ChainingAt t (statePtr s + 64#64) words) (g : Geometry s)
    (indices : List (Fin 32)) (memory : u.mem = (emitMemory s t words indices).mem) :
    ChainingAt u (statePtr s + 64#64) words := by
  have frame : MemoryFrame [((outputPtr s).toNat, 32)] t u := by
    intro address outside
    rw [memory]
    exact emitMemory_frame s t words indices g.outputBound address outside
  have physical := g.stateBound
  have apart := g.outputState
  apply chaining.frame frame (by bv_omega)
  right
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  bv_omega

end SszArm.Hash.Finalize
