import SszArm.EmitContract

namespace SszArm.Emit

open SszNative (NatOperand)
open SszNative.Serialize (Desc Value)
open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

theorem load_eq_of_mem_eq {s t : ArmState} (memory : t.mem = s.mem) :
    widthLoad t = widthLoad s := by
  funext address bytes
  unfold widthLoad
  rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) bytes (BitVec.ofNat 64 address)]

theorem descriptor_eq_of_mem_eq {s t : ArmState} (memory : t.mem = s.mem)
    (address : BitVec 64) (desc : Desc) : DescriptorAt t address desc ↔ DescriptorAt s address desc := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have loads := load_eq_of_mem_eq memory
  cases desc <;> simp only [DescriptorAt, reads, loads]

theorem value_eq_of_mem_eq {s t : ArmState} (memory : t.mem = s.mem)
    (address : BitVec 64) (value : Value) : ValueAt t address value ↔ ValueAt s address value := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have loads := load_eq_of_mem_eq memory
  cases value <;> simp only [ValueAt, reads, loads]

theorem backing_eq_of_mem_eq {s t : ArmState} (memory : t.mem = s.mem)
    (args : Args) (value : Value) : backingSpan t args value = backingSpan s args value := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  cases value <;> simp only [backingSpan, reads]

theorem Owned.of_mem_eq {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (memory : t.mem = s.mem) : Owned t args desc value size := by
  refine { owned with
    descriptor := (descriptor_eq_of_mem_eq memory _ _).2 owned.descriptor
    value_at := (value_eq_of_mem_eq memory _ _).2 owned.value_at
    backingOwned := ?_ }
  simpa only [backing_eq_of_mem_eq memory] using owned.backingOwned

theorem frame_read_offset {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address : BitVec 64) (total offset bytes : Nat)
    (bound : address.toNat + total ≤ 2^64) (owned : Protected writes address.toNat total)
    (within : offset + bytes ≤ total) :
    read_mem_bytes bytes (address + BitVec.ofNat 64 offset) t =
      read_mem_bytes bytes (address + BitVec.ofNat 64 offset) s := by
  by_cases empty : bytes = 0
  · subst bytes
    apply BitVec.eq_of_toNat_eq
    rfl
  · have offsetBound : offset < total := by omega
    have position : (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by bv_omega
    exact frame.read _ _ (by rw [position]; omega)
      (by rw [position]; exact owned.subspan offset bytes within)

theorem operand_header_preserved {writes : List Span} {s t : ArmState}
    (frame : MemoryFrame writes s t) (address : Nat) (operand : NatOperand)
    (bound : address + 16 ≤ 2^64) (header : Protected writes address 16)
    (limbs : NatDivision.OperandOwned writes operand)
    (input : SszNative.NatArithmetic.operandAt (widthLoad s) address operand) :
    SszNative.NatArithmetic.operandAt (widthLoad t) address operand := by
  obtain ⟨pointer, payload, representation⟩ := input
  refine ⟨?_, ?_, NatDivision.operand_at_preserved frame operand representation limbs⟩
  · rw [frame.load address 8 (by omega) (by simpa using header.subspan 0 8 (by decide))]
    exact pointer
  · rw [frame.load (address + 8) 8 (by omega) (header.subspan 8 8 (by decide))]
    exact payload

theorem bodyWrites_subset (args : Args) (size : Nat) (span : Span)
    (member : span ∈ bodyWrites args size) : span ∈ writesFor args size := by
  simp only [bodyWrites, writesFor, stackWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member ⊢
  rcases member with (rfl | rfl) | member
  · exact Or.inl (Or.inl (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inr member

theorem stackWrites_subset (args : Args) (size : Nat) (span : Span)
    (member : span ∈ stackWrites args) : span ∈ writesFor args size := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))

theorem Protected.weaken_emit {small large : List Span} {address bytes : Nat}
    (owned : Protected large address bytes) (subset : ∀ span ∈ small, span ∈ large) :
    Protected small address bytes := by
  rcases owned with empty | nonempty
  · exact Or.inl empty
  · exact Or.inr (fun span member => nonempty span (subset span member))

theorem output_tail {s t : ArmState} {args : Args} {desc : Desc} {value : Value} {size : Nat}
    (owned : Owned s args desc value size) (frame : MemoryFrame (writesFor args size) s t)
    (index : Nat) (low : size ≤ index) (high : index < args.capacity.toNat) :
    t.mem (args.output + BitVec.ofNat 64 index) = s.mem (args.output + BitVec.ofNat 64 index) := by
  have position : (args.output + BitVec.ofNat 64 index).toNat = args.output.toNat + index := by
    have bound := owned.outputBound
    bv_omega
  apply frame
  intro span member
  simp only [writesFor, List.mem_append] at member
  rcases member with member | member
  · rcases member with member | member
    · rcases owned.outputStack with empty | separate
      · omega
      · have apart := separate span member
        rw [position]
        omega
    · rcases owned.outputResult with empty | separate
      · omega
      · have apart := separate span member
        rw [position]
        omega
  · by_cases zero : size = 0
    · simp [zero] at member
    · simp only [zero, ↓reduceIte, List.mem_singleton] at member
      subst span
      rw [position]
      exact Or.inr (by omega)

end SszArm.Emit
