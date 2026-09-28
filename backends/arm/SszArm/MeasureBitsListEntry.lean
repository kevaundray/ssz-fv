import SszArm.MeasureBitsListWork
import SszArm.BitVectorPair

namespace SszArm.Measure.Bits.List

open SszNative.Serialize (Packed)

@[irreducible] def entered (schema : Schema) (s : ArmState) (base : BitVec 64) : ArmState :=
  ListEntry.loaded schema.kind (ListEntry.gated schema.kind s base) base

theorem entry_executes (schema : Schema) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 schema.kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 3#32) :
    run (2 + (ListEntry.loadOps schema.kind).length) s = entered schema s base := by
  have checked := ListEntry.gate_run schema.kind s base code error pc
  have loaded := ListEntry.load_run schema.kind (ListEntry.gated schema.kind s base) base
    (code.congr (ListEntry.gated_program _ _ _))
    ((ListEntry.gated_error _ _ _).trans error) (ListEntry.gated_pc_bits _ _ _ tag)
  rw [run_plus, checked, loaded]
  simp only [entered]

@[simp] theorem entered_program (schema : Schema) (s : ArmState) (base : BitVec 64) :
    (entered schema s base).program = s.program := by simp [entered]
@[simp] theorem entered_error (schema : Schema) (s : ArmState) (base : BitVec 64) :
    read_err (entered schema s base) = read_err s := by simp [entered]
@[simp] theorem entered_memory (schema : Schema) (s : ArmState) (base : BitVec 64) :
    (entered schema s base).mem = s.mem := by simp [entered]
@[simp] theorem entered_vector (schema : Schema) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (entered schema s base) = r (.SFP reg) s := by simp [entered]

theorem entered_register (schema : Schema) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 22#5, 23#5, 25#5, 26#5]) :
    r (.GPR reg) (entered schema s base) = r (.GPR reg) s := by
  unfold entered
  exact (ListEntry.loaded_register schema.kind (ListEntry.gated schema.kind s base) base reg untouched).trans
    (ListEntry.gated_register schema.kind s base reg)

theorem entered_owned (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits)) :
    Owned (entered schema s base) args schema.descriptor (.bits bits) := by
  apply owned.of_local_frame
  intro address outside
  exact congrFun (entered_memory schema s base) address

theorem entered_work (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (registers : BodyRegisters s args) (descriptor : r (.GPR 1#5) s = args.descriptor) :
    Work (entered schema s base) args schema bits := by
  have low := owned.value_at.2.2.2.2.1
  have high := owned.value_at.2.2.2.2.2
  cases schema with
  | bounded cap =>
    have pointer := BitVector.read_of_observe_offset s args.descriptor 8 8 cap.pointer owned.descriptor.2.1
    have payload := BitVector.read_of_observe_offset s args.descriptor 16 8 cap.payload
      (by simpa only [Nat.add_assoc] using owned.descriptor.2.2.1)
    constructor <;>
      simp [Schema.kind, Schema.cap, entered, ListEntry.loaded, ListEntry.gated,
        state_simp_rules, registers.result, registers.arena, registers.stack, registers.value,
        descriptor, low, high, pointer, payload]
  | progressive cap =>
    cases cap with
    | none =>
      have absent : read_mem_bytes 8 (args.descriptor + 8#64) s = 0#64 := owned.descriptor.2
      constructor <;>
        simp [Schema.kind, Schema.cap, entered, ListEntry.loaded, ListEntry.gated,
          state_simp_rules, registers.result, registers.arena, registers.stack, registers.value,
          descriptor, low, high, absent]
    | some cap =>
      have present := owned.descriptor.2.1
      have pointer := BitVector.read_of_observe_offset s args.descriptor 16 8 cap.pointer
        owned.descriptor.2.2.1
      have payload := BitVector.read_of_observe_offset s args.descriptor 24 8 cap.payload
        (by simpa only [Nat.add_assoc] using owned.descriptor.2.2.2.1)
      constructor <;>
        simp [Schema.kind, Schema.cap, entered, ListEntry.loaded, ListEntry.gated,
          state_simp_rules, registers.result, registers.arena, registers.stack, registers.value,
          descriptor, low, high, present, pointer, payload]

theorem entered_pc (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (base : BitVec 64) (owned : Owned s args schema.descriptor (.bits bits))
    (registers : BodyRegisters s args) :
    read_pc (entered schema s base) = base + BitVec.ofNat 64
      (if (bits.count >>> (64 : Nat)).setWidth 64 = 0#64
       then schema.kind.smallEntry else schema.kind.allocateEntry) := by
  have high := owned.value_at.2.2.2.2.2
  cases schema <;>
    simp [entered, ListEntry.loaded, ListEntry.gated, Schema.kind,
      state_simp_rules, registers.value, high]

end SszArm.Measure.Bits.List
