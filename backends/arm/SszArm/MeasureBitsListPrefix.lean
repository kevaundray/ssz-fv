import SszArm.MeasureBitsListGeometry
import SszArm.MeasureHelpersWritten

namespace SszArm.Measure.Bits.List

open SszNative (NatOperand)
open SszNative.Serialize (Packed)
open UintCodec (widthLoad)
open Delimited (Span MemoryFrame)

structure Core (s : ArmState) (args : Args) (schema : Schema) (bits : Packed) (actual : NatOperand) : Prop where
  result : r (.GPR 19#5) s = args.result
  arena : r (.GPR 20#5) s = args.arena
  stack : r (.GPR 31#5) s = args.bodySP
  low : r (.GPR 26#5) s = bits.count.setWidth 64
  high : r (.GPR 25#5) s = (bits.count >>> (64 : Nat)).setWidth 64
  cap : match schema.cap with
    | none => True
    | some operand => r (.GPR 22#5) s = operand.pointer ∧ r (.GPR 23#5) s = operand.payload
  pointer : r (.GPR 21#5) s = actual.pointer
  payload : r (.GPR 24#5) s = actual.payload

def prefixWrites (s : ArmState) (args : Args) (bits : Packed) : List Span :=
  [(args.stack.toNat - 288, 16)] ++ countWrites s args bits

structure Prefix (s t : ArmState) (args : Args) (schema : Schema) (bits : Packed) (actual : NatOperand) : Prop where
  counted : (countCall s args bits).result = .ok actual
  program : t.program = s.program
  error : read_err t = read_err s
  core : Core t args schema bits actual
  actualAt : actual.At (widthLoad t)
  cursor : (read_mem_bytes 8 (args.arena + 16#64) t).toNat = (countCall s args bits).used
  header : read_mem_bytes 8 args.arena t = read_mem_bytes 8 args.arena s ∧
    read_mem_bytes 8 (args.arena + 8#64) t = read_mem_bytes 8 (args.arena + 8#64) s
  written : NatDivision.WrittenAt (widthLoad t) (countCall s args bits)
  frame : MemoryFrame (prefixWrites s args bits) s t
  registers : ∀ reg : BitVec 5, reg ∈ [18#5, 27#5, 28#5, 29#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem CountPost.prefix {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed}
    {base : BitVec 64} {actual : NatOperand} (post : CountPost s t args schema bits base actual) :
    Prefix s t args schema bits actual := by
  refine ⟨post.counted, post.program, post.error,
    ⟨post.work.result, post.work.arena, post.work.stack, post.work.low, post.work.high,
      post.work.cap, post.pointer, post.payload⟩, post.actualAt, post.cursor, post.header,
    post.written, ?_, post.registers, post.vectors⟩
  apply post.frame.weaken
  intro span member
  exact List.mem_append.mpr (Or.inr member)

theorem Core.of_registers {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (core : Core s args schema bits actual)
    (unchanged : ∀ reg : BitVec 5, reg ∈ [19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 31#5] →
      r (.GPR reg) t = r (.GPR reg) s) : Core t args schema bits actual := by
  refine ⟨(unchanged 19#5 (by decide)).trans core.result,
    (unchanged 20#5 (by decide)).trans core.arena,
    (unchanged 31#5 (by decide)).trans core.stack,
    (unchanged 26#5 (by decide)).trans core.low,
    (unchanged 25#5 (by decide)).trans core.high, ?_,
    (unchanged 21#5 (by decide)).trans core.pointer,
    (unchanged 24#5 (by decide)).trans core.payload⟩
  cases cap : schema.cap with
  | none => trivial
  | some operand =>
    simpa only [cap, unchanged 22#5 (by decide), unchanged 23#5 (by decide)] using core.cap

theorem prefix_subset_full (schema : Schema) (s : ArmState) (args : Args) (bits : Packed)
    (span : Span) (member : span ∈ prefixWrites s args bits) :
    span ∈ writesFor args (outcome s args schema.descriptor (.bits bits)) := by
  simp only [prefixWrites, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | allocated
  · simp [writesFor, localWrites, stackWrites, bodyStackWrites]
  · exact List.mem_append.mpr (Or.inr (count_writes_subset schema s args bits span allocated))

theorem Prefix.full_frame {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (pre : Prefix s t args schema bits actual) :
    MemoryFrame (writesFor args (outcome s args schema.descriptor (.bits bits))) s t :=
  pre.frame.weaken (prefix_subset_full schema s args bits)

theorem Prefix.cap_at {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s t args schema bits actual)
    (cap : NatOperand) (present : schema.cap = some cap) : cap.At (widthLoad t) := by
  have member : cap ∈ Emit.descriptorOperands schema.descriptor ++ Emit.valueOperands (.bits bits) :=
    List.mem_append.mpr (Or.inl (cap_member schema cap present))
  exact NatDivision.operand_at_preserved pre.full_frame cap (owned.operand_at cap member)
    (owned.operandOwned cap member)

theorem Prefix.actual_lower_owned {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s t args schema bits actual) :
    NatDivision.OperandOwned (Helpers.loweringWrites t) actual := by
  apply Helpers.fromWide_result_owned (Helpers.loweringWrites t) (arenaOf s args) bits.count
    owned.storageBound _ actual pre.counted
  rcases owned.freeLocal with empty | separate
  · exact Or.inl empty
  · right
    intro span member
    exact separate span (List.mem_append.mpr (Or.inl
      (lowering_subset_local args _ t owned.stackLow pre.core.stack span member)))

theorem Prefix.cap_lower_owned {schema : Schema} {s t : ArmState} {args : Args} {bits : Packed} {actual : NatOperand}
    (owned : Owned s args schema.descriptor (.bits bits)) (pre : Prefix s t args schema bits actual)
    (cap : NatOperand) (present : schema.cap = some cap) :
    NatDivision.OperandOwned (Helpers.loweringWrites t) cap := by
  apply operand_owned_restrict cap (owned.operandOwned cap
    (List.mem_append.mpr (Or.inl (cap_member schema cap present))))
  intro span member
  exact List.mem_append.mpr (Or.inl (lowering_subset_local args _ t owned.stackLow pre.core.stack span member))

end SszArm.Measure.Bits.List
