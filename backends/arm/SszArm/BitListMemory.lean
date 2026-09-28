import SszArm.BitListContract
import SszArm.BitListBlocks

namespace SszArm.BitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open BitVector (Covers)

def called (s : ArmState) (base : BitVec 64) : Variant → ArmState
  | .list => listCalled s base
  | .progressive => progressiveCalled s base

def helperOption (s : ArmState) : Variant → BitVec 64
  | .list => r (.GPR 31#5) s + 144#64
  | .progressive => optionAddress s .progressive

def helperSP (s : ArmState) : Variant → BitVec 64
  | .list => r (.GPR 31#5) s
  | .progressive => r (.GPR 31#5) s + 368#64

@[simp] theorem called_out (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 0#5) (called s base kind) = r (.GPR 0#5) s := by
  cases kind <;> simp (config := {decide := true})
    [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_option (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 1#5) (called s base kind) = helperOption s kind := by
  cases kind <;> simp (config := {decide := true})
    [called, helperOption, optionAddress, listCalled, progressiveCalled, state_simp_rules]
@[simp] theorem called_source (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 2#5) (called s base kind) = r (.GPR 2#5) s := by
  cases kind <;> simp (config := {decide := true})
    [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_length (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 3#5) (called s base kind) = r (.GPR 3#5) s := by
  cases kind <;> simp (config := {decide := true})
    [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_arena (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 4#5) (called s base kind) = r (.GPR 19#5) s := by
  cases kind <;> simp (config := {decide := true})
    [called, listCalled, listMemory, progressiveCalled, state_simp_rules]
@[simp] theorem called_sp (s : ArmState) (base : BitVec 64) (kind : Variant) :
    r (.GPR 31#5) (called s base kind) = helperSP s kind := by
  cases kind <;> simp (config := {decide := true})
    [called, helperSP, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_program (s : ArmState) (base : BitVec 64) (kind : Variant) :
    (called s base kind).program = s.program := by
  cases kind <;> simp [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_error (s : ArmState) (base : BitVec 64) (kind : Variant) :
    read_err (called s base kind) = read_err s := by
  cases kind <;> simp [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]
@[simp] theorem called_pc (s : ArmState) (base : BitVec 64) (kind : Variant) :
    read_pc (called s base kind) = base + delimitedOffset := by
  cases kind <;> simp [called, listCalled, progressiveCalled, state_simp_rules]

theorem called_vectors (s : ArmState) (base : BitVec 64) (kind : Variant) (reg : BitVec 5) :
    r (.SFP reg) (called s base kind) = r (.SFP reg) s := by
  cases kind <;> simp [called, listCalled, listMemory, progressiveCalled, BoolCodec.returned, state_simp_rules]

theorem called_aligned (s : ArmState) (base : BitVec 64) (kind : Variant)
    (aligned : CheckSPAlignment s) : CheckSPAlignment (called s base kind) := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) (called s base kind)) 4
  rw [called_sp]
  cases kind with
  | list => exact stack
  | progressive =>
    change Aligned (r (.GPR 31#5) s + 368#64) 4
    simp only [Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at stack ⊢
    bv_omega

theorem local_covered (s : ArmState) (kind : Variant) (allocation : Option SszNative.Arena.Reservation) :
    Covers (writesFor s kind allocation) (localWrites s kind) := by
  intro span member
  refine ⟨span, ?_, Nat.le_refl _, Nat.le_refl _⟩
  cases allocation <;> simp_all [writesFor]

theorem copied_frame {s : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s .list limit data) :
    MemoryFrame [((r (.GPR 31#5) s).toNat + 144, 24)] s (listMemory s) := by
  intro address outside
  have separate := outside ((r (.GPR 31#5) s).toNat + 144, 24) (by simp)
  have bound := owned.stackHigh
  simp (disch := delimited_side) [listMemory]

theorem called_frame {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    MemoryFrame (localWrites s kind) s (called s base kind) := by
  cases kind with
  | list =>
    have frame := (copied_frame owned).weaken (large := localWrites s .list) (by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      simp [localWrites, stackWrites])
    intro address outside
    simpa only [called, listCalled, ArmState.mem_w_eq_mem] using frame address outside
  | progressive =>
    intro address outside
    simp [called, progressiveCalled, BoolCodec.returned, state_simp_rules]

theorem called_resources {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    Delimited.arenaOf (called s base kind) = arenaOf s := by
  have frame := called_frame owned base
  have capacity : (r (.GPR 19#5) s + 8#64).toNat = (r (.GPR 19#5) s).toNat + 8 := by
    have bound := owned.arenaBound
    bv_omega
  have cursor : (r (.GPR 19#5) s + 16#64).toNat = (r (.GPR 19#5) s).toNat + 16 := by
    have bound := owned.arenaBound
    bv_omega
  have hb := frame.read (r (.GPR 19#5) s) 8 (by have := owned.arenaBound; omega)
    (by simpa using owned.arenaLocal.subspan 0 8 (by decide))
  have hc := frame.read (r (.GPR 19#5) s + 8#64) 8
    (by rw [capacity]; have := owned.arenaBound; omega)
    (by rw [capacity]; exact owned.arenaLocal.subspan 8 8 (by decide))
  have hu := frame.read (r (.GPR 19#5) s + 16#64) 8
    (by rw [cursor]; have := owned.arenaBound; omega)
    (by rw [cursor]; exact owned.arenaLocal.subspan 16 8 (by decide))
  simp only [Delimited.arenaOf, called_arena, hb, hc, hu, arenaOf]

theorem helper_locals {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    Covers (localWrites s kind) (Delimited.localWrites (called s base kind)) := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have upper : (r (.GPR 31#5) s + 368#64).toNat = (r (.GPR 31#5) s).toNat + 368 := by bv_omega
  intro span member
  simp only [Delimited.localWrites, List.mem_cons, List.not_mem_nil, or_false, called_out] at member
  rcases member with rfl | rfl
  · exact ⟨((r (.GPR 0#5) s).toNat, 80), by simp [localWrites], by omega, by omega⟩
  · cases kind <;> by_cases empty : r (.GPR 3#5) s = 0#64
    all_goals
      simp only [Delimited.activationSpan, called_length, called_sp, helperSP, empty, ↓reduceIte, upper]
    · exact ⟨((r (.GPR 31#5) s).toNat - 112, 112), by simp [localWrites, stackWrites], by omega, by omega⟩
    · exact ⟨((r (.GPR 31#5) s).toNat - 112, 112), by simp [localWrites, stackWrites], by omega, by omega⟩
    · exact ⟨((r (.GPR 31#5) s).toNat + 256, 112), by simp [localWrites, stackWrites], by omega, by omega⟩
    · exact ⟨((r (.GPR 31#5) s).toNat + 256, 112), by simp [localWrites, stackWrites], by omega, by omega⟩

theorem helper_writes {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) (allocation : Option SszNative.Arena.Reservation) :
    Covers (writesFor s kind allocation) (Delimited.writesFor (called s base kind) allocation) := by
  have locals := (local_covered s kind allocation).trans (helper_locals owned base)
  cases allocation with
  | none => exact locals
  | some reservation =>
    intro span member
    simp only [Delimited.writesFor, Delimited.allocatedWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, called_arena] at member
    rcases member with member | rfl | rfl
    · exact locals span member
    · exact ⟨((r (.GPR 19#5) s).toNat + 16, 8), by simp [writesFor], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(reservation.pointer, 16), by simp [writesFor], Nat.le_refl _, Nat.le_refl _⟩

/-- Reads in the stack copy are the exact original words, not canonicalized caps. -/
theorem copied_words {s : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s .list limit data) (base : BitVec 64) :
    read_mem_bytes 4 (helperOption s .list) (called s base .list) = 1#32 ∧
    read_mem_bytes 8 (helperOption s .list + 8#64) (called s base .list) =
      read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
    read_mem_bytes 8 (helperOption s .list + 16#64) (called s base .list) =
      read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s := by
  have bound := owned.stackHigh
  have splitTag (u : ArmState) (address : BitVec 64) :
      write_mem_bytes 8 address 1#64 u =
        write_mem_bytes 4 (address + 4#64) 0#32 (write_mem_bytes 4 address 1#32 u) := by
    simp [write_mem_bytes, BitVec.add_assoc]
  simp (disch := delimited_side) [called, listCalled, helperOption, state_simp_rules,
    listMemory, UintCodec.Tail.write_pair_words, splitTag, BitVec.add_assoc]

end SszArm.BitList
