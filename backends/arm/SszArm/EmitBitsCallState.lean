import SszArm.EmitBitsPrepare
import SszArm.EmitMemcpy

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open Delimited (MemoryFrame)

def checked (path : Path) (s : ArmState) : ArmState :=
  guarded path.backingGuard (backingLoaded (guarded path.capacityGuard (quotientLoaded path s)))

def prepared (path : Path) (s : ArmState) : ArmState := ready path (checked path s)

def Path.copySite : Path → CopySite
  | .list => .bitList | .vector => .bitVector

@[simp] theorem checked_program (path : Path) (s : ArmState) : (checked path s).program = s.program := by
  simp [checked]

@[simp] theorem checked_error (path : Path) (s : ArmState) : read_err (checked path s) = read_err s := by
  simp [checked]

@[simp] theorem checked_memory (path : Path) (s : ArmState) :
    (checked path s).mem = (quotientLoaded path s).mem := by simp [checked]

@[simp] theorem checked_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 23#5, 24#5, path.low]) :
    r (.GPR reg) (checked path s) = r (.GPR reg) s := by
  have h24 : reg ≠ 24#5 := by simp_all
  have rest : reg ∉ [8#5, 9#5, 23#5, path.low] := by simp_all
  simp [checked, h24, quotientLoaded_register path s reg rest]

@[simp] theorem checked_full (path : Path) (s : ArmState) :
    r (.GPR 23#5) (checked path s) = r (.GPR 23#5) (quotientLoaded path s) := by
  simp [checked]

@[simp] theorem prepared_program (path : Path) (s : ArmState) :
    (prepared path s).program = s.program := by simp [prepared]

@[simp] theorem prepared_error (path : Path) (s : ArmState) :
    read_err (prepared path s) = read_err s := by simp [prepared]

@[simp] theorem prepared_memory (path : Path) (s : ArmState) :
    (prepared path s).mem = (quotientLoaded path s).mem := by simp [prepared]

@[simp] theorem ready_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [0#5, 1#5, 2#5, 22#5, 25#5]) :
    r (.GPR reg) (ready path s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h2 : reg ≠ 2#5 := by simp_all
  have h22 : reg ≠ 22#5 := by simp_all
  have h25 : reg ≠ 25#5 := by simp_all
  cases path <;> simp [ready, block, Path.setupOps, Op.effect, Activation.put,
    Activation.next, state_simp_rules, h0, h1, h2, h22, h25]

@[simp] theorem prepared_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [0#5, 1#5, 2#5, 8#5, 9#5, 22#5, 23#5, 24#5, 25#5, 26#5]) :
    r (.GPR reg) (prepared path s) = r (.GPR reg) s := by
  have readyUntouched : reg ∉ [0#5, 1#5, 2#5, 22#5, 25#5] := by simp_all
  have checkUntouched : reg ∉ [8#5, 9#5, 23#5, 24#5, path.low] := by
    cases path <;> simp_all [Path.low]
  rw [prepared, ready_register path _ reg readyUntouched,
    checked_register path s reg checkUntouched]

theorem prepared_owned (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    Owned (prepared path s) args desc (.bits bits) size :=
  (quotientLoaded_owned path owned registers).of_mem_eq (prepared_memory path s)

theorem quotientLoaded_frame (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    MemoryFrame (bodyWrites args size) s (quotientLoaded path s) := by
  have stack : r (.GPR 31#5) (counted path (routed path s)) = args.bodySP :=
    (counted_register path _ 31#5 (by cases path <;> decide) (by decide)).trans
      ((routed_register _ _ _ (by decide)).trans registers.stack)
  have frame := shifted_frame path (counted path (routed path s)) args size stack owned.stackLow
  intro address outside
  exact (frame address outside).trans (congrFun ((counted_memory _ _).trans (routed_memory _ _)) address)

theorem prepared_frame (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    MemoryFrame (bodyWrites args size) s (prepared path s) := by
  intro address outside
  rw [prepared_memory]
  exact quotientLoaded_frame path owned registers address outside

theorem prepared_arguments (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    r (.GPR 0#5) (prepared path s) = args.output ∧
    r (.GPR 1#5) (prepared path s) = read_mem_bytes 8 (args.value + 16#64) (prepared path s) ∧
    (r (.GPR 2#5) (prepared path s)).toNat = bits.count.toNat / 8 := by
  unfold prepared
  obtain ⟨r0, r1, r2⟩ := ready_arguments path (checked path s)
  have value := (checked_register path s 22#5 (by cases path <;> decide)).trans registers.value
  refine ⟨r0.trans ((checked_register path s 20#5 (by cases path <;> decide)).trans registers.output), ?_, ?_⟩
  · rw [r1, value]
    exact (Memory.mem_eq_iff_read_mem_bytes_eq.mp (ready_memory path (checked path s)) 8 _).symm
  · rw [r2, checked_full]
    exact quotientLoaded_value path owned registers

end SszArm.Emit.Bits
