import SszArm.EmitBitsLoads

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)
open BitVector.ValueTail (countLow countHigh quotientWord)

def pathOf : Desc → Path
  | .bitVector _ => .vector | _ => .list

def Path.capacityGuard : Path → Guard
  | .list => .listCapacity | .vector => .vectorCapacity

def Path.backingGuard : Path → Guard
  | .list => .listBacking | .vector => .vectorBacking

def routed (path : Path) (s : ArmState) : ArmState :=
  match path with
  | .list => dispatched s
  | .vector => guarded .vectorTag (dispatched s)

def Path.routeFuel : Path → Nat
  | .list => 3 | .vector => 5

@[simp] theorem routed_program (path : Path) (s : ArmState) : (routed path s).program = s.program := by
  cases path <;> simp [routed]

@[simp] theorem routed_error (path : Path) (s : ArmState) : read_err (routed path s) = read_err s := by
  cases path <;> simp [routed]

@[simp] theorem routed_memory (path : Path) (s : ArmState) : (routed path s).mem = s.mem := by
  cases path <;> simp [routed]

@[simp] theorem routed_register (path : Path) (s : ArmState) (reg : BitVec 5) (other : reg ≠ 9#5) :
    r (.GPR reg) (routed path s) = r (.GPR reg) s := by
  cases path <;> simp [routed, other]

@[simp] theorem routed_vector (path : Path) (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (routed path s) = r (.SFP reg) s := by
  cases path <;> simp [routed]

theorem routed_pc (s : ArmState) (base : BitVec 64) (desc : Desc)
    (kind : IsBits desc) (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc) :
    read_pc (routed (pathOf desc) s) = base + BitVec.ofNat 64 (pathOf desc).countStart := by
  have initial := dispatched_pc s base desc kind pc tag
  cases desc with
  | bitVector length =>
    have good : Guard.good .vectorTag (dispatched s) := by
      simp only [Guard.good, dispatched_register s 8#5 (by decide), tag, descriptorTag]
      rfl
    rw [pathOf, routed, guarded_pc .vectorTag _ good, initial]
    simp [countEntry, Path.countStart, BitVec.add_assoc]
  | bitList limit => exact initial
  | progressiveBitList limit => exact initial
  | _ => cases kind

theorem route_run (s : ArmState) (base : BitVec 64) (desc : Desc)
    (kind : IsBits desc) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc) :
    run (pathOf desc).routeFuel s = routed (pathOf desc) s := by
  have first := dispatch_run s base code error aligned pc
  cases desc with
  | bitVector length =>
    have nextPC := dispatched_pc s base (.bitVector length) trivial pc tag
    have nextCode : CodeAt (dispatched s) base := by simpa only [CodeAt, dispatched_program] using code
    have nextAligned : CheckSPAlignment (dispatched s) := by
      simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
        dispatched_register s 31#5 (by decide)] using aligned
    change run (3 + 2) s = _
    rw [run_plus, first]
    exact guard_run .vectorTag _ base nextCode ((dispatched_error s).trans error) nextAligned nextPC
  | bitList limit => exact first
  | progressiveBitList limit => exact first
  | _ => cases kind

def quotientLoaded (path : Path) (s : ArmState) : ArmState := shifted path (counted path (routed path s))

@[simp] theorem quotientLoaded_program (path : Path) (s : ArmState) :
    (quotientLoaded path s).program = s.program := by simp [quotientLoaded]

@[simp] theorem quotientLoaded_error (path : Path) (s : ArmState) :
    read_err (quotientLoaded path s) = read_err s := by simp [quotientLoaded]

@[simp] theorem quotientLoaded_register (path : Path) (s : ArmState) (reg : BitVec 5)
    (untouched : reg ∉ [8#5, 9#5, 23#5, path.low]) :
    r (.GPR reg) (quotientLoaded path s) = r (.GPR reg) s := by
  have h8 : reg ≠ 8#5 := by simp_all
  have h9 : reg ≠ 9#5 := by simp_all
  have h23 : reg ≠ 23#5 := by simp_all
  have hlo : reg ≠ path.low := by simp_all
  simp [quotientLoaded, h8, h9, h23, hlo]

theorem quotientLoaded_value (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    (r (.GPR 23#5) (quotientLoaded path s)).toNat = bits.count.toNat / 8 := by
  have value : r (.GPR 22#5) (routed path s) = args.value :=
    (routed_register _ _ _ (by decide)).trans registers.value
  have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (routed_memory path s)
  have low := owned.value_at.2.2.2.2.1
  have high := owned.value_at.2.2.2.2.2
  have quotient := (count_quotient bits owned.physical).1
  simpa only [quotientLoaded, shifted_quotient, counted_low, counted_high,
    value, loads, low, high, quotientWord, BitVector.ValueTail.shift3_eq,
    countLow, countHigh] using quotient

theorem quotientLoaded_owned (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) :
    Owned (quotientLoaded path s) args desc (.bits bits) size := by
  have countedOwned : Owned (counted path (routed path s)) args desc (.bits bits) size :=
    owned.of_mem_eq ((counted_memory _ _).trans (routed_memory _ _))
  apply shifted_owned path countedOwned
  exact (counted_register path _ 31#5 (by cases path <;> decide) (by decide)).trans
    ((routed_register _ _ _ (by decide)).trans registers.stack)

theorem quotientLoaded_run (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat)
    (kind : IsBits desc) (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc) :
    run ((pathOf desc).routeFuel + (1 + 6)) s = quotientLoaded (pathOf desc) s := by
  let path := pathOf desc
  let a := routed path s
  let b := counted path a
  have runA := route_run s base desc kind code error aligned pc tag
  have pcA := routed_pc s base desc kind pc tag
  have codeA : CodeAt a base := by simpa only [a, CodeAt, routed_program] using code
  have errorA : read_err a = .None := (routed_error path s).trans error
  have spA : r (.GPR 31#5) a = r (.GPR 31#5) s := routed_register _ _ _ (by decide)
  have alignedA : CheckSPAlignment a := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, spA] using aligned
  have runB := count_run path a base codeA errorA alignedA pcA
  have pcB : read_pc b = base + BitVec.ofNat 64 path.shiftStart := by
    have advance (chosen : Path) :
        BitVec.ofNat 64 chosen.countStart + 4#64 = BitVec.ofNat 64 chosen.shiftStart := by
      cases chosen <;> decide
    rw [counted_pc, pcA, BitVec.add_assoc, advance]
  have codeB : CodeAt b base := by simpa only [b, CodeAt, counted_program] using codeA
  have errorB : read_err b = .None := (counted_error path a).trans errorA
  have spB : r (.GPR 31#5) b = args.bodySP :=
    (counted_register path a 31#5 (by cases path <;> decide) (by decide)).trans
      (spA.trans registers.stack)
  have alignedB : CheckSPAlignment b := by
    have same : r (.GPR 31#5) b = r (.GPR 31#5) s := spB.trans registers.stack.symm
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, same] using aligned
  have stackLow : 16 ≤ (r (.GPR 31#5) b).toNat := by
    have low := owned.stackLow
    rw [spB, Args.bodySP]
    bv_omega
  rw [run_plus, runA, run_plus, runB]
  exact shift_run path b base codeB errorB alignedB pcB stackLow

theorem quotientLoaded_capacity (path : Path) {s : ArmState} {args : Args} {desc : Desc}
    {bits : Packed} {size : Nat} (kind : IsBits desc)
    (owned : Owned s args desc (.bits bits) size) (registers : BodyRegisters s args) :
    path.capacityGuard.good (quotientLoaded path s) := by
  have quotient := quotientLoaded_value path owned registers
  have capacity := quotientLoaded_register path s 21#5 (by cases path <;> decide)
  have full := full_le_size kind owned.expected
  have fitting := owned.fitting
  cases path <;>
    simp only [Path.capacityGuard, Guard.good, Guard.right, Guard.left]
  all_goals rw [quotient, capacity, registers.capacity]; omega

end SszArm.Emit.Bits
