import SszArm.MeasureBitsListGate

namespace SszArm.Measure.Bits.ListEntry

open Result

def loadOps : Kind → List Op
  | .bounded => [p1256, p1260, p1264]
  | .progressive => [p692, p696, p700, p704]

def Kind.smallEntry : Kind → Nat | .bounded => 1268 | .progressive => 708

def Kind.allocateEntry : Kind → Nat | .bounded => 1628 | .progressive => 1500

@[irreducible] def loaded (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  let count := w (.GPR 25#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s)
    (w (.GPR 26#5) (read_mem_bytes 8 (r (.GPR 21#5) s + 32#64) s) s)
  let fields := match kind with
    | .bounded =>
      w (.GPR 23#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
        (w (.GPR 22#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) count)
    | .progressive =>
      w (.GPR 22#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s)
        (w (.GPR 8#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
          (w (.GPR 23#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 24#64) s) count))
  w .PC (base + BitVec.ofNat 64 (if read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s = 0#64
    then kind.smallEntry else kind.allocateEntry)) fields

theorem load_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.checked) :
    run (loadOps kind).length s = loaded kind s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (loadOps kind) s := by
    cases kind <;>
      simp (config := {decide := true, instances := true})
        [Follows, loadOps, p1256, p1260, p1264, p692, p696, p700, p704,
          Kind.checked, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
          minimal_theory, error, pc, BitVec.add_assoc,
          BoolCodec.pair_read_low, BoolCodec.pair_read_high]
  rw [runs _ s base code follows]
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [loaded, effect, loadOps, p1256, p1260, p1264, p692, p696, p700, p704,
        Kind.checked, Kind.smallEntry, Kind.allocateEntry, Op.effect, exec_inst,
        state_simp_rules, bitvec_rules, minimal_theory, pc, BitVec.add_assoc,
        BoolCodec.pair_read_low, BoolCodec.pair_read_high, NatExact.gpr_w_pc,
        w_of_w_shadow]
  all_goals
    by_cases highZero : read_mem_bytes 8 (r (.GPR 21#5) s + 40#64) s = 0#64 <;>
      simp only [highZero, ↓reduceIte]

@[simp] theorem loaded_program (kind : Kind) (s : ArmState) (base : BitVec 64) :
    (loaded kind s base).program = s.program := by cases kind <;> simp [loaded, state_simp_rules]
@[simp] theorem loaded_error (kind : Kind) (s : ArmState) (base : BitVec 64) :
    read_err (loaded kind s base) = read_err s := by cases kind <;> simp [loaded, state_simp_rules]
@[simp] theorem loaded_vector (kind : Kind) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (loaded kind s base) = r (.SFP reg) s := by cases kind <;> simp [loaded, state_simp_rules]
@[simp] theorem loaded_memory (kind : Kind) (s : ArmState) (base : BitVec 64) :
    (loaded kind s base).mem = s.mem := by cases kind <;> simp [loaded, state_simp_rules]

theorem loaded_register (kind : Kind) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (unchanged : reg ∉ [8#5, 22#5, 23#5, 25#5, 26#5]) :
    r (.GPR reg) (loaded kind s base) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  cases kind <;> simp [loaded, state_simp_rules, unchanged.1, unchanged.2.1,
    unchanged.2.2.1, unchanged.2.2.2.1, unchanged.2.2.2.2]

def smallOps : Kind → List Op
  | .bounded => [p1268, p1272, p1276]
  | .progressive => [p708, p712]

@[irreducible] def small (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + (match kind with | .bounded => 1712#64 | .progressive => 716#64))
    (w (.GPR 24#5) (r (.GPR 26#5) s) (w (.GPR 21#5) 0#64 s))

theorem small_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.smallEntry) :
    run (smallOps kind).length s = small kind s base := by
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base (smallOps kind) s := by
    cases kind <;>
      simp (config := {decide := true, instances := true})
        [Follows, smallOps, p1268, p1272, p1276, p708, p712, Kind.smallEntry,
          Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
          error, pc, BitVec.add_assoc]
  rw [runs _ s base code follows]
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [small, effect, smallOps, p1268, p1272, p1276, p708, p712, Kind.smallEntry,
        Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        pc, BitVec.add_assoc, NatExact.gpr_w_pc, w_of_w_shadow]

end SszArm.Measure.Bits.ListEntry
