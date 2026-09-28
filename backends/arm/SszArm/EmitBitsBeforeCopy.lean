import SszArm.EmitBitsCopy

namespace SszArm.Emit.Bits

open SszNative.Serialize (Desc Packed)

def Path.prepareFuel (path : Path) : Nat :=
  (path.routeFuel + 7) + (2 + (1 + (2 + path.setupOps.length)))

theorem aligned_of_stack {s t : ArmState} (aligned : CheckSPAlignment s)
    (same : r (.GPR 31#5) t = r (.GPR 31#5) s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, same] using aligned

theorem ready_pc (path : Path) (s : ArmState) :
    read_pc (ready path s) = read_pc s + BitVec.ofNat 64 (4 * path.setupOps.length) := by
  cases path <;> simp [ready, block, Path.setupOps, Op.effect, Activation.put,
    Activation.next, state_simp_rules, BitVec.add_assoc]

theorem prepare_run (s : ArmState) (base : BitVec 64) (args : Args)
    (desc : Desc) (bits : Packed) (size : Nat)
    (kind : IsBits desc) (owned : Owned s args desc (.bits bits) size)
    (registers : BodyRegisters s args) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 568#64)
    (tag : r (.GPR 8#5) s = descriptorTag desc) :
    run (pathOf desc).prepareFuel s = prepared (pathOf desc) s ∧
    read_pc (prepared (pathOf desc) s) = base + BitVec.ofNat 64 (pathOf desc).copySite.offset := by
  let path := pathOf desc
  let q := quotientLoaded path s
  let a := guarded path.capacityGuard q
  let b := backingLoaded a
  let c := guarded path.backingGuard b
  have qRun := quotientLoaded_run s base args desc bits size kind owned registers code error aligned pc tag
  have qInput := quotientLoaded_owned path owned registers
  have qFull := quotientLoaded_value path owned registers
  have qSP : r (.GPR 31#5) q = r (.GPR 31#5) s :=
    quotientLoaded_register path s 31#5 (by cases path <;> decide)
  have qValue : r (.GPR 22#5) q = args.value :=
    (quotientLoaded_register path s 22#5 (by cases path <;> decide)).trans registers.value
  have qAligned := aligned_of_stack aligned qSP
  have qCode : CodeAt q base := by simpa only [q, CodeAt, quotientLoaded_program] using code
  have qError : read_err q = .None := (quotientLoaded_error path s).trans error
  have qPC : read_pc q = base + BitVec.ofNat 64 path.capacityGuard.start := by
    have advance (chosen : Path) :
        base + BitVec.ofNat 64 chosen.countStart + 4#64 + 24#64 =
          base + BitVec.ofNat 64 chosen.capacityGuard.start := by
      cases chosen <;> simp [Path.countStart, Path.capacityGuard, Guard.start, BitVec.add_assoc]
    have routedPC := routed_pc s base desc kind pc tag
    dsimp only [q, quotientLoaded]
    rw [shifted_pc, counted_pc, routedPC]
    exact advance (pathOf desc)
  have capacityGood := quotientLoaded_capacity path kind owned registers
  have aRun := guard_run path.capacityGuard q base qCode qError qAligned qPC
  have aPC : read_pc a = base + BitVec.ofNat 64 path.backingStart := by
    rw [guarded_pc path.capacityGuard q capacityGood, qPC]
    cases path <;> simp [Path.capacityGuard, Guard.start, Path.backingStart, BitVec.add_assoc]
  have aCode : CodeAt a base := by simpa only [a, CodeAt, guarded_program] using qCode
  have aError : read_err a = .None := (guarded_error path.capacityGuard q).trans qError
  have aAligned := aligned_of_stack qAligned (guarded_register path.capacityGuard q 31#5)
  have aInput : Owned a args desc (.bits bits) size := qInput.of_mem_eq (guarded_memory _ _)
  have aValue : r (.GPR 22#5) a = args.value := (guarded_register _ _ _).trans qValue
  have aFull : (r (.GPR 23#5) a).toNat = bits.count.toNat / 8 := by
    rw [guarded_register]
    exact qFull
  have bRun := backing_run path a base aCode aError aAligned aPC
  have bPC : read_pc b = base + BitVec.ofNat 64 path.backingGuard.start := by
    rw [backing_pc, aPC]
    cases path <;> simp [Path.backingStart, Path.backingGuard, Guard.start, BitVec.add_assoc]
  have bCode : CodeAt b base := by simpa only [b, CodeAt, backing_program] using aCode
  have bError : read_err b = .None := (backing_error a).trans aError
  have bAligned := aligned_of_stack aAligned (backing_register a 31#5 (by decide))
  have backingGood : path.backingGuard.good b := by
    have length : (r (.GPR 24#5) b).toNat = bits.bytes.size := by
      rw [backing_length, aValue]
      exact aInput.value_at.2.1
    have full : (r (.GPR 23#5) b).toNat = bits.count.toNat / 8 := by
      rw [backing_register _ 23#5 (by decide)]
      exact aFull
    cases path <;>
      simp only [Path.backingGuard, Guard.good, Guard.right, Guard.left]
    all_goals rw [length, full]; exact (backing_guards bits).1
  have cRun := guard_run path.backingGuard b base bCode bError bAligned bPC
  have cPC : read_pc c = base + BitVec.ofNat 64 path.setupStart := by
    rw [guarded_pc path.backingGuard b backingGood, bPC]
    cases path <;> simp [Path.backingGuard, Guard.start, Path.setupStart, BitVec.add_assoc]
  have cCode : CodeAt c base := by simpa only [c, CodeAt, guarded_program] using bCode
  have cError : read_err c = .None := (guarded_error path.backingGuard b).trans bError
  have cAligned := aligned_of_stack bAligned (guarded_register path.backingGuard b 31#5)
  have dRun := setup_run path c base cCode cError cAligned cPC
  constructor
  · change run ((path.routeFuel + 7) + (2 + (1 + (2 + path.setupOps.length)))) s = _
    rw [run_plus, qRun, run_plus, aRun, run_plus, bRun, run_plus, cRun]
    exact dRun
  · have advance (chosen : Path) :
        base + BitVec.ofNat 64 chosen.setupStart + BitVec.ofNat 64 (4 * chosen.setupOps.length) =
          base + BitVec.ofNat 64 chosen.copySite.offset := by
      cases chosen <;>
        simp [Path.setupStart, Path.setupOps, Path.copySite, CopySite.offset, BitVec.add_assoc]
    change read_pc (ready path c) = _
    rw [ready_pc, cPC]
    exact advance path

end SszArm.Emit.Bits
