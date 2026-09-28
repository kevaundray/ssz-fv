import SszArm.MeasureBitsAllocExec
import SszArm.DelimitedArenaArithmetic

namespace SszArm.Measure.Bits.Alloc

inductive CheckKind where
  | address | round | align | finish | capacity
  deriving DecidableEq

def CheckKind.ops : CheckKind → List Op
  | .address => [.loadBase, .loadUsed, .addAddress, .addressGuard]
  | .round => [.compareAlignment, .alignmentGuard]
  | .align => [.addPadding, .maskPadding, .subtractAddress, .addUsed, .usedGuard]
  | .finish => [.compareSize, .sizeGuard]
  | .capacity => [.loadCapacity, .addSize, .compareCapacity, .capacityGuard]

def CheckKind.offset : CheckKind → Nat
  | .address => 0 | .round => 16 | .align => 24 | .finish => 44 | .capacity => 52

def CheckKind.clobbers (site : Site) : CheckKind → List (BitVec 5)
  | .address => [site.baseReg, site.usedReg, site.workReg]
  | .round | .finish => []
  | .align => [site.tempReg, site.workReg, site.usedReg]
  | .capacity => [site.tempReg, site.workReg]

structure GuardFrame (site : Site) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5,
    reg ∉ [site.baseReg, site.usedReg, site.workReg, site.tempReg] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : t.mem = s.mem

theorem GuardFrame.refl (site : Site) (s : ArmState) : GuardFrame site s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem GuardFrame.trans {site : Site} {s t u : ArmState}
    (st : GuardFrame site s t) (tu : GuardFrame site t u) : GuardFrame site s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg keep => (tu.registers reg keep).trans (st.registers reg keep),
    fun reg => (tu.vectors reg).trans (st.vectors reg), tu.memory.trans st.memory⟩

theorem GuardFrame.sp {site : Site} {s t : ArmState} (frame : GuardFrame site s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s :=
  frame.registers _ (by cases site <;> decide)

theorem GuardFrame.aligned {site : Site} {s t : ArmState}
    (frame : GuardFrame site s t) (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

theorem guard_registers (site : Site) (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) (reg : BitVec 5) (keep : reg ∉ kind.clobbers site) :
    r (.GPR reg) (block site base kind.ops s) = r (.GPR reg) s := by
  cases site <;> cases kind <;>
    simp only [CheckKind.clobbers, Site.baseReg, Site.usedReg, Site.workReg, Site.tempReg,
      List.mem_cons, List.not_mem_nil, or_false, not_or] at keep <;>
    simp (disch := simp_all) [CheckKind.ops, block, effect, put, next,
      Site.baseReg, Site.usedReg, Site.workReg, Site.tempReg,
      Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_frame (site : Site) (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) : GuardFrame site s (block site base kind.ops s) := by
  constructor
  · cases kind <;> simp [CheckKind.ops, block]
  · cases kind <;> simp [CheckKind.ops, block]
  · intro reg keep
    apply guard_registers site kind s base reg
    cases kind <;> simp_all [CheckKind.clobbers]
  · intro reg
    cases site <;> cases kind <;>
      simp [CheckKind.ops, block, effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]
  · cases site <;> cases kind <;>
      simp [CheckKind.ops, block, effect, put, next,
        Udivti3.compare, Udivti3.next, state_simp_rules]

theorem guard_run (site : Site) (kind : CheckKind) (s : ArmState)
    (base : BitVec 64) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.entry + kind.offset)) :
    run kind.ops.length s = block site base kind.ops s := by
  apply block_run site base kind.ops s code error aligned
  have pc' : r .PC s = base + BitVec.ofNat 64 (site.entry + kind.offset) := pc
  cases site <;> cases kind <;>
    simp (config := {decide := true, instances := true})
      [CheckKind.ops, CheckKind.offset, Site.entry, Follows, row, Op.index, effect,
        put, next, Udivti3.compare, Udivti3.next, state_simp_rules, pc', BitVec.add_assoc]

structure Checkpoint (site : Site) (s t : ArmState) : Prop where
  runs : ∃ fuel, run fuel s = t
  frame : GuardFrame site s t

theorem Checkpoint.refl (site : Site) (s : ArmState) : Checkpoint site s s :=
  ⟨⟨0, rfl⟩, GuardFrame.refl site s⟩

theorem Checkpoint.step {site : Site} {s t : ArmState} (reached : Checkpoint site s t)
    (kind : CheckKind) (base : BitVec 64) (code : CodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc t = base + BitVec.ofNat 64 (site.entry + kind.offset)) :
    Checkpoint site s (block site base kind.ops t) := by
  obtain ⟨fuel, runs⟩ := reached.runs
  have nextRun := guard_run site kind t base (code.congr reached.frame.program)
    (reached.frame.error.trans error) (reached.frame.aligned aligned) pc
  refine ⟨⟨fuel + kind.ops.length, ?_⟩, reached.frame.trans (guard_frame site kind t base)⟩
  rw [run_plus, runs, nextRun]

theorem Checkpoint.header {site : Site} {s t : ArmState} (reached : Checkpoint site s t)
    (offset : BitVec 64) :
    read_mem_bytes 8 (r (.GPR 20#5) t + offset) t =
      read_mem_bytes 8 (r (.GPR 20#5) s + offset) s := by
  rw [reached.frame.registers 20#5 (by cases site <;> decide)]
  exact Memory.mem_eq_iff_read_mem_bytes_eq.mp reached.frame.memory _ _

end SszArm.Measure.Bits.Alloc
