import SszArm.IndicesPrefixEqualWidthArithmetic
import SszArm.NatCompareBlocks

namespace SszArm.Indices.PrefixEqual.Width

open Udivti3 (next put flagged)
open Delimited (MemoryFrame Protected)

def changed (side : Side) : List (BitVec 5) :=
  [lower side, upper side, limb side, count side, high side]

/-- Width evaluation restores its lowering SP and both scratch registers;
only its five architectural results/work registers may differ. -/
structure Frame (side : Side) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ changed side → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
      t.mem a = s.mem a

theorem Frame.refl (side : Side) (s : ArmState) : Frame side s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {side : Side} {s t : ArmState} (frame : Frame side s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s :=
  frame.registers _ (by cases side <;> decide)

theorem Frame.trans {side : Side} {s t u : ArmState}
    (first : Frame side s t) (second : Frame side t u) : Frame side s u :=
  ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
    fun reg => (second.vectors reg).trans (first.vectors reg),
    fun a outside => (second.memory a (by simpa only [first.sp] using outside)).trans
      (first.memory a outside)⟩

theorem Frame.aligned {side : Side} {s t : ArmState} (frame : Frame side s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

theorem Frame.code {side : Side} {s t : ArmState} (frame : Frame side s t)
    {base : BitVec 64} (code : Linked.PrefixEqual.CodeAt s base) : Linked.PrefixEqual.CodeAt t base :=
  Codec.Linked.WordsAt.preserve code frame.program

theorem Frame.memoryFrame {side : Side} {s t : ArmState} (frame : Frame side s t)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t := by
  intro a outside
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  apply frame.memory a
  dsimp at apart
  omega

theorem Frame.source {side : Side} {s t : ArmState} (frame : Frame side s t)
    (p : BitVec 64) (words : List (BitVec 64)) (source : NatCompare.Source s p words) :
    NatCompare.Source t p words := by
  simpa only [NatCompare.Source, ByteView.Source, frame.sp] using source

theorem Frame.words {side : Side} {s t : ArmState} (frame : Frame side s t)
    (p : BitVec 64) (words : List (BitVec 64)) (source : NatCompare.Source s p words)
    (stored : NatCompare.Words s p words) : NatCompare.Words t p words := by
  intro i
  rw [← stored i]
  have physical := source.2.1
  have inside := i.isLt
  have position : (p + BitVec.ofNat 64 (8 * i.val)).toNat = p.toNat + 8 * i.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply (frame.memoryFrame source.1).read
  · rw [position]; omega
  · right
    intro span member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst span
    rw [position]
    rcases source.2.2 with empty | before | after
    · subst words; exact Fin.elim0 i
    · left; dsimp; omega
    · right; dsimp; omega

/-- Whole operations that have not yet restored their lowering saves. -/
def loweringOps : List Op := [.p16, .p20, .p24, .p28, .p32, .p40, .p44,
  .p108, .p112, .p116, .p120, .p124, .p148, .p152, .p156]

theorem pure_op_frame (side : Side) (base : BitVec 64) (op : Op) (s : ArmState)
    (pure : op ∉ loweringOps) : Frame side s (op.effect side base s) := by
  constructor
  · exact op.program side base s
  · exact op.error side base s
  · intro reg outside
    cases side <;> cases op <;>
      simp_all [loweringOps, changed, lower, upper, limb, count, high, Op.effect,
        Clz.Side.input, Clz.Side.counter, put, next, flagged, state_simp_rules]
  · intro reg
    cases op <;> simp [Op.effect, put, next, flagged, state_simp_rules]
  · intro a outside
    cases op <;> simp_all [loweringOps, Op.effect, put, next, flagged, state_simp_rules]

theorem pure_frame (side : Side) (base : BitVec 64) (ops : List Op) (s : ArmState)
    (pure : ∀ op ∈ ops, op ∉ loweringOps) : Frame side s (block side base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl side s
  | cons op rest ih =>
      exact (pure_op_frame side base op s (pure op List.mem_cons_self)).trans
        (ih _ (fun op member => pure op (List.mem_cons_of_mem _ member)))

/-- Address facts for the lowering pair, proved with bounded Nat arithmetic. -/
theorem stack_positions (s : ArmState) (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    (r (.GPR 31#5) s - 16#64).toNat = (r (.GPR 31#5) s).toNat - 16 ∧
    (r (.GPR 31#5) s - 8#64).toNat = (r (.GPR 31#5) s).toNat - 8 := by
  have bound := (r (.GPR 31#5) s).isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor <;> omega

def savedPair (s : ArmState) (first second : BitVec 5) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (r (.GPR second) s)
    (NatCompare.saved s first)

theorem savedPair_low (s : ArmState) (first second : BitVec 5)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (savedPair s first second) = r (.GPR first) s := by
  obtain ⟨low, high⟩ := stack_positions s safe
  have bound := (r (.GPR 31#5) s).isLt
  unfold savedPair NatCompare.saved
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
    (by rw [low]; omega) (by rw [high]; omega) (by rw [low, high]; omega),
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by rw [low]; omega)]

theorem savedPair_high (s : ArmState) (first second : BitVec 5)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (savedPair s first second) = r (.GPR second) s := by
  obtain ⟨_, high⟩ := stack_positions s safe
  have bound := (r (.GPR 31#5) s).isLt
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by rw [high]; omega)

theorem savedPair_frame (side : Side) (s : ArmState) (first second : BitVec 5)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) : Frame side s (savedPair s first second) := by
  obtain ⟨low, high⟩ := stack_positions s safe
  have bound := (r (.GPR 31#5) s).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [savedPair, NatCompare.saved, state_simp_rules]
  · simp [savedPair, NatCompare.saved, state_simp_rules]
  · intro reg outside; simp [savedPair, NatCompare.saved, state_simp_rules]
  · intro reg; simp [savedPair, NatCompare.saved, state_simp_rules]
  · intro a outside
    unfold savedPair NatCompare.saved
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ a (by rw [high]; omega)
      (by rw [high]; omega),
      BoolCodec.write_mem_bytes_frame _ _ 8 _ a (by rw [low]; omega) (by rw [low]; omega)]

end SszArm.Indices.PrefixEqual.Width
