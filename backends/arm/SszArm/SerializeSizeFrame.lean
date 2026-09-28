import SszArm.SerializeExec
import SszArm.NatToU128Memory
import SszArm.NatAddLoadState

namespace SszArm.Serialize.Size

/-- Only the saved X9 word is written; the upper half of the lowering slot is untouched. -/
def writes (s : ArmState) : List Delimited.Span :=
  [((r (.GPR 31#5) s).toNat - 16, 8)]

structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [5#5, 9#5, 10#5, 11#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : Delimited.MemoryFrame (writes s) s t

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem Frame.sp {s t : ArmState} (h : Frame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem Frame.trans {s t u : ArmState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a outside
  exact (k.memory a (by simpa only [writes, h.sp] using outside)).trans (h.memory a outside)

theorem Frame.aligned {s t : ArmState} (h : Frame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using aligned

theorem Frame.code {s t : ArmState} (h : Frame s t) {base : BitVec 64}
    (code : Serialize.CodeAt s base) : Serialize.CodeAt t base := code.congr h.program

theorem Frame.source {s t : ArmState} (h : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (source : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using source

theorem Frame.memory16 {s t : ArmState} (h : Frame s t) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t := by
  intro a outside
  apply h.memory
  intro span member
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  rcases apart with low | high
  · exact Or.inl low
  · right
    change (r (.GPR 31#5) s).toNat - 16 + 8 ≤ a.toNat
    change (r (.GPR 31#5) s).toNat - 16 + 16 ≤ a.toNat at high
    omega

theorem Frame.words {s t : ArmState} (h : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (source : NatCompare.Source s pointer words) (stored : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := by
  intro i
  rw [← stored i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  change t.mem _ = s.mem _
  apply h.memory16
  intro span member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst span
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at source
  rcases source with ⟨stack, bound, empty | separate⟩
  · subst words; exact Fin.elim0 i
  · have hi := i.isLt
    have address : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
        pointer.toNat + 8 * i.val + j := by bv_omega
    rw [address]
    omega

def readonlyOps : List Serialize.Op :=
  [.p152, .p156, .p160, .p164, .p200, .p204, .p208, .p212, .p216, .p220,
   .p416, .p420, .p424, .p428]

theorem readonly_frame (base : BitVec 64) (ops : List Serialize.Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ readonlyOps) : Frame s (Serialize.block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih =>
    have member := allowed op List.mem_cons_self
    have one : Frame s (op.effect base s) := by
      cases op <;> simp_all only [readonlyOps, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · exact Serialize.Op.program _ _ _
        · exact Serialize.Op.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Serialize.Op.effect, Serialize.put, Serialize.next,
            Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
        · intro reg; exact Serialize.Op.vector _ _ _ _
        · intro a outside
          simp [Serialize.Op.effect, Serialize.put, Serialize.next,
            Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
    exact one.trans (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop)))

theorem readonly_memory (base : BitVec 64) (ops : List Serialize.Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ readonlyOps) :
    (Serialize.block base ops s).mem = s.mem := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have member := allowed op List.mem_cons_self
    have one : (op.effect base s).mem = s.mem := by
      cases op <;> simp_all [readonlyOps, Serialize.Op.effect, Serialize.put, Serialize.next,
        Emit.Dispatch.compare64, Emit.Dispatch.next, state_simp_rules]
    exact (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop))).trans one

def loadOps : List Serialize.Op := [.p168, .p172, .p176, .p180, .p184, .p188, .p192, .p196]

def loadResult (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + 200#64) (w (.GPR 11#5) limb (NatCompare.saved s 9#5))

theorem load_run (s : ArmState) (base limb : BitVec 64)
    (code : Serialize.CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 168#64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 8#5) s + (r (.GPR 10#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) : run 8 s = loadResult s base limb := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5) =
      r (.GPR 9#5) s := BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have follows : Serialize.Follows base loadOps s := by
    change r .PC s = base + 168#64 at pc
    simp [loadOps, Serialize.Follows, Serialize.Op.row, Serialize.Op.effect,
      Serialize.put, Serialize.next, state_simp_rules, pc, BitVec.add_assoc]
  rw [show 8 = loadOps.length by rfl, Serialize.block_run base loadOps s code error aligned follows]
  have sequence : Serialize.block base loadOps s = NatAdd.indexedReadSequence s 8#5 10#5 9#5 11#5 := by
    rfl
  rw [sequence]
  have semantics := NatAdd.indexedReadSequence_eq s 8#5 10#5 9#5 11#5 limb
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    loaded restore
  simpa only [loadResult, pc, BitVec.add_assoc, BitVec.ofNat_add_ofNat] using semantics

theorem load_frame (s : ArmState) (base limb : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) : Frame s (loadResult s base limb) := by
  constructor
  · simp [loadResult, NatCompare.saved, state_simp_rules]
  · simp [loadResult, NatCompare.saved, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [loadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simp [loadResult, NatCompare.saved, state_simp_rules]
  · intro a outside
    have apart := outside ((r (.GPR 31#5) s).toNat - 16, 8) (by simp [writes])
    simpa [loadResult, NatCompare.saved, state_simp_rules] using
      BoolCodec.write_mem_bytes_frame s (r (.GPR 31#5) s - 16#64) 8
        (r (.GPR 9#5) s) a (by bv_omega) (by bv_omega)

end SszArm.Serialize.Size
