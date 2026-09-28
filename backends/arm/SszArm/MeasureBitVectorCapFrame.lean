import SszArm.MeasureBitVectorScan
import SszArm.MeasureScanTransition

namespace SszArm.Measure.BitVector

/-- The cap conversion retains the original count pair and descriptor address;
only its five cap work registers may differ at the comparison entry. -/
structure CapFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [10#5, 11#5, 12#5, 13#5, 14#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ address : BitVec 64,
    address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ address.toNat → t.mem address = s.mem address

theorem CapFrame.refl (s : ArmState) : CapFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem CapFrame.sp {s t : ArmState} (frame : CapFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := frame.registers _ (by decide)

theorem CapFrame.trans {s t u : ArmState} (first : CapFrame s t) (second : CapFrame t u) :
    CapFrame s u := by
  refine ⟨second.program.trans first.program, second.error.trans first.error,
    fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
    fun reg => (second.vectors reg).trans (first.vectors reg), ?_⟩
  intro address outside
  exact (second.memory address (by simpa only [first.sp] using outside)).trans
    (first.memory address outside)

theorem CapFrame.aligned {s t : ArmState} (frame : CapFrame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, frame.sp] using aligned

theorem CapFrame.of_scan {s t : ArmState} (frame : ScanFrame s t)
    (high : r (.GPR 9#5) t = r (.GPR 9#5) s) : CapFrame s t := by
  refine ⟨frame.program, frame.error, ?_, frame.vectors, frame.memory⟩
  intro reg outside
  by_cases nine : reg = 9#5
  · subst reg
    exact high
  · apply frame.registers
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using
      show reg ≠ 9#5 ∧ reg ≠ 12#5 ∧ reg ≠ 13#5 ∧ reg ≠ 14#5 from
        ⟨nine, fun same => outside (by simp [same]), fun same => outside (by simp [same]),
          fun same => outside (by simp [same])⟩

theorem CapFrame.memoryFrame {s t : ArmState} (frame : CapFrame s t)
    (writes : List Delimited.Span)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (safe : 16 ≤ (r (.GPR 31#5) s).toNat) : Delimited.MemoryFrame writes s t := by
  intro address outside
  have separate := outside _ slot
  apply frame.memory
  rcases separate with low | high
  · exact Or.inl low
  · right
    omega

theorem CapFrame.source {s t : ArmState} (frame : CapFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64)) (source : NatCompare.Source s pointer words) :
    NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, frame.sp] using source

theorem CapFrame.words {s t : ArmState} (frame : CapFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (source : NatCompare.Source s pointer words) (observed : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := by
  intro index
  rw [← observed index]
  apply BoolCodec.read_bytes_congr
  intro byte within
  change t.mem _ = s.mem _
  apply frame.memory
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at source
  rcases source with ⟨stack, bound, empty | separate⟩
  · subst words
    exact Fin.elim0 index
  · have physical := index.isLt
    have address : (pointer + BitVec.ofNat 64 (8 * index.val) + BitVec.ofNat 64 byte).toNat =
        pointer.toNat + 8 * index.val + byte := by bv_omega
    rw [address]
    omega

end SszArm.Measure.BitVector
