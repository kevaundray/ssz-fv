import SszArm.NatMulReturnFrame
import SszArm.NatMulScanLoad
import SszArm.NatMulWordScanFrame
import SszNatOperandNormalization

namespace SszArm.NatMul

open UintCodec SszNative.Limbs
open Delimited (MemoryFrame)

structure NormalizeFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 20#5, 23#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem NormalizeFrame.refl (s : ArmState) : NormalizeFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem NormalizeFrame.sp {s t : ArmState} (h : NormalizeFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem NormalizeFrame.trans {s t u : ArmState} (h : NormalizeFrame s t)
    (k : NormalizeFrame t u) : NormalizeFrame s u := by
  refine ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), ?_⟩
  intro a ha
  exact (k.memory a (by simpa only [h.sp] using ha)).trans (h.memory a ha)

theorem NormalizeFrame.code {s t : ArmState} (h : NormalizeFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem NormalizeFrame.aligned {s t : ArmState} (h : NormalizeFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem NormalizeFrame.source {s t : ArmState} (h : NormalizeFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem NormalizeFrame.words {s t : ArmState} (h : NormalizeFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  apply h.memory
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at hs
  rcases hs with ⟨hsp, hbound, hempty | hsep⟩
  · subst words; exact Fin.elim0 i
  · have hi := i.isLt
    have haddr : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
        pointer.toNat + 8 * i.val + j := by bv_omega
    rw [haddr]
    omega

theorem NormalizeFrame.frame {s t : ArmState} (h : NormalizeFrame s t) (out : BitVec 64) :
    MemoryFrame (returnWrites s out) s t := by
  intro a outside
  exact h.memory a (outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnWrites]))

theorem NormalizeFrame.space {s t : ArmState} (h : NormalizeFrame s t) {out : BitVec 64}
    (space : ReturnSpace s out) : ReturnSpace t out := by
  exact ⟨by simpa only [h.sp] using space.stack,
    by simpa only [h.sp] using space.savedBound, space.output,
    by simpa only [h.sp] using space.separate⟩

theorem NormalizeFrame.saved {entry s t : ArmState} (h : NormalizeFrame s t)
    (saved : Saved entry s) {out : BitVec 64} (space : ReturnSpace s out) : Saved entry t :=
  saved.return_frame space (return_frame_widen (h.frame out)) h.sp
    (h.registers _ (by decide)) h.vectors

def normalizePureOps : List Op :=
  [.p1012, .p1048, .p1052, .p1056, .p1060, .p1064, .p1068, .p1072,
   .p1276, .p1280, .p1284, .p1288, .p1292]

theorem normalize_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ normalizePureOps) : NormalizeFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NormalizeFrame.refl s
  | cons op ops ih =>
    have hx := allowed op List.mem_cons_self
    have frame : NormalizeFrame s (op.effect base s) := by
      simp only [normalizePureOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals subst op
      all_goals
        constructor
        · exact Op.program _ _ _
        · exact Op.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg; exact Op.sfp _ _ _ _
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact frame.trans (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop)))

def normalizeLoadOps : List Op :=
  [.p1016, .p1020, .p1024, .p1028, .p1032, .p1036, .p1040, .p1044]

def normalizeLoaded (s : ArmState) (base word : BitVec 64) : ArmState :=
  w .PC (base + 1048#64) (w (.GPR 9#5) word (NatCompare.saved s 10#5))

theorem normalize_load_run (s : ArmState) (base word : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 1016#64) (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 20#5) s + (r (.GPR 23#5) s <<< 3)).toNat + 8 ≤ 2^64)
    (separate : (r (.GPR 20#5) s + (r (.GPR 23#5) s <<< 3)).toNat + 8 ≤
        (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤
          (r (.GPR 20#5) s + (r (.GPR 23#5) s <<< 3)).toNat)
    (value : read_mem_bytes 8 (r (.GPR 20#5) s + (r (.GPR 23#5) s <<< 3)) s = word) :
    run 8 s = normalizeLoaded s base word := by
  have hload : read_mem_bytes 8 (r (.GPR 20#5) s + (r (.GPR 23#5) s <<< 3))
      (NatCompare.saved s 10#5) = word := by
    unfold NatCompare.saved
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      physical (by bv_omega) (by bv_omega)]
    exact value
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 10#5) = r (.GPR 10#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + 1016#64 := hp
  have hf : Follows base normalizeLoadOps s := by
    simp [normalizeLoadOps, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = normalizeLoadOps.length by rfl, block_run base normalizeLoadOps s hc he ha hf]
  change NatAdd.indexedReadSequence s 20#5 23#5 10#5 9#5 = _
  have semantics := NatAdd.indexedReadSequence_eq s 20#5 23#5 10#5 9#5 word
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hload hrestore
  simpa only [normalizeLoaded, hp, BitVec.add_assoc] using semantics

theorem normalize_load_frame (s : ArmState) (base word : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NormalizeFrame s (normalizeLoaded s base word) := by
  have hf := NatCompare.saved_frame s 10#5 hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [normalizeLoaded, state_simp_rules] using hf.program
  · simpa [normalizeLoaded, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [normalizeLoaded, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [normalizeLoaded, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [normalizeLoaded, state_simp_rules] using hf.memory a ha

end SszArm.NatMul
