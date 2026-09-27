import SszArm.NatDivisionExec
import SszArm.NatCompareBlocks

namespace SszArm.NatDivision

open UintCodec SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The four indexed reads in the scans and the forward copy use the same
lowering spill, but the physical scan already carries a byte offset. -/
inductive ScanLoad where
  | initial | physical | quotient | copy
  deriving DecidableEq

def ScanLoad.start : ScanLoad → Nat
  | .initial => 48 | .physical => 132 | .quotient => 1044 | .copy => 372

def ScanLoad.size : ScanLoad → Nat
  | .physical => 7 | _ => 8

def ScanLoad.ops : ScanLoad → List Op
  | .initial => [.p48, .p52, .p56, .p60, .p64, .p68, .p72, .p76]
  | .physical => [.p132, .p136, .p140, .p144, .p148, .p152, .p156]
  | .quotient => [.p1044, .p1048, .p1052, .p1056, .p1060, .p1064, .p1068, .p1072]
  | .copy => [.p372, .p376, .p380, .p384, .p388, .p392, .p396, .p400]

def ScanLoad.address (kind : ScanLoad) (s : ArmState) : BitVec 64 :=
  match kind with
  | .initial | .copy => r (.GPR 1#5) s + (r (.GPR 9#5) s <<< 3)
  | .physical => r (.GPR 9#5) s + r (.GPR 23#5) s
  | .quotient => r (.GPR 24#5) s + (r (.GPR 9#5) s <<< 3)

def scanLoadResult (s : ArmState) (base : BitVec 64) (kind : ScanLoad)
    (word : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 4 * kind.size))
    (w (.GPR 10#5) word (NatCompare.saved s 11#5))

/-- Exact execution of all lowering instructions, including the saved X11. -/
theorem scan_load_run (s : ArmState) (base word : BitVec 64) (kind : ScanLoad)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hload : read_mem_bytes 8 (kind.address s) (NatCompare.saved s 11#5) = word) :
    run kind.size s = scanLoadResult s base kind word := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 11#5) = r (.GPR 11#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hf : Follows base kind.ops s := by
    cases kind <;> simp [ScanLoad.ops, ScanLoad.start, Follows, Op.row,
      Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show kind.size = kind.ops.length by cases kind <;> rfl,
    block_run base kind.ops s hc he ha hf]
  simp only [NatCompare.saved, ScanLoad.address] at hload hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h10 : reg = 10#5 <;> by_cases h11 : reg = 11#5 <;>
        by_cases h31 : reg = 31#5 <;> (try subst reg) <;> cases kind <;>
        simp_all (config := {decide := true, instances := true})
          [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.ops,
            ScanLoad.address, block, Op.effect, put, next, NatCompare.saved,
            state_simp_rules, NatCompare.read_spill_w,
            BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      cases kind <;> simp_all (config := {decide := true, instances := true})
        [scanLoadResult, ScanLoad.start, ScanLoad.size, ScanLoad.ops,
          block, Op.effect, put, next, NatCompare.saved, state_simp_rules,
          NatCompare.read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg =>
      cases kind <;> simp [scanLoadResult, ScanLoad.ops, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
    | FLAG flag =>
      cases kind <;> simp [scanLoadResult, ScanLoad.ops, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
    | ERR =>
      cases kind <;> simp [scanLoadResult, ScanLoad.ops, block, Op.effect,
        put, next, NatCompare.saved, state_simp_rules]
  · cases kind <;> simp [scanLoadResult, ScanLoad.ops, block, Op.effect,
      put, next, NatCompare.saved, state_simp_rules]
  · intro n addr
    cases kind <;> simp [scanLoadResult, ScanLoad.ops, block, Op.effect,
      put, next, NatCompare.saved, state_simp_rules, NatCompare.read_spill_w]

/-- Scans preserve all registers outside their six explicit work registers,
as well as every byte outside the lowering slot. -/
structure ScanFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 22#5, 23#5, 24#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a : BitVec 64,
    a.toNat < (r (.GPR 31#5) s).toNat - 16 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat →
    t.mem a = s.mem a

theorem ScanFrame.refl (s : ArmState) : ScanFrame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem ScanFrame.sp {s t : ArmState} (hf : ScanFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := hf.registers _ (by decide)

theorem ScanFrame.trans {s t u : ArmState} (st : ScanFrame s t) (tu : ScanFrame t u) :
    ScanFrame s u := by
  refine ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg), ?_⟩
  intro a ha
  exact (tu.memory a (by simpa only [st.sp] using ha)).trans (st.memory a ha)

theorem ScanFrame.code {s t : ArmState} (hf : ScanFrame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, hf.program] using hc

theorem ScanFrame.aligned {s t : ArmState} (hf : ScanFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, hf.sp] using ha

theorem ScanFrame.source {s t : ArmState} (hf : ScanFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) : NatCompare.Source t pointer words := by
  simpa only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat, hf.sp] using hs

theorem ScanFrame.words {s t : ArmState} (hf : ScanFrame s t)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : NatCompare.Source s pointer words) (hm : NatCompare.Words s pointer words) :
    NatCompare.Words t pointer words := by
  intro i
  rw [← hm i]
  apply BoolCodec.read_bytes_congr
  intro j hj
  apply hf.memory
  simp only [NatCompare.Source, ByteView.Source, BitVec.ofNat_eq_ofNat] at hs
  rcases hs with ⟨hsp, hbound, hempty | hsep⟩
  · subst words; exact Fin.elim0 i
  · have hi := i.isLt
    have haddr : (pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j).toNat =
        pointer.toNat + 8 * i.val + j := by bv_omega
    rw [haddr]
    omega

theorem scan_load_frame (s : ArmState) (base word : BitVec 64) (kind : ScanLoad)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ScanFrame s (scanLoadResult s base kind word) := by
  have hf := NatCompare.saved_frame s 11#5 hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using hf.program
  · simpa [scanLoadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [scanLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [scanLoadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanLoadResult, state_simp_rules] using hf.memory a ha

/-- Read-only instructions used at scan heads and exits. -/
def scanPureOps : List Op :=
  [.p36, .p40, .p44, .p80, .p84, .p88, .p92, .p96, .p100,
   .p104, .p108, .p112, .p116, .p120, .p124, .p128, .p160, .p164, .p168,
   .p1032, .p1036, .p1040, .p1076, .p1080, .p1084, .p1088, .p1092,
   .p1096, .p1100, .p1104, .p1108, .p1112, .p1116]

theorem scan_pure_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hops : ∀ op ∈ ops, op ∈ scanPureOps) : ScanFrame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact ScanFrame.refl s
  | cons op ops ih =>
    have hx := hops op List.mem_cons_self
    have hf : ScanFrame s (op.effect base s) := by
      simp only [scanPureOps, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx |
        hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx |
        hx | hx | hx | hx | hx | hx | hx
      all_goals subst op
      all_goals
        constructor
        · exact Op.program _ _ _
        · exact Op.error _ _ _
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]
        · intro reg; exact Op.sfp _ _ _ _
        · intro a ha; simp [Op.effect, put, next, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hops op (List.mem_cons_of_mem _ hop)))

end SszArm.NatDivision
