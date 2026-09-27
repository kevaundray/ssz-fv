import SszArm.NatCompareMemory

namespace SszArm.NatCompare

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def stackOps : List Op := [.p16, .p20, .p44, .p80, .p84, .p108, .p320, .p324, .p348, .p380, .p384, .p408, .p456, .p460, .p484, .p640, .p644, .p668]

theorem readonly_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∉ stackOps) : Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have hf : Frame s (op.effect base s) := by
      cases op <;> simp_all only [stackOps, List.mem_cons, List.not_mem_nil, or_false,
        not_true_eq_false, true_or, or_true]
      all_goals
        constructor
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, Udivti3.compare,
            Udivti3.next, state_simp_rules]
        · intro reg
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
        · intro a ha
          simp [Op.effect, put, next, Udivti3.compare, Udivti3.next, state_simp_rules]
    exact hf.trans (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop)))

theorem block_zero (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∉ [.p256, .p572, .p580, .p704]) :
    r (.GPR 0#5) (block base ops s) = r (.GPR 0#5) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have hf : r (.GPR 0#5) (op.effect base s) = r (.GPR 0#5) s := by
      cases op <;> simp_all [Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules]
    exact (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop))).trans hf

inductive LoadKind where
  | trimLeft | trimRight | right | left | leftSmall | smallRight
  deriving DecidableEq

def LoadKind.start : LoadKind → Nat
  | .trimLeft => 16 | .trimRight => 80 | .right => 320
  | .left => 380 | .leftSmall => 456 | .smallRight => 640

def LoadKind.tmp : LoadKind → BitVec 5
  | .trimLeft | .left | .leftSmall => 10#5
  | .trimRight => 9#5
  | .right | .smallRight => 11#5

def LoadKind.dst : LoadKind → BitVec 5
  | .trimLeft => 11#5 | .trimRight => 12#5
  | .right | .smallRight => 10#5 | .left | .leftSmall => 8#5

def LoadKind.ptr : LoadKind → BitVec 5
  | .trimLeft | .trimRight => 8#5
  | .right | .smallRight => 2#5 | .left | .leftSmall => 0#5

def LoadKind.index : LoadKind → BitVec 5
  | .trimRight => 10#5 | _ => 9#5

def LoadKind.ops : LoadKind → List Op
  | .trimLeft => [.p16, .p20, .p24, .p28, .p32, .p36, .p40, .p44]
  | .trimRight => [.p80, .p84, .p88, .p92, .p96, .p100, .p104, .p108]
  | .right => [.p320, .p324, .p328, .p332, .p336, .p340, .p344, .p348]
  | .left => [.p380, .p384, .p388, .p392, .p396, .p400, .p404, .p408]
  | .leftSmall => [.p456, .p460, .p464, .p468, .p472, .p476, .p480, .p484]
  | .smallRight => [.p640, .p644, .p648, .p652, .p656, .p660, .p664, .p668]

def loadResult (s : ArmState) (base : BitVec 64) (kind : LoadKind) (word : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 32)) (w (.GPR kind.dst) word (saved s kind.tmp))

/-- Eight real lowered instructions, including the save and the restore. -/
theorem load_run (s : ArmState) (base word : BitVec 64) (kind : LoadKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hload : read_mem_bytes 8 (r (.GPR kind.ptr) s + (r (.GPR kind.index) s <<< 3))
      (saved s kind.tmp) = word) :
    run 8 s = loadResult s base kind word := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s kind.tmp) =
      r (.GPR kind.tmp) s := BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hf : Follows base kind.ops s := by
    cases kind <;>
      simp [LoadKind.ops, LoadKind.start, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = kind.ops.length by cases kind <;> rfl, block_run base kind.ops s hc he ha hf]
  simp only [saved] at hload hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h8 : reg = 8#5 <;> by_cases h9 : reg = 9#5 <;> by_cases h10 : reg = 10#5 <;>
        by_cases h11 : reg = 11#5 <;> by_cases h12 : reg = 12#5 <;>
        by_cases h31 : reg = 31#5 <;> (try subst reg) <;> cases kind <;>
        simp_all (config := {decide := true, instances := true})
          [loadResult, LoadKind.start, LoadKind.ops, LoadKind.tmp, LoadKind.dst,
            LoadKind.ptr, LoadKind.index, block, Op.effect, put, next, saved,
            state_simp_rules, read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | PC =>
      cases kind <;>
        simp_all (config := {decide := true, instances := true})
          [loadResult, LoadKind.start, LoadKind.ops, LoadKind.tmp, LoadKind.dst,
            LoadKind.ptr, LoadKind.index, block, Op.effect, put, next, saved,
            state_simp_rules, read_spill_w, BitVec.sub_add_cancel, BitVec.add_assoc]
    | SFP reg =>
      cases kind <;> simp [loadResult, LoadKind.ops, block, Op.effect, put, next, saved, state_simp_rules]
    | FLAG flag =>
      cases kind <;> simp [loadResult, LoadKind.ops, block, Op.effect, put, next, saved, state_simp_rules]
    | ERR =>
      cases kind <;> simp [loadResult, LoadKind.ops, block, Op.effect, put, next, saved, state_simp_rules]
  · cases kind <;> simp [loadResult, LoadKind.ops, block, Op.effect, put, next, saved, state_simp_rules]
  · intro n addr
    cases kind <;>
      simp [loadResult, LoadKind.ops, LoadKind.tmp, block, Op.effect, put, next,
        saved, state_simp_rules, read_spill_w]

theorem load_frame (s : ArmState) (base word : BitVec 64) (kind : LoadKind)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : Frame s (loadResult s base kind word) := by
  have hf := saved_frame s kind.tmp hs
  constructor
  · simpa [loadResult, state_simp_rules] using hf.program
  · simpa [loadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    cases kind <;> simpa (disch := simp_all)
      [loadResult, LoadKind.dst, state_simp_rules] using hf.registers reg (by simpa using hr)
  · intro reg; simpa [loadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [loadResult, state_simp_rules] using hf.memory a ha

@[simp] theorem load_zero (s : ArmState) (base word : BitVec 64) (kind : LoadKind) :
    r (.GPR 0#5) (loadResult s base kind word) = r (.GPR 0#5) s := by
  cases kind <;> simp [loadResult, LoadKind.dst, saved, state_simp_rules]

theorem limb_load (s : ArmState) (pointer : BitVec 64) (words : List (BitVec 64))
    (n : Nat) (tmp : BitVec 5) (hn : n < words.length)
    (hs : Source s pointer words) (hm : Words s pointer words) :
    read_mem_bytes 8 (pointer + (BitVec.ofNat 64 n <<< 3)) (saved s tmp) = words[n]?.getD 0 := by
  have hshift : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8*n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have := hs.2.1
    omega
  rw [hshift]
  have hl := (saved_frame s tmp hs.1).words pointer words hs hm ⟨n, hn⟩
  simpa [List.getElem?_eq_getElem hn] using hl

end SszArm.NatCompare
