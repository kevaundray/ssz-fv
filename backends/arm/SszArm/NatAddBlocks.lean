import SszArm.NatAddLoadState
import SszArm.NatCompareBlocks

namespace SszArm.NatAdd

open UintCodec
open NatCompare (Source Words saved read_spill_w)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The seven indexed reads in the linked image. Each expands to the real
16-byte SP adjustment, temporary save, address calculation, load and restore. -/
inductive LoadKind where
  | trimLeft | trimRight | normalizeLeft | normalizeRight
  | loopLeft | loopRight | loopRightSmall
  deriving DecidableEq

def LoadKind.start : LoadKind → Nat
  | .trimLeft => 20 | .trimRight => 316 | .normalizeLeft => 592
  | .normalizeRight => 416 | .loopLeft => 1700 | .loopRight => 1572
  | .loopRightSmall => 1880

def LoadKind.tmp : LoadKind → BitVec 5
  | .trimLeft => 10#5
  | .normalizeLeft | .normalizeRight => 11#5
  | _ => 9#5

def LoadKind.dst : LoadKind → BitVec 5
  | .trimLeft => 11#5 | .trimRight => 12#5
  | .normalizeLeft | .normalizeRight => 10#5
  | .loopLeft => 16#5 | .loopRight => 17#5 | .loopRightSmall => 15#5

def LoadKind.ptr : LoadKind → BitVec 5
  | .trimLeft => 8#5 | .normalizeLeft | .loopLeft => 1#5
  | _ => 3#5

def LoadKind.index : LoadKind → BitVec 5
  | .trimLeft | .normalizeLeft | .normalizeRight => 9#5
  | .trimRight => 11#5 | .loopLeft | .loopRight => 15#5
  | .loopRightSmall => 14#5

def LoadKind.ops : LoadKind → List Op
  | .trimLeft => [.p20, .p24, .p28, .p32, .p36, .p40, .p44, .p48]
  | .trimRight => [.p316, .p320, .p324, .p328, .p332, .p336, .p340, .p344]
  | .normalizeLeft => [.p592, .p596, .p600, .p604, .p608, .p612, .p616, .p620]
  | .normalizeRight => [.p416, .p420, .p424, .p428, .p432, .p436, .p440, .p444]
  | .loopLeft => [.p1700, .p1704, .p1708, .p1712, .p1716, .p1720, .p1724, .p1728]
  | .loopRight => [.p1572, .p1576, .p1580, .p1584, .p1588, .p1592, .p1596, .p1600]
  | .loopRightSmall => [.p1880, .p1884, .p1888, .p1892, .p1896, .p1900, .p1904, .p1908]

def loadResult (s : ArmState) (base : BitVec 64) (kind : LoadKind)
    (word : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 32))
    (w (.GPR kind.dst) word (saved s kind.tmp))

/-- Each enum arm is merely a binding of the same eight real architectural
transforms. The state-algebra proof is opaque and shared between all seven sites. -/
theorem load_ops_sequence (s : ArmState) (base : BitVec 64) (kind : LoadKind) :
    block base kind.ops s = indexedReadSequence s kind.ptr kind.index kind.tmp kind.dst := by
  cases kind <;> rfl

/-- Exact execution of a lowered indexed read, including its persistent spill. -/
theorem load_run (s : ArmState) (base word : BitVec 64) (kind : LoadKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hload : read_mem_bytes 8
      (r (.GPR kind.ptr) s + (r (.GPR kind.index) s <<< 3))
      (saved s kind.tmp) = word) :
    run 8 s = loadResult s base kind word := by
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (saved s kind.tmp) =
      r (.GPR kind.tmp) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hf : Follows base kind.ops s := by
    cases kind <;>
      simp [LoadKind.ops, LoadKind.start, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = kind.ops.length by cases kind <;> rfl,
    block_run base kind.ops s hc he ha hf]
  rw [load_ops_sequence]
  have semantics := indexedReadSequence_eq s kind.ptr kind.index kind.tmp kind.dst word
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) hload hrestore
  simpa only [loadResult, hp, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc] using semantics

/-- Width and normalization reads have precisely the comparison pilot's frame. -/
theorem load_compare_frame (s : ArmState) (base word : BitVec 64) (kind : LoadKind)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (hk : kind ∈ [.trimLeft, .trimRight, .normalizeLeft, .normalizeRight]) :
    NatCompare.Frame s (loadResult s base kind word) := by
  have hf := NatCompare.saved_frame s kind.tmp hs
  constructor
  · simpa [loadResult, state_simp_rules] using hf.program
  · simpa [loadResult, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    cases kind <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, or_self, false_or]
    all_goals simpa (disch := simp_all)
      [loadResult, LoadKind.dst, state_simp_rules] using hf.registers reg (by simpa using hr)
  · intro reg; simpa [loadResult, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [loadResult, state_simp_rules] using hf.memory a ha

/-- Width-scan arithmetic does not touch the output or original operand pairs. -/
def scanOps : List Op :=
  [.p0, .p4, .p8, .p12, .p16, .p52, .p56, .p60, .p64, .p68,
   .p72, .p76, .p80, .p84, .p88, .p92, .p96, .p104, .p108, .p112,
   .p116, .p120, .p124, .p128, .p132, .p136, .p140,
   .p292, .p296, .p300, .p304, .p308, .p312, .p348, .p352, .p356,
   .p360, .p364, .p368, .p372, .p376, .p380, .p408, .p412,
   .p448, .p452, .p456, .p460, .p464, .p468, .p572, .p576,
   .p580, .p584, .p588, .p624, .p628, .p632]

theorem scan_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∈ scanOps) : NatCompare.Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact NatCompare.Frame.refl s
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have hf : NatCompare.Frame s (op.effect base s) := by
      cases op <;> simp_all only [scanOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, or_self]
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

theorem scan_code {s t : ArmState} (hf : NatCompare.Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, hf.program] using hc

@[simp] theorem load_zero (s : ArmState) (base word : BitVec 64) (kind : LoadKind) :
    r (.GPR 0#5) (loadResult s base kind word) = r (.GPR 0#5) s := by
  cases kind <;> simp [loadResult, LoadKind.dst, saved, state_simp_rules]

theorem scan_zero (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∈ scanOps) :
    r (.GPR 0#5) (block base ops s) = r (.GPR 0#5) s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    have hz : r (.GPR 0#5) (op.effect base s) = r (.GPR 0#5) s := by
      cases op <;> simp_all [scanOps, Op.effect, put, next, Udivti3.compare,
        Udivti3.next, state_simp_rules]
    exact (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop))).trans hz

end SszArm.NatAdd
