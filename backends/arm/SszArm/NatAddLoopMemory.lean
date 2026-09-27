import SszArm.NatAddBlocks
import SszArm.NatAddMemory

namespace SszArm.NatAdd

open UintCodec
open NatCompare (Source Words saved read_spill_w)
open Delimited (Span Protected MemoryFrame)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The carry loops retain the input ABI, output base, low word, and all
callee-saved registers. Only the six carry-loop work registers may change. -/
structure LoopFrame (writes : List Span) (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [12#5, 13#5, 14#5, 15#5, 16#5, 17#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : MemoryFrame writes s t

theorem LoopFrame.refl (writes : List Span) (s : ArmState) : LoopFrame writes s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, MemoryFrame.refl writes s⟩

theorem LoopFrame.trans {writes : List Span} {s t u : ArmState}
    (h : LoopFrame writes s t) (k : LoopFrame writes t u) : LoopFrame writes s u :=
  ⟨k.program.trans h.program, k.error.trans h.error,
   fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
   fun reg => (k.vectors reg).trans (h.vectors reg), h.memory.trans k.memory⟩

theorem LoopFrame.sp {writes : List Span} {s t : ArmState} (h : LoopFrame writes s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem LoopFrame.aligned {writes : List Span} {s t : ArmState}
    (h : LoopFrame writes s t) (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem LoopFrame.code {writes : List Span} {s t : ArmState}
    (h : LoopFrame writes s t) {base : BitVec 64} (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem LoopFrame.source {writes : List Span} {s t : ArmState}
    (h : LoopFrame writes s t) (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : Source s pointer words) : Source t pointer words := by
  simpa only [Source, ByteView.Source, BitVec.ofNat_eq_ofNat, h.sp] using hs

theorem LoopFrame.words {writes : List Span} {s t : ArmState}
    (h : LoopFrame writes s t) (pointer : BitVec 64) (words : List (BitVec 64))
    (hs : Source s pointer words) (hm : Words s pointer words)
    (owned : Protected writes pointer.toNat (8 * words.length)) : Words t pointer words := by
  intro i
  rw [← hm i]
  have hi := i.isLt
  have bound := hs.2.1
  have address : (pointer + BitVec.ofNat 64 (8 * i.val)).toNat =
      pointer.toNat + 8 * i.val := by bv_omega
  exact h.memory.read _ 8 (by rw [address]; omega)
    (by rw [address]; exact owned.subspan (8 * i.val) 8 (by omega))

inductive StoreKind where
  | large | small
  deriving DecidableEq

def StoreKind.start : StoreKind → Nat
  | .large => 1628 | .small => 1920

def StoreKind.index : StoreKind → BitVec 5
  | .large => 15#5 | .small => 14#5

def StoreKind.src : StoreKind → BitVec 5
  | .large => 16#5 | .small => 15#5

def StoreKind.ops : StoreKind → List Op
  | .large => [.p1628, .p1632, .p1636, .p1640, .p1644, .p1648, .p1652, .p1656]
  | .small => [.p1920, .p1924, .p1928, .p1932, .p1936, .p1940, .p1944, .p1948]

def storeAddress (s : ArmState) (kind : StoreKind) : BitVec 64 :=
  r (.GPR 9#5) s + (r (.GPR kind.index) s <<< 3)

def storeMemory (s : ArmState) (kind : StoreKind) : ArmState :=
  write_mem_bytes 8 (storeAddress s kind) (r (.GPR kind.src) s) (saved s 10#5)

def storeResult (s : ArmState) (base : BitVec 64) (kind : StoreKind) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.start + 32)) (storeMemory s kind)

/-- Restoring the indexed store's two temporary fields leaves no register
mutation. The statement is independent of the actual store bytes. -/
theorem store_restore_fields (s : ArmState) (tmp : BitVec 5) (address : BitVec 64)
    (tmpSP : tmp ≠ 31#5) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR tmp) (r (.GPR tmp) s)
        (w (.GPR tmp) address
          (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) s))) = s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases hsp : reg = 31#5 <;> by_cases ht : reg = tmp <;>
        (try subst reg) <;> simp_all [state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp only [w_program]
  · intro n pointer; simp only [read_mem_bytes_of_w]

/-- State algebra for the eight real indexed-store instructions. -/
def indexedStoreSequence (s : ArmState) (ptr index tmp src : BitVec 5) : ArmState :=
  let s := put 31 (r (.GPR 31#5) s - 16#64) s
  let s := next (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR tmp) s) s)
  let s := put tmp (r (.GPR index) s) s
  let s := put tmp (r (.GPR tmp) s <<< 3) s
  let s := put tmp (r (.GPR ptr) s + r (.GPR tmp) s) s
  let s := next (write_mem_bytes 8 (r (.GPR tmp) s) (r (.GPR src) s) s)
  let s := put tmp (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  put 31 (r (.GPR 31#5) s + 16#64) s

theorem indexedStoreSequence_eq (s : ArmState) (ptr index tmp src : BitVec 5)
    (tmpSP : tmp ≠ 31#5) (ptrSP : ptr ≠ 31#5) (indexSP : index ≠ 31#5)
    (srcSP : src ≠ 31#5) (ptrTmp : ptr ≠ tmp) (srcTmp : src ≠ tmp)
    (restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (write_mem_bytes 8 (r (.GPR ptr) s + (r (.GPR index) s <<< 3))
        (r (.GPR src) s) (saved s tmp)) = r (.GPR tmp) s) :
    indexedStoreSequence s ptr index tmp src =
      w .PC (read_pc s + 32#64)
        (write_mem_bytes 8 (r (.GPR ptr) s + (r (.GPR index) s <<< 3))
          (r (.GPR src) s) (saved s tmp)) := by
  have spTmp : (31#5) ≠ tmp := Ne.symm tmpSP
  have restored := store_restore_fields
    (write_mem_bytes 8 (r (.GPR ptr) s + (r (.GPR index) s <<< 3))
      (r (.GPR src) s) (saved s tmp))
    tmp (r (.GPR ptr) s + (r (.GPR index) s <<< 3)) tmpSP
  simp only [saved, r_of_write_mem_bytes] at restore restored ⊢
  simpa (config := {decide := true}) (disch := simp_all)
    [indexedStoreSequence, put, next, load_store_field, load_gpr_pc,
      state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel, spTmp, restore] using
    congrArg (w .PC (read_pc s + 32#64)) restored

theorem store_ops_sequence (s : ArmState) (base : BitVec 64) (kind : StoreKind) :
    block base kind.ops s = indexedStoreSequence s 9#5 kind.index 10#5 kind.src := by
  cases kind <;> rfl

/-- All eight actual indexed-store instructions. The flags from ADDS survive
both the temporary spill and the output write, and X10 and SP are restored. -/
theorem store_run (s : ArmState) (base : BitVec 64) (kind : StoreKind)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.start)
    (hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (storeMemory s kind) =
      r (.GPR 10#5) s) :
    run 8 s = storeResult s base kind := by
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.start := hp
  have hf : Follows base kind.ops s := by
    cases kind <;> simp [StoreKind.ops, StoreKind.start, Follows, Op.row, Op.effect,
      put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = kind.ops.length by cases kind <;> rfl,
    block_run base kind.ops s hc he ha hf]
  rw [store_ops_sequence]
  have semantics := indexedStoreSequence_eq s 9#5 kind.index 10#5 kind.src
    (by decide) (by decide) (by cases kind <;> decide)
    (by cases kind <;> decide) (by decide) (by cases kind <;> decide) hrestore
  simpa only [storeResult, storeMemory, storeAddress, hp, BitVec.ofNat_add,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using semantics

/-- Static physical separation supplies the restore premise of `store_run`. -/
theorem store_restore (s : ArmState) (kind : StoreKind)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (storeAddress s kind).toNat + 8 ≤ 2^64)
    (apart : Protected [((storeAddress s kind).toNat, 8)]
      (r (.GPR 31#5) s - 16#64).toNat 8) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (storeMemory s kind) =
      r (.GPR 10#5) s := by
  unfold storeMemory
  rw [(Delimited.store_frame (saved s 10#5) (storeAddress s kind) 8
    (r (.GPR kind.src) s) physical).read _ 8 (by bv_omega) apart]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)

/-- A store touches only its eight-byte output word and the lowering slot. -/
theorem store_frame (s : ArmState) (base : BitVec 64) (kind : StoreKind)
    (writes : List Span) (hs : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (storeAddress s kind).toNat + 8 ≤ 2^64)
    (slot : ((r (.GPR 31#5) s).toNat - 16, 16) ∈ writes)
    (word : ∀ a : BitVec 64,
      (storeAddress s kind).toNat ≤ a.toNat →
      a.toNat < (storeAddress s kind).toNat + 8 →
      ∃ span ∈ writes, span.1 ≤ a.toNat ∧ a.toNat < span.1 + span.2) :
    LoopFrame writes s (storeResult s base kind) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [storeResult, storeMemory, saved, state_simp_rules]
  · simp [storeResult, storeMemory, saved, state_simp_rules]
  · intro reg hr; simp [storeResult, storeMemory, saved, state_simp_rules]
  · intro reg; simp [storeResult, storeMemory, saved, state_simp_rules]
  · intro a outside
    have hout : a.toNat < (storeAddress s kind).toNat ∨
        (storeAddress s kind).toNat + 8 ≤ a.toNat := by
      by_cases low : a.toNat < (storeAddress s kind).toNat
      · exact Or.inl low
      · by_cases high : (storeAddress s kind).toNat + 8 ≤ a.toNat
        · exact Or.inr high
        · obtain ⟨span, member, lo, hi⟩ := word a (by omega) (by omega)
          have := outside span member
          omega
    have hslot := outside _ slot
    simp only [storeResult, ArmState.mem_w_eq_mem]
    exact (BoolCodec.write_mem_bytes_frame (saved s 10#5) (storeAddress s kind) 8
      (r (.GPR kind.src) s) a physical hout).trans
      (BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega))

end SszArm.NatAdd
