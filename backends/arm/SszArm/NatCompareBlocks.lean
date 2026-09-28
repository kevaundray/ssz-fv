import SszArm.NatCompareMemory
import SszArm.NatAddLoadState

namespace SszArm.NatCompare

open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def stackOps : List Op := [.p16, .p20, .p44, .p80, .p84, .p108, .p320, .p324, .p348, .p380, .p384, .p408, .p456, .p460, .p484, .p640, .p644, .p668]

/-- Symbolic GPR read-over-write: reading a register through a later register
write (user repair, exported for reuse). -/
theorem r_gpr_of_w_gpr (reg k : BitVec 5) (v : BitVec 64) (t : ArmState) :
    r (.GPR reg) (w (.GPR k) v t) = if reg = k then v else r (.GPR reg) t := by
  by_cases h : reg = k
  · subst h; simp only [r_of_w_same, if_true]
  · rw [if_neg h]; exact r_of_w_different (by simpa using h)

/-- Reading a register through a later PC write (user repair, exported). -/
theorem r_gpr_of_w_pc (reg : BitVec 5) (v : BitVec 64) (t : ArmState) :
    r (.GPR reg) (w .PC v t) = r (.GPR reg) t :=
  r_of_w_different (show StateField.GPR reg ≠ StateField.PC from by simp)

/-- A PC-only write preserves the comparison frame. -/
theorem frame_w_pc (s : ArmState) (v : BitVec 64) : Frame s (w .PC v s) := by
  refine ⟨w_program, ?_, fun x _ => ?_, fun x => ?_, fun a _ => ?_⟩
  · simp only [read_err]
    exact r_of_w_different (show StateField.ERR ≠ StateField.PC from by simp)
  · exact r_of_w_different (show StateField.GPR x ≠ StateField.PC from by simp)
  · exact r_of_w_different (show StateField.SFP x ≠ StateField.PC from by simp)
  · rw [ArmState.mem_w_eq_mem]

/-- A write to one comparison scratch register preserves the frame: the frame's
register clause excludes exactly the six written candidates. -/
theorem frame_w_gpr (s : ArmState) (reg : BitVec 5) (v : BitVec 64)
    (h : reg ∈ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5]) : Frame s (w (.GPR reg) v s) := by
  refine ⟨w_program, ?_, fun x hx => ?_, fun x => ?_, fun a _ => ?_⟩
  · simp only [read_err]
    exact r_of_w_different (show StateField.ERR ≠ StateField.GPR reg from by simp)
  · by_cases he : x = reg
    · rw [he] at hx
      exact absurd h hx
    · exact r_of_w_different (show StateField.GPR x ≠ StateField.GPR reg from
        fun hh => he (StateField.GPR.inj hh))
  · exact r_of_w_different (show StateField.SFP x ≠ StateField.GPR reg from by simp)
  · rw [ArmState.mem_w_eq_mem]

/-- `compare`'s four flag writes preserve the frame. -/
theorem frame_write_pstate (p : PState) (s : ArmState) : Frame s (write_pstate p s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [write_pstate, state_simp_rules]
  · simp [write_pstate, state_simp_rules]
  · intro x _; simp [write_pstate, state_simp_rules]
  · intro x; simp [write_pstate, state_simp_rules]
  · intro a _; simp [write_pstate, state_simp_rules, ArmState.mem_w_eq_mem]

/-- The PC increment inside every non-branch effect preserves the frame. -/
theorem frame_next (s : ArmState) : Frame s (next s) := frame_w_pc s (read_pc s + 4#64)

/-- A scratch register write after the PC increment. -/
theorem frame_put (s : ArmState) (reg : BitVec 5) (v : BitVec 64)
    (h : reg ∈ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5]) : Frame s (put reg v s) :=
  (frame_next s).trans (frame_w_gpr _ reg v h)

/-- The actual comparison of two operands (flags only, over a PC increment). -/
theorem frame_compare (a b : BitVec 64) (s : ArmState) :
    Frame s (Udivti3.compare a b s) :=
  (frame_next s).trans
    (frame_write_pstate (AddWithCarry a (~~~b) 1#1).2 (Udivti3.next s))

/-- A flag write after the PC increment. -/
theorem frame_write_pstate_next (p : PState) (s : ArmState) :
    Frame s (write_pstate p (next s)) :=
  (frame_next s).trans (frame_write_pstate p (next s))

/-- A scratch register write on top of a flag update. -/
theorem frame_w_gpr_pstate (s : ArmState) (k : BitVec 5) (v : BitVec 64) (p : PState)
    (hk : k ∈ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5]) :
    Frame s (w (.GPR k) v (write_pstate p (next s))) :=
  (frame_write_pstate_next _ _).trans (frame_w_gpr _ _ _ hk)

/-- Every effect outside the stack save/restore pairs is one of the preserved
shapes above: a protected register write, a PC write, a flag update, or a
flag update followed by a scratch write. -/
theorem readonly_op_frame (base : BitVec 64) (op : Op) (s : ArmState)
    (h : op ∉ stackOps) : Frame s (op.effect base s) := by
  cases op <;> simp_all only [stackOps, List.mem_cons, List.not_mem_nil, or_false,
    not_true_eq_false, true_or, or_true]
  all_goals
    simp only [Op.effect]
    first
      | with_reducible exact frame_put _ _ _ (by decide)
      | with_reducible exact frame_w_pc _ _
      | with_reducible exact frame_compare _ _ _
      | with_reducible exact frame_write_pstate_next _ _
      | with_reducible exact
          (frame_write_pstate_next _ _).trans (frame_w_gpr _ _ _ (by decide))

theorem readonly_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (hs : ∀ op ∈ ops, op ∉ stackOps) : Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih =>
    have hx := hs op List.mem_cons_self
    exact (readonly_op_frame base op s hx).trans
      (ih _ (fun op hop => hs op (List.mem_cons_of_mem _ hop)))

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

/-- Each load kind binds the same eight real architectural transforms (SP
adjust, temporary save, address calculation, indexed load and restore); the
binding is definitional, so the state algebra stays opaque. -/
theorem load_ops_sequence (s : ArmState) (base : BitVec 64) (kind : LoadKind) :
    block base kind.ops s = NatAdd.indexedReadSequence s kind.ptr kind.index kind.tmp kind.dst := by
  cases kind <;> rfl

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
  have hf : Follows base kind.ops s := by
    cases kind
    all_goals
      simp only [read_pc, LoadKind.start] at hp
      simp [LoadKind.ops, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hp, BitVec.add_assoc]
  rw [show 8 = kind.ops.length by cases kind <;> rfl, block_run base kind.ops s hc he ha hf,
    load_ops_sequence]
  have semantics := NatAdd.indexedReadSequence_eq s kind.ptr kind.index kind.tmp kind.dst word
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) (by cases kind <;> decide)
    (by cases kind <;> decide) hload hrestore
  simpa only [loadResult, hp, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc] using semantics

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
