import SszArm.BitListImpl
import SszArm.BoolActivation

namespace SszArm.BitList

namespace Block

inductive Op where
  | p564 | p568 | p572 | p576 | p580 | p584 | p588 | p592 | p596 | p600
  | p2052 | p2056 | p2060 | p2064 | p2068 | p2072 | p2076 | p2080
  | p4732 | p4736 | p4740 | p4744 | p4748 | p4752 | p4756 | p4760
  deriving DecidableEq

def Op.row : Op → Nat × BitVec 32
  | .p564 => (564, 0xaa1303e4#32)
  | .p568 => (568, 0xa9564ff4#32)
  | .p572 => (572, 0xa95557f6#32)
  | .p576 => (576, 0x91002021#32)
  | .p580 => (580, 0xa9545ff8#32)
  | .p584 => (584, 0xa95367fa#32)
  | .p588 => (588, 0xa9526ffc#32)
  | .p592 => (592, 0xa9517bfd#32)
  | .p596 => (596, 0x9105c3ff#32)
  | .p600 => (600, 0x140009ba#32)
  | .p2052 => (2052, 0xa940a029#32)
  | .p2056 => (2056, 0x910243e1#32)
  | .p2060 => (2060, 0xaa1303e4#32)
  | .p2064 => (2064, 0xa909a3e9#32)
  | .p2068 => (2068, 0x52800028#32)
  | .p2072 => (2072, 0xf9004be8#32)
  | .p2076 => (2076, 0x94000849#32)
  | .p2080 => (2080, 0x14000297#32)
  | .p4732 => (4732, 0xa9564ff4#32)
  | .p4736 => (4736, 0xa95557f6#32)
  | .p4740 => (4740, 0xa9545ff8#32)
  | .p4744 => (4744, 0xa95367fa#32)
  | .p4748 => (4748, 0xa9526ffc#32)
  | .p4752 => (4752, 0xa9517bfd#32)
  | .p4756 => (4756, 0x9105c3ff#32)
  | .p4760 => (4760, 0xd65f03c0#32)

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def put (reg : BitVec 5) (value : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) value (next s)

def pair (first second : BitVec 5) (address : BitVec 64) (s : ArmState) : ArmState :=
  next (w (.GPR second) (read_mem_bytes 8 (address + 8#64) s)
    (w (.GPR first) (read_mem_bytes 8 address s) s))

def Op.effect : Op → ArmState → ArmState
  | .p564, s | .p2060, s => put 4 (r (.GPR 19#5) s) s
  | .p568, s | .p4732, s => pair 20 19 (r (.GPR 31#5) s + 352#64) s
  | .p572, s | .p4736, s => pair 22 21 (r (.GPR 31#5) s + 336#64) s
  | .p576, s => put 1 (r (.GPR 1#5) s + 8#64) s
  | .p580, s | .p4740, s => pair 24 23 (r (.GPR 31#5) s + 320#64) s
  | .p584, s | .p4744, s => pair 26 25 (r (.GPR 31#5) s + 304#64) s
  | .p588, s | .p4748, s => pair 28 27 (r (.GPR 31#5) s + 288#64) s
  | .p592, s | .p4752, s => pair 29 30 (r (.GPR 31#5) s + 272#64) s
  | .p596, s | .p4756, s => put 31 (r (.GPR 31#5) s + 368#64) s
  | .p600, s => w .PC (read_pc s + 9960#64) s
  | .p2052, s => pair 9 8 (r (.GPR 1#5) s + 8#64) s
  | .p2056, s => put 1 (r (.GPR 31#5) s + 144#64) s
  | .p2064, s => next (write_mem_bytes 16 (r (.GPR 31#5) s + 152#64)
      (r (.GPR 8#5) s ++ r (.GPR 9#5) s) s)
  | .p2068, s => put 8 1#64 s
  | .p2072, s => next (write_mem_bytes 8 (r (.GPR 31#5) s + 144#64) (r (.GPR 8#5) s) s)
  | .p2076, s => w .PC (read_pc s + 8484#64) (w (.GPR 30#5) (read_pc s + 4#64) s)
  | .p2080, s => w .PC (read_pc s + 2652#64) s
  | .p4760, s => w .PC (r (.GPR 30#5) s) s

theorem step (op : Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 op.row.1) : stepi s = op.effect s := by
  have fetched := code op.row (by cases op <;> decide)
  cases op
  all_goals
    simp only [Op.row] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Op.effect, pair, put, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, pc, aligned, BitVec.add_assoc]
  all_goals simp only [w, write_base_pc, write_base_gpr]

@[simp] theorem Op.program (op : Op) (s : ArmState) : (op.effect s).program = s.program := by
  cases op <;> simp [Op.effect, pair, put, next, state_simp_rules]

@[simp] theorem Op.error (op : Op) (s : ArmState) : read_err (op.effect s) = read_err s := by
  cases op <;> simp (config := {decide := true}) [Op.effect, pair, put, next, state_simp_rules]

def effect (ops : List Op) (s : ArmState) : ArmState :=
  ops.foldl (fun state op => op.effect state) s

def Follows (base : BitVec 64) : List Op → ArmState → Prop
  | [], _ => True
  | op :: ops, s => CheckSPAlignment s ∧
      read_pc s = base + BitVec.ofNat 64 op.row.1 ∧ Follows base ops (op.effect s)

theorem runs (ops : List Op) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (follows : Follows base ops s) : run ops.length s = effect ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops induction =>
    change run (ops.length + 1) s = effect ops (op.effect s)
    rw [run, step op s base code error follows.1 follows.2.1]
    exact induction _ (by simpa only [CodeAt, Op.program] using code)
      ((op.error s).trans error) follows.2.2

def listOps : List Op := [.p2052, .p2056, .p2060, .p2064, .p2068, .p2072, .p2076]
def progressiveOps : List Op :=
  [.p564, .p568, .p572, .p576, .p580, .p584, .p588, .p592, .p596, .p600]
def returnOps : List Op := [.p2080, .p4732, .p4736, .p4740, .p4744, .p4748, .p4752, .p4756, .p4760]

end Block

/-- Copied cap words retain the caller's original, possibly noncanonical Nat. -/
def listMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s + 144#64) 1#64
    (write_mem_bytes 16 (r (.GPR 31#5) s + 152#64)
      (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ++
       read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s) s)

@[irreducible] def listCalled (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + delimitedOffset)
    (w (.GPR 30#5) (base + 2080#64) (w (.GPR 8#5) 1#64
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s)
        (w (.GPR 1#5) (r (.GPR 31#5) s + 144#64)
          (w (.GPR 4#5) (r (.GPR 19#5) s) (listMemory s))))))

/-- The actual tail B uses LR restored from the old activation; no BL occurs. -/
@[irreducible] def progressiveCalled (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + delimitedOffset)
    (w (.GPR 1#5) (r (.GPR 1#5) s + 8#64)
      (w (.GPR 4#5) (r (.GPR 19#5) s) (BoolCodec.returned s)))

theorem list_entry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2052#64) : run 7 s = listCalled s base := by
  have follows : Block.Follows base Block.listOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [Block.Follows, Block.listOps, Block.Op.row,
      Block.Op.effect, Block.pair, Block.put, Block.next, state_simp_rules, aligned, pc,
      BitVec.add_assoc]
  rw [show run 7 s = Block.effect Block.listOps s from Block.runs _ s base code error follows]
  change r .PC s = _ at pc
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field <;>
      simp (config := {decide := true}) [Block.effect, Block.listOps, Block.Op.effect,
        Block.pair, Block.put, Block.next, listCalled, listMemory, delimitedOffset,
        state_simp_rules, pc, BitVec.add_assoc]
    all_goals
      simp only [Memory.write_mem_bytes_eq_mem_write_bytes, r, w, read_base_gpr,
        write_base_gpr, write_base_pc, read_store, write_store]
      rename_i reg
      by_cases h8 : reg = 8#5 <;> by_cases h9 : reg = 9#5 <;>
        by_cases h1 : reg = 1#5 <;> by_cases h4 : reg = 4#5 <;>
        simp [h8, h9, h1, h4]
  · simp [Block.effect, Block.listOps, Block.Op.effect, Block.pair, Block.put,
      Block.next, listCalled, listMemory, state_simp_rules]
  · intro bytes address
    simp (config := {decide := true}) [Block.effect, Block.listOps, Block.Op.effect,
      Block.pair, Block.put, Block.next, listCalled, listMemory,
      state_simp_rules, BitVec.add_assoc]
    simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes,
      Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem]

theorem progressive_entry_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 564#64) : run 10 s = progressiveCalled s base := by
  have afterSP : CheckSPAlignment (Block.put 31 (r (.GPR 31#5) s + 368#64) s) := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Block.put, Block.next,
      state_simp_rules, Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  have follows : Block.Follows base Block.progressiveOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [Block.Follows, Block.progressiveOps, Block.Op.row,
      Block.Op.effect, Block.pair, Block.put, Block.next, state_simp_rules,
      CheckSPAlignment, read_gpr, BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  rw [show run 10 s = Block.effect Block.progressiveOps s from Block.runs _ s base code error follows]
  change r .PC s = _ at pc
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field <;>
      simp (config := {decide := true}) [Block.effect, Block.progressiveOps, Block.Op.effect,
        Block.pair, Block.put, Block.next, progressiveCalled, BoolCodec.returned,
        delimitedOffset, state_simp_rules, pc, BitVec.add_assoc]
    all_goals
      simp only [r, w, read_base_gpr, write_base_gpr, write_base_pc, read_store, write_store]
      rename_i reg
      by_cases h1 : reg = 1#5 <;> by_cases h4 : reg = 4#5 <;> simp [h1, h4]
  · simp [Block.effect, Block.progressiveOps, Block.Op.effect, Block.pair, Block.put,
      Block.next, progressiveCalled, BoolCodec.returned, state_simp_rules]
  · intro bytes address
    simp [Block.effect, Block.progressiveOps, Block.Op.effect, Block.pair, Block.put,
      Block.next, progressiveCalled, BoolCodec.returned, state_simp_rules]

theorem return_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 2080#64) : run 9 s = BoolCodec.returned s := by
  have afterSP : CheckSPAlignment (Block.put 31 (r (.GPR 31#5) s + 368#64) s) := by
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Block.put, Block.next,
      state_simp_rules, Aligned, ← BitVec.toNat_inj, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  have follows : Block.Follows base Block.returnOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true}) [Block.Follows, Block.returnOps, Block.Op.row,
      Block.Op.effect, Block.pair, Block.put, Block.next, state_simp_rules,
      CheckSPAlignment, read_gpr, BitVec.setWidth_eq, pc, BitVec.add_assoc] at aligned afterSP ⊢
    exact ⟨aligned, afterSP⟩
  rw [show run 9 s = Block.effect Block.returnOps s from Block.runs _ s base code error follows]
  change r .PC s = _ at pc
  simp (config := {decide := true}) [Block.effect, Block.returnOps, Block.Op.effect,
    Block.pair, Block.put, Block.next, BoolCodec.returned,
    state_simp_rules, pc, BitVec.add_assoc]
  simp only [w, write_base_pc, write_base_gpr]

end SszArm.BitList
