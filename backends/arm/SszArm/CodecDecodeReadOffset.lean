import SszArm.CodecDecodeReadOffsetOps
import SszArm.CodecLinkedReadOffset
import SszArm.BoolResultMemory
import SszArm.NatCompareMemory

namespace SszArm.Codec.Decode.ReadOffset

/-- Caller-owned input is protected from the actual eight-byte LR spill. The
remaining eight bytes of the activation are not included in the write frame. -/
structure Owned (s : ArmState) : Prop where
  length : 4 ≤ (r (.GPR 1#5) s).toNat
  inputHigh : (r (.GPR 0#5) s).toNat + 4 ≤ 2 ^ 64
  stackLow : 16 ≤ (r (.GPR 31#5) s).toNat
  separated : (r (.GPR 0#5) s).toNat + 4 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat - 8 ≤ (r (.GPR 0#5) s).toNat

def path : List Op :=
  [.p0, .p4, .p8, .p12, .p16, .p20, .p24, .p28, .p32,
   .p36, .p40, .p44, .p48, .p52, .p56, .p60, .p64, .p68]

def spilled (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 30#5) s) s

def byte (s : ArmState) (offset : BitVec 64) : BitVec 64 :=
  (read_mem_bytes 1 (r (.GPR 0#5) s + offset) s).setWidth 64

def lowThree (s : ArmState) : BitVec 64 :=
  byte s 0 ||| (byte s 1 <<< 8) ||| (byte s 2 <<< 16)

def decoded (s : ArmState) : BitVec 64 := lowThree s ||| (byte s 3 <<< 24)

/-- Exact architectural result, retaining the real saved-LR store. -/
def returned (s : ArmState) : ArmState :=
  w .PC (r (.GPR 30#5) s)
    (w (.GPR 0#5) (decoded s)
      (w (.GPR 8#5) (lowThree s)
        (w (.GPR 9#5) (byte s 3)
          (w (.GPR 10#5) (byte s 2)
            (write_pstate (AddWithCarry (r (.GPR 1#5) s) (~~~3#64) 1#1).2
              (spilled s))))))

theorem code_of_linked {s : ArmState} {base : BitVec 64}
    (code : Linked.ReadOffset.CodeAt s base) : CodeAt s base := by
  intro op
  exact code op.row (by cases op <;> decide)

theorem spilled_read (s : ArmState) (owned : Owned s) (offset : Nat) (bound : offset < 4) :
    read_mem_bytes 1 (r (.GPR 0#5) s + BitVec.ofNat 64 offset) (spilled s) =
      read_mem_bytes 1 (r (.GPR 0#5) s + BitVec.ofNat 64 offset) s := by
  have low := owned.stackLow
  have high := owned.inputHigh
  have separation := owned.separated
  unfold spilled
  apply BoolCodec.read_mem_bytes_write_mem_bytes_disjoint <;> bv_omega

theorem spilled_lr (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (spilled s) = r (.GPR 30#5) s := by
  apply BoolCodec.read_mem_bytes_write_mem_bytes_same
  bv_omega

/-- The checked length excludes each of the four real bounds-panic edges. -/
theorem path_follows (s : ArmState) (base : BitVec 64)
    (length : 4 ≤ (r (.GPR 1#5) s).toNat) (pc : read_pc s = base) :
    Follows base path s := by
  have nonzero : r (.GPR 1#5) s ≠ 0#64 := by bv_omega
  have notOne : r (.GPR 1#5) s ≠ 1#64 := by bv_omega
  have notThree : r (.GPR 1#5) s ≠ 3#64 := by bv_omega
  have greaterTwo : 2 < (r (.GPR 1#5) s).toNat := by omega
  have twoHigh := (Udivti3.cmp_high (r (.GPR 1#5) s) 2#64).mpr greaterTwo
  change (AddWithCarry (r (.GPR 1#5) s) 18446744073709551613#64 1#1).2.c = 1#1 ∧
    (AddWithCarry (r (.GPR 1#5) s) 18446744073709551613#64 1#1).2.z = 0#1 at twoHigh
  have threeNot : (AddWithCarry (r (.GPR 1#5) s) 18446744073709551612#64 1#1).2.z ≠ 1#1 := by
    intro zero
    exact notThree ((Udivti3.cmp_zero (r (.GPR 1#5) s) 3#64).mp zero)
  change r .PC s = base at pc
  simp [path, Follows, Op.row, Op.effect, put, next, Udivti3.compare, Udivti3.next,
    state_simp_rules, pc, nonzero, notOne, twoHigh.1, twoHigh.2, threeNot,
    BitVec.add_assoc]

macro "read_offset_reduce" : tactic => `(tactic|
  simp (config := {decide := true})
    [*, block, path, Op.effect, put, next, Udivti3.compare, Udivti3.next,
     returned, lowThree, decoded, byte, spilled, state_simp_rules, BitVec.add_assoc,
     BitVec.sub_add_cancel, Udivti3.cmp_zero, Udivti3.cmp_high, NatCompare.read_spill_w])

theorem block_returned (s : ArmState) (base : BitVec 64) (owned : Owned s) :
    block base path s = returned s := by
  have nonzero : r (.GPR 1#5) s ≠ 0#64 := by have := owned.length; bv_omega
  have notOne : r (.GPR 1#5) s ≠ 1#64 := by have := owned.length; bv_omega
  have notThree : r (.GPR 1#5) s ≠ 3#64 := by have := owned.length; bv_omega
  have greaterTwo : 2 < (r (.GPR 1#5) s).toNat := by have := owned.length; omega
  have twoHigh := (Udivti3.cmp_high (r (.GPR 1#5) s) 2#64).mpr greaterTwo
  change (AddWithCarry (r (.GPR 1#5) s) 18446744073709551613#64 1#1).2.c = 1#1 ∧
    (AddWithCarry (r (.GPR 1#5) s) 18446744073709551613#64 1#1).2.z = 0#1 at twoHigh
  have threeNot : (AddWithCarry (r (.GPR 1#5) s) 18446744073709551612#64 1#1).2.z ≠ 1#1 := by
    intro zero
    exact notThree ((Udivti3.cmp_zero (r (.GPR 1#5) s) 3#64).mp zero)
  have load0 := spilled_read s owned 0 (by decide)
  have load1 := spilled_read s owned 1 (by decide)
  have load2 := spilled_read s owned 2 (by decide)
  have load3 := spilled_read s owned 3 (by decide)
  have link := spilled_lr s owned.stackLow
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at load0 load1 load2 load3
  simp only [spilled] at load0 load1 load2 load3 link
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases zero : reg = 0#5
      · subst reg; read_offset_reduce
      · by_cases eight : reg = 8#5
        · subst reg; read_offset_reduce
        · by_cases nine : reg = 9#5
          · subst reg; read_offset_reduce
          · by_cases ten : reg = 10#5
            · subst reg; read_offset_reduce
            · by_cases thirty : reg = 30#5
              · subst reg; read_offset_reduce
              · by_cases stack : reg = 31#5
                · subst reg; read_offset_reduce
                · simp_all [block, path, Op.effect, put, next, Udivti3.compare,
                    Udivti3.next, returned, spilled, state_simp_rules, NatCompare.read_spill_w]
    | PC => read_offset_reduce
    | SFP reg => read_offset_reduce
    | FLAG flag => cases flag <;> read_offset_reduce
    | ERR => read_offset_reduce
  · read_offset_reduce
  · intro width address
    read_offset_reduce

/-- Four little-endian byte loads return the entire unsigned offset, not a
truncated native count. This is an opaque word lemma before state instantiation. -/
theorem pack_four (a b c d : BitVec 8) :
    a.setWidth 64 ||| (b.setWidth 64 <<< 8) ||| (c.setWidth 64 <<< 16) |||
      (d.setWidth 64 <<< 24) = (d ++ (c ++ (b ++ a))).setWidth 64 := by
  rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or
      (b := d) (b' := c ++ (b ++ a)) (w'' := 64),
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or
      (b := c) (b' := b ++ a) (w'' := 64),
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or
      (b := b) (b' := a) (w'' := 64)]
  rw [BitVec.or_comm (d.setWidth 64 <<< (24 : Nat)),
    BitVec.or_comm (c.setWidth 64 <<< (16 : Nat)),
    BitVec.or_comm (b.setWidth 64 <<< (8 : Nat))]

private theorem append_nat {high low : Nat} (a : BitVec high) (b : BitVec low) :
    (a ++ b).toNat = 2 ^ low * a.toNat + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt a.toNat,
    Nat.shiftLeft_eq, Nat.mul_comm]

theorem read_four_bytes (s : ArmState) (address : BitVec 64) :
    read_mem_bytes 4 address s =
      read_mem_bytes 1 (address + 3#64) s ++
        (read_mem_bytes 1 (address + 2#64) s ++
          (read_mem_bytes 1 (address + 1#64) s ++ read_mem_bytes 1 address s)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [read_mem_bytes, BitVec.toNat_cast, append_nat, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.mul_zero, Nat.zero_add, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  omega

theorem decoded_eq_read (s : ArmState) :
    decoded s = (read_mem_bytes 4 (r (.GPR 0#5) s) s).setWidth 64 := by
  simp only [decoded, lowThree, byte, BitVec.add_zero]
  rw [pack_four, read_four_bytes]
  simp

structure Post (s t : ArmState) : Prop where
  result : r (.GPR 0#5) t = (read_mem_bytes 4 (r (.GPR 0#5) s) s).setWidth 64
  pc : read_pc t = r (.GPR 30#5) s
  error : read_err t = .None
  program : t.program = s.program
  registers : ∀ reg : BitVec 5, reg ≠ 0#5 → reg ≠ 8#5 → reg ≠ 9#5 → reg ≠ 10#5 →
    r (.GPR reg) t = r (.GPR reg) s
  simd : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : ∀ address : BitVec 64,
    (address.toNat < (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat - 8 ≤ address.toNat) → t.mem address = s.mem address

theorem returned_post (s : ArmState) (owned : Owned s) (error : read_err s = .None) :
    Post s (returned s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [returned, state_simp_rules] using decoded_eq_read s
  · simp [returned, state_simp_rules]
  · simpa [returned, spilled, state_simp_rules] using error
  · simp [returned, spilled, state_simp_rules]
  · intro reg h0 h8 h9 h10
    simp [returned, spilled, state_simp_rules, h0, h8, h9, h10]
  · intro reg
    simp [returned, spilled, state_simp_rules]
  · intro address outside
    have low := owned.stackLow
    simp only [returned, spilled, state_simp_rules]
    apply BoolCodec.write_mem_bytes_frame <;> bv_omega

/-- Original-entry ISA return theorem for the actual linked helper. No future
execution or branch-outcome hypothesis is used. -/
theorem program_correct (s : ArmState) (base : BitVec 64) (owned : Owned s)
    (code : Linked.ReadOffset.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    ∃ t, run 18 s = t ∧ Post s t := by
  refine ⟨returned s, ?_, returned_post s owned error⟩
  have execution := block_run base path s (code_of_linked code) error aligned
    (path_follows s base owned.length pc)
  exact execution.trans (block_returned s base owned)

end SszArm.Codec.Decode.ReadOffset
