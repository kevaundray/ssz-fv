import SszArm.BoolBody
import SszArm.BoolActivation

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

macro "tail_frame_writes" : tactic => `(tactic|
  repeat' first
    | rw [ArmState.mem_w_eq_mem]
    | rw [write_mem_bytes_frame _ _ 16 _ _ (by bv_omega) (by bv_omega)]
    | rw [write_mem_bytes_frame _ _ 8 _ _ (by bv_omega) (by bv_omega)]
    | rw [write_mem_bytes_frame _ _ 4 _ _ (by bv_omega) (by bv_omega)]
    | rw [write_mem_bytes_frame _ _ 1 _ _ (by bv_omega) (by bv_omega)])

theorem scope_tail_frame (s : ArmState) (base a : BitVec 64) (hs : ScratchSeparated s)
    (hout : a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat)
    (hstack : a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (returned (afterJump scopeStores s base 4732)).mem a = s.mem a := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  simp (config := {decide := true, instances := true})
    [returned, afterJump, scopeStores, zeroPair, storeBlock, StoreOp.effect,
     state_simp_rules, BitVec.add_assoc]
  tail_frame_writes

theorem bad_tail_frame (s : ArmState) (base a : BitVec 64) (hs : ScratchSeparated s)
    (hout : a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat)
    (hstack : a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (badTail s base).mem a = s.mem a := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  simp (config := {decide := true, instances := true})
    [badTail, tagsStored, reasonStored, tagInitialized, returned, afterJump, badStores,
     zeroPair, storeBlock, StoreOp.effect, state_simp_rules, BitVec.add_assoc]
  tail_frame_writes

theorem success_tail_frame (s : ArmState) (base a : BitVec 64) (value : Bool)
    (hs : ScratchSeparated s)
    (hout : a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 18 ≤ a.toNat)
    (hstack : a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (successTail (if value then trueStores else falseStores) s base).mem a = s.mem a := by
  rcases hs with ⟨hsp32, hsp368, hspace, hsep⟩
  cases value <;>
    simp (config := {decide := true, instances := true})
      [successTail, returned, afterJump, trueStores, falseStores, tagStores, storeBlock,
       StoreOp.effect, state_simp_rules, BitVec.add_assoc]
  all_goals tail_frame_writes

theorem body_frame (s : ArmState) (base a : BitVec 64) (hs : ScratchSeparated s)
    (hout : a.toNat < (r (.GPR 0#5) s).toNat ∨ (r (.GPR 0#5) s).toNat + 76 ≤ a.toNat)
    (hstack : a.toNat < (r (.GPR 31#5) s).toNat - 32 ∨ (r (.GPR 31#5) s).toNat ≤ a.toNat) :
    (bodyState s base).mem a = s.mem a := by
  let l := lengthCompared s
  have hl : r (.GPR 0#5) l = r (.GPR 0#5) s ∧
      r (.GPR 31#5) l = r (.GPR 31#5) s ∧ l.mem = s.mem := by
    simp (config := {decide := true})
      [l, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules]
  by_cases hn : r (.GPR 3) s = 1#64
  · simp only [bodyState, hn, ↓reduceIte]
    let b := byteLoaded (w .PC (base + 612#64) l)
    have hb : r (.GPR 0#5) b = r (.GPR 0#5) s ∧
        r (.GPR 31#5) b = r (.GPR 31#5) s ∧ b.mem = s.mem := by
      simpa (config := {decide := true}) [b, byteLoaded, state_simp_rules] using hl
    have hout18 : a.toNat < (r (.GPR 0#5) s).toNat ∨
        (r (.GPR 0#5) s).toNat + 18 ≤ a.toNat := by omega
    by_cases hz : inputByte s = 0#8
    · simp only [hz, ↓reduceIte]
      have hf := success_tail_frame (w .PC (base + 4084#64) b) base a false
        (by simpa [ScratchSeparated, state_simp_rules, hb.1, hb.2.1] using hs)
        (by simpa [state_simp_rules, hb.1] using hout18)
        (by simpa [state_simp_rules, hb.2.1] using hstack)
      simpa [state_simp_rules, hb.2.2] using hf
    · simp only [hz, ↓reduceIte]
      let c := byteCompared (w .PC (base + 620#64) b)
      have hc : r (.GPR 0#5) c = r (.GPR 0#5) s ∧
          r (.GPR 31#5) c = r (.GPR 31#5) s ∧ c.mem = s.mem := by
        simpa (config := {decide := true}) [c, byteCompared, state_simp_rules] using hb
      by_cases ho : inputByte s = 1#8
      · simp only [ho, ↓reduceIte]
        have hf := success_tail_frame (w .PC (base + 628#64) c) base a true
          (by simpa [ScratchSeparated, state_simp_rules, hc.1, hc.2.1] using hs)
          (by simpa [state_simp_rules, hc.1] using hout18)
          (by simpa [state_simp_rules, hc.2.1] using hstack)
        simpa [state_simp_rules, hc.2.2] using hf
      · simp only [ho, ↓reduceIte]
        have hf := bad_tail_frame (w .PC (base + 4144#64) c) base a
          (by simpa [ScratchSeparated, state_simp_rules, hc.1, hc.2.1] using hs)
          (by simpa [state_simp_rules, hc.1] using hout)
          (by simpa [state_simp_rules, hc.2.1] using hstack)
        simpa [state_simp_rules, hc.2.2] using hf
  · simp only [bodyState, hn, ↓reduceIte]
    have hf := scope_tail_frame (w .PC (base + 2084#64) l) base a
      (by simpa [ScratchSeparated, state_simp_rules, hl.1, hl.2.1] using hs)
      (by simpa [state_simp_rules, hl.1] using hout)
      (by simpa [state_simp_rules, hl.2.1] using hstack)
    simpa [state_simp_rules, hl.2.2] using hf

macro "prefix_registers" : tactic => `(tactic|
  simp (config := {decide := true})
    [byteLoaded, byteCompared, lengthCompared, Udivti3.compare, Udivti3.next, state_simp_rules])

theorem body_exit (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (bodyState s base) = r (.GPR 31#5) s + 368#64 ∧
    read_pc (bodyState s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) (bodyState s base) := by
  by_cases hn : r (.GPR 3) s = 1#64
  · simp only [bodyState, hn, ↓reduceIte]
    by_cases hz : inputByte s = 0#8
    · simp only [hz, ↓reduceIte]
      constructor
      · rw [successTail_sp _ _ _ (by decide)]
        prefix_registers
      · rw [successTail_pc _ _ _ (by decide)]
        prefix_registers
    · simp only [hz, ↓reduceIte]
      by_cases ho : inputByte s = 1#8
      · simp only [ho, ↓reduceIte]
        constructor
        · rw [successTail_sp _ _ _ (by decide)]
          prefix_registers
        · rw [successTail_pc _ _ _ (by decide)]
          prefix_registers
      · simp only [ho, ↓reduceIte]
        constructor
        · rw [badTail_sp]
          prefix_registers
        · rw [badTail_pc]
          prefix_registers
  · simp only [bodyState, hn, ↓reduceIte]
    constructor
    · rw [returned_sp, afterJump_sp _ _ _ _ (by decide)]
      prefix_registers
    · rw [returned_pc_read, afterJump_sp _ _ _ _ (by decide)]
      prefix_registers

theorem body_return_pc (s : ArmState) (base : BitVec 64) (hs : ScratchSeparated s)
    (hout : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat + 272 ∨
      (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat) :
    read_pc (bodyState s base) = read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) s := by
  rw [(body_exit s base).2]
  exact activation_word s (bodyState s base) 8
    (activation_of_frame s (bodyState s base) hs hout (fun a ha hb => body_frame s base a hs ha hb))
    (by decide)

theorem body_register_read (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (offset : Nat) (hr : (reg, offset) ∈ savedRegisters) :
    r (.GPR reg) (bodyState s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) (bodyState s base) := by
  by_cases hn : r (.GPR 3) s = 1#64
  · simp only [bodyState, hn, ↓reduceIte]
    by_cases hz : inputByte s = 0#8
    · simp only [hz, ↓reduceIte]
      rw [successTail_register _ _ _ (by decide) reg offset hr]
      prefix_registers
    · simp only [hz, ↓reduceIte]
      by_cases ho : inputByte s = 1#8
      · simp only [ho, ↓reduceIte]
        rw [successTail_register _ _ _ (by decide) reg offset hr]
        prefix_registers
      · simp only [ho, ↓reduceIte]
        rw [badTail_register _ _ reg offset hr]
        prefix_registers
  · simp only [bodyState, hn, ↓reduceIte]
    rw [returned_register _ reg offset hr, afterJump_sp _ _ _ _ (by decide)]
    prefix_registers

theorem body_register (s : ArmState) (base : BitVec 64) (hs : ScratchSeparated s)
    (hout : (r (.GPR 0#5) s).toNat + 80 ≤ (r (.GPR 31#5) s).toNat + 272 ∨
      (r (.GPR 31#5) s).toNat + 368 ≤ (r (.GPR 0#5) s).toNat)
    (reg : BitVec 5) (offset : Nat) (hr : (reg, offset) ∈ savedRegisters) :
    r (.GPR reg) (bodyState s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s := by
  rw [body_register_read s base reg offset hr]
  have hb := savedRegister_bounds reg offset hr
  have hw := activation_word s (bodyState s base) (offset - 272)
    (activation_of_frame s (bodyState s base) hs hout (fun a ha hb => body_frame s base a hs ha hb))
    (by omega)
  simpa [Nat.add_sub_of_le hb.1] using hw

end SszArm.BoolCodec
