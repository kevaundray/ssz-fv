import SszArm.IndicesLinkedPrefixEqual
import SszArm.DelimitedMemory

namespace SszArm.Indices.PrefixEqual.Return

/-- Distinct real return sites; the Boolean is set before restoring the pair. -/
inductive Site where
  | equalFirst | unequal | equalSecond | equalThird | equalLast
  deriving DecidableEq

def Site.offset : Site → Nat
  | .equalFirst => 620
  | .unequal => 632
  | .equalSecond => 1336
  | .equalThird => 1524
  | .equalLast => 1552

def Site.value : Site → Bool
  | .unequal => false
  | _ => true

def Site.word : Site → BitVec 32
  | .unequal => 0x2a1f03e0#32
  | _ => 0x52800020#32

def next (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s

def result (site : Site) (s : ArmState) : ArmState :=
  w (.GPR 0#5) (if site.value then 1#64 else 0#64) (next s)

/-- LDP X20,X19,[SP],#16, including its real post-index writeback. -/
def restore (s : ArmState) : ArmState :=
  w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
    (w (.GPR 19#5) (read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s)
      (w (.GPR 20#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) (next s)))

def ret (s : ArmState) : ArmState := w .PC (r (.GPR 30#5) s) s

def finish (site : Site) (s : ArmState) : ArmState := ret (restore (result site s))

theorem result_step (site : Site) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    stepi s = result site s := by
  have fetched := code (site.offset, site.word) (by cases site <;> decide)
  cases site
  all_goals
    simp only [Site.offset, Site.word] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [result, Site.value, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

theorem restore_step (site : Site) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.offset + 4)) :
    stepi s = restore s := by
  have fetched := code (site.offset + 4, 0xa8c14ff4#32) (by cases site <;> decide)
  cases site
  all_goals
    simp only [Site.offset, Nat.reduceAdd] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [restore, next, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
        aligned, BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc]
  all_goals first | rfl | exact w_of_w_commute (by decide)

theorem ret_step (site : Site) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 (site.offset + 8)) :
    stepi s = ret s := by
  have fetched := code (site.offset + 8, 0xd65f03c0#32) (by cases site <;> decide)
  cases site
  all_goals
    simp only [Site.offset, Nat.reduceAdd] at pc fetched
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ error pc
      (fetch_inst_from_program.trans fetched) rfl]
    simp (config := {decide := true, instances := true})
      [ret, exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

/-- A three-instruction internal tail, with no assumed future run. -/
theorem finish_run (site : Site) (s : ArmState) (base : BitVec 64)
    (code : Linked.PrefixEqual.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.offset) :
    run 3 s = finish site s := by
  have resultCode : Linked.PrefixEqual.CodeAt (result site s) base := by
    simpa only [Linked.PrefixEqual.CodeAt, Codec.Linked.WordsAt,
      result, next, state_simp_rules] using code
  have resultError : read_err (result site s) = .None := by
    simpa [result, next, state_simp_rules] using error
  have resultAligned : CheckSPAlignment (result site s) := by
    simpa [result, next, CheckSPAlignment, state_simp_rules] using aligned
  have resultPC : read_pc (result site s) = base + BitVec.ofNat 64 (site.offset + 4) := by
    simp [result, next, state_simp_rules, pc, BitVec.ofNat_add, BitVec.add_assoc]
  have restoreCode : Linked.PrefixEqual.CodeAt (restore (result site s)) base := by
    simpa only [Linked.PrefixEqual.CodeAt, Codec.Linked.WordsAt,
      restore, result, next, state_simp_rules] using code
  have restoreError : read_err (restore (result site s)) = .None := by
    simpa [restore, result, next, state_simp_rules] using error
  have restorePC : read_pc (restore (result site s)) =
      base + BitVec.ofNat 64 (site.offset + 8) := by
    simp [restore, result, next, state_simp_rules, pc, BitVec.ofNat_add, BitVec.add_assoc]
  change run 2 (stepi s) = _
  rw [result_step site s base code error pc]
  change run 1 (stepi (result site s)) = _
  rw [restore_step site _ base resultCode resultError resultAligned resultPC]
  change stepi (restore (result site s)) = _
  exact ret_step site _ base restoreCode restoreError restorePC

/-- The current save-slot observations suffice for the tail's AAPCS frame.
These are internal cut facts, not assumptions on the original entry root. -/
structure Saved (original current : ArmState) : Prop where
  sp : r (.GPR 31#5) current + 16#64 = r (.GPR 31#5) original
  x20 : read_mem_bytes 8 (r (.GPR 31#5) current) current = r (.GPR 20#5) original
  x19 : read_mem_bytes 8 (r (.GPR 31#5) current + 8#64) current = r (.GPR 19#5) original
  registers : ∀ reg : BitVec 5, 21 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) current = r (.GPR reg) original
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) current).setWidth 64 = (r (.SFP reg) original).setWidth 64

theorem finish_returned (site : Site) (original s : ArmState)
    (saved : Saved original s) (error : read_err s = .None) :
    Delimited.Returned original (finish site s) := by
  constructor
  · simpa [finish, ret, restore, result, next, state_simp_rules] using
      saved.registers 30#5 (by decide) (by decide)
  · simpa [finish, ret, restore, result, next, state_simp_rules] using error
  · simpa [finish, ret, restore, result, next, state_simp_rules] using saved.sp
  · intro reg lower upper
    by_cases r19 : reg = 19#5
    · subst reg
      simpa [finish, ret, restore, result, next, state_simp_rules] using saved.x19
    · by_cases r20 : reg = 20#5
      · subst reg
        simpa [finish, ret, restore, result, next, state_simp_rules] using saved.x20
      · have notZero : reg ≠ 0#5 := by intro h; subst reg; simp at lower
        have notSP : reg ≠ 31#5 := by intro h; subst reg; simp at upper
        have larger : 21 ≤ reg.toNat := by
          have n19 : reg.toNat ≠ 19 := by
            intro h; apply r19; apply BitVec.eq_of_toNat_eq; exact h
          have n20 : reg.toNat ≠ 20 := by
            intro h; apply r20; apply BitVec.eq_of_toNat_eq; exact h
          omega
        simpa [finish, ret, restore, result, next, state_simp_rules,
          r19, r20, notZero, notSP] using saved.registers reg larger upper
  · intro reg lower upper
    simpa [finish, ret, restore, result, next, state_simp_rules] using
      saved.vectors reg lower upper

theorem finish_value (site : Site) (s : ArmState) :
    r (.GPR 0#5) (finish site s) = if site.value then 1#64 else 0#64 := by
  simp [finish, ret, restore, result, next, state_simp_rules]

theorem finish_memory (site : Site) (s : ArmState) :
    (finish site s).mem = s.mem := by
  simp [finish, ret, restore, result, next, state_simp_rules]

end SszArm.Indices.PrefixEqual.Return
