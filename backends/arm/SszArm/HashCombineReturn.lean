import SszArm.HashCombineOps
import SszArm.HashMemory

namespace SszArm.Hash.Combine

structure Saved (origin s : ArmState) : Prop where
  x29 : read_mem_bytes 8 (r (.GPR 31#5) s + 224#64) s = r (.GPR 29#5) origin
  x30x25 : read_mem_bytes 16 (r (.GPR 31#5) s + 240#64) s =
    r (.GPR 25#5) origin ++ r (.GPR 30#5) origin
  x24x23 : read_mem_bytes 16 (r (.GPR 31#5) s + 256#64) s =
    r (.GPR 23#5) origin ++ r (.GPR 24#5) origin
  x22x21 : read_mem_bytes 16 (r (.GPR 31#5) s + 272#64) s =
    r (.GPR 21#5) origin ++ r (.GPR 22#5) origin
  x20x19 : read_mem_bytes 16 (r (.GPR 31#5) s + 288#64) s =
    r (.GPR 19#5) origin ++ r (.GPR 20#5) origin
  x26 : r (.GPR 26#5) s = r (.GPR 26#5) origin
  x27 : r (.GPR 27#5) s = r (.GPR 27#5) origin
  x28 : r (.GPR 28#5) s = r (.GPR 28#5) origin
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) s).setWidth 64 = (r (.SFP reg) origin).setWidth 64

def epilogueOps : List Op := [.p392, .p396, .p400, .p404, .p408, .p412, .p416]

@[irreducible] def epilogue (s : ArmState) : ArmState := block epilogueOps s

theorem epilogue_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 392#64) : run 7 s = epilogue s := by
  have follows : Follows base epilogueOps s := by
    change r .PC s = _ at pc
    simp (config := {decide := true, instances := true})
      [Follows, epilogueOps, Op.row, Op.effect, restore, load, put, next,
        state_simp_rules, aligned, pc, BitVec.add_assoc]
    simp (config := {decide := true}) [CheckSPAlignment, read_gpr, Aligned,
      ← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      BitVec.zero_eq, BitVec.toNat_ofNat] at aligned ⊢
    bv_omega
  rw [epilogue]
  exact runs epilogueOps s base code error follows

@[simp] theorem epilogue_memory (s : ArmState) : (epilogue s).mem = s.mem := by
  simp [epilogue, epilogueOps, block, Op.effect, restore, load, put, next, state_simp_rules]

@[simp] theorem epilogue_program (s : ArmState) : (epilogue s).program = s.program := by
  simp only [epilogue, block_program]

@[simp] theorem epilogue_error (s : ArmState) : read_err (epilogue s) = read_err s := by
  simp only [epilogue, block_error]

private theorem loaded_pair (word : BitVec 128) (low high : BitVec 64)
    (saved : word = high ++ low) :
    word.extractLsb' 0 64 = low ∧ word.extractLsb' 64 64 = high := by
  rw [saved]
  exact ⟨BitVec.extractLsb'_append_right (n := 64) (m := 64) high low,
    BitVec.extractLsb'_append_left (n := 64) (m := 64) high low⟩

theorem epilogue_returned (origin s : ArmState) (saved : Saved origin s)
    (program : s.program = origin.program) (error : read_err s = .None)
    (sp : r (.GPR 31#5) s + 304#64 = r (.GPR 31#5) origin) :
    Returned origin (epilogue s) := by
  have pair20 := loaded_pair (read_mem_bytes 16 (r (.GPR 31#5) s + 288#64) s)
    (r (.GPR 20#5) origin) (r (.GPR 19#5) origin) saved.x20x19
  have pair22 := loaded_pair (read_mem_bytes 16 (r (.GPR 31#5) s + 272#64) s)
    (r (.GPR 22#5) origin) (r (.GPR 21#5) origin) saved.x22x21
  have pair24 := loaded_pair (read_mem_bytes 16 (r (.GPR 31#5) s + 256#64) s)
    (r (.GPR 24#5) origin) (r (.GPR 23#5) origin) saved.x24x23
  have pair30 := loaded_pair (read_mem_bytes 16 (r (.GPR 31#5) s + 240#64) s)
    (r (.GPR 30#5) origin) (r (.GPR 25#5) origin) saved.x30x25
  have registers (reg : BitVec 5) (lo : 19 ≤ reg.toNat) (hi : reg.toNat ≤ 30) :
      r (.GPR reg) (epilogue s) = r (.GPR reg) origin := by
    have cases : reg = 19#5 ∨ reg = 20#5 ∨ reg = 21#5 ∨ reg = 22#5 ∨
        reg = 23#5 ∨ reg = 24#5 ∨ reg = 25#5 ∨ reg = 26#5 ∨ reg = 27#5 ∨
        reg = 28#5 ∨ reg = 29#5 ∨ reg = 30#5 := by bv_omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [epilogue, epilogueOps, block, Op.effect, restore, load, put, next,
        state_simp_rules, saved.x29, saved.x26, saved.x27, saved.x28,
        pair20.1, pair20.2, pair22.1, pair22.2, pair24.1, pair24.2, pair30.1, pair30.2]
  refine ⟨?_, (epilogue_error s).trans error,
    (epilogue_program s).trans program, ?_, registers, ?_⟩
  · simp [epilogue, epilogueOps, block, Op.effect, restore, load, put, next,
      state_simp_rules, pair30.1]
  · simpa [epilogue, epilogueOps, block, Op.effect, restore, load, put, next,
      state_simp_rules] using sp
  · intro reg lo hi
    simpa [epilogue, epilogueOps, block, Op.effect, restore, load, put, next,
      state_simp_rules] using saved.vectors reg lo hi

theorem Saved.of_frame {origin s t : ArmState} {writes : List Delimited.Span}
    (saved : Saved origin s) (memory : Delimited.MemoryFrame writes s t)
    (physical : (r (.GPR 31#5) s).toNat + 304 ≤ 2^64)
    (owned : Delimited.Protected writes (r (.GPR 31#5) s + 224#64).toNat 80)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (registers : ∀ reg : BitVec 5, 26 ≤ reg.toNat → reg.toNat ≤ 28 →
      r (.GPR reg) t = r (.GPR reg) s)
    (vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
      (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64) :
    Saved origin t := by
  have reads (offset bytes : Nat) (lo : 224 ≤ offset) (hi : offset + bytes ≤ 304) :
      read_mem_bytes bytes (r (.GPR 31#5) t + BitVec.ofNat 64 offset) t =
        read_mem_bytes bytes (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s := by
    by_cases empty : bytes = 0
    · subst bytes
      rfl
    have positive : 0 < bytes := by omega
    have baseNat : (r (.GPR 31#5) s + 224#64).toNat =
        (r (.GPR 31#5) s).toNat + 224 := by bv_omega
    have offsetNat : (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat =
        (r (.GPR 31#5) s).toNat + offset := by bv_omega
    rw [sp]
    apply read_frame (r (.GPR 31#5) s + BitVec.ofNat 64 offset) bytes memory
    · rw [offsetNat]
      omega
    · apply protected_subspan owned
      · rw [baseNat, offsetNat]
        omega
      · rw [baseNat, offsetNat]
        omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (reads 224 8 (by decide) (by decide)).trans saved.x29
  · exact (reads 240 16 (by decide) (by decide)).trans saved.x30x25
  · exact (reads 256 16 (by decide) (by decide)).trans saved.x24x23
  · exact (reads 272 16 (by decide) (by decide)).trans saved.x22x21
  · exact (reads 288 16 (by decide) (by decide)).trans saved.x20x19
  · exact (registers 26#5 (by decide) (by decide)).trans saved.x26
  · exact (registers 27#5 (by decide) (by decide)).trans saved.x27
  · exact (registers 28#5 (by decide) (by decide)).trans saved.x28
  · intro reg lo hi
    exact (vectors reg lo hi).trans (saved.vectors reg lo hi)

end SszArm.Hash.Combine
