import SszX86.HashCombineEntry

namespace SszX86.Hash.Combine
open SszX86.WordNormalize

theorem left_residual_store_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData)
    (mapping : Mapped s.dmem (s.regs.rsp.toBitVec + 104) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      (storeWord s 104 s.regs.r13.toBitVec, root + 239)) :
    Eventually (step e) P (s, root + 234) := by
  hash_combine_step 45 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load _ _ 8 0 8 mapping (by decide)
  word_simpa [storeWord, Effects.All] using next

def lengthAdded (s : MachineData) (length : BitVec 64) (flags : StatusFlags) : MachineData :=
  {storeWord s 112 (length + s.regs.r14.toBitVec) with status := flags}

/-- The wrapped addition occurs before the buffered-copy branch, even for an
empty right slice. No bound on the sum of the two lengths is used. -/
theorem add_right_length_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (length : BitVec 64)
    (readWord : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 112) 8 =
      some (Int.ofBytes (wordBytes length)))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (lengthAdded s length flags, root + 244)) :
    Eventually (step e) P (s, root + 239) := by
  hash_combine_step 46 using hc
  simp only [MachineData.load, readWord, SszX86.ofBytes_wordBytes, Effects.All]
  apply Delimited.store_cps
  · exact ⟨_, readWord⟩
  word_simpa [lengthAdded, storeWord, Effects.All] using next _

theorem buffer_nonempty_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.r13.toBitVec = 0 then root + 331 else root + 249)) :
    Eventually (step e) P (s, root + 244) := by
  have target := hc.targets ("hash_combine_u331", 331) (by decide)
  hash_combine_step 47 using hc
  constructor
  all_goals hash_combine_step 48 using hc
  all_goals simp only [StatusFlags.from_result, BitVec.and_self, beq_iff_eq,
    target, Effects.All]
  all_goals split <;> rename_i branch <;> word_simpa [branch] using next _

/-- CMOVB chooses the smaller of buffer capacity and the full physical length. -/
def selectedCount (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rbp := UInt64.ofNat
    (min (64 - s.regs.r13.toNat) s.regs.r14.toNat)}, status := flags}

theorem select_count_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (small : s.regs.r13.toNat < 64)
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (selectedCount s flags, root + 264)) :
    Eventually (step e) P (s, root + 249) := by
  have room : (64#64 - s.regs.r13.toBitVec).toNat = 64 - s.regs.r13.toNat := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod]
    omega
  have roomWord : 64#64 - s.regs.r13.toBitVec =
      BitVec.ofNat 64 (64 - s.regs.r13.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [room, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  hash_combine_step 49 using hc
  hash_combine_step 50 using hc
  hash_combine_step 51 using hc
  hash_combine_step 52 using hc
  simp only [StatusFlags.from_result, Udivti3.cf_sub, room, decide_eq_true_eq]
  split
  · rename_i smaller
    have selected : min (64 - s.regs.r13.toNat) s.regs.r14.toNat = s.regs.r14.toNat :=
      Nat.min_eq_right (Nat.le_of_lt smaller)
    word_simpa [selectedCount, selected] using next _
  · rename_i larger
    have selected : min (64 - s.regs.r13.toNat) s.regs.r14.toNat = 64 - s.regs.r13.toNat :=
      Nat.min_eq_left (by omega)
    word_simpa [selectedCount, selected, roomWord] using next _

def bufferCopyArgs (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with
    rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec + s.regs.r13.toBitVec + 8),
    rsi := s.regs.r15, rdx := s.regs.rbp}, status := flags}

theorem buffer_copy_args_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (bufferCopyArgs s flags, root + 278)) :
    Eventually (step e) P (s, root + 264) := by
  hash_combine_step 53 using hc
  hash_combine_step 54 using hc
  hash_combine_step 55 using hc
  hash_combine_step 56 using hc
  word_simpa [bufferCopyArgs, BitVec.mul_one, BitVec.add_assoc] using next _

def occupancyAdded (s : MachineData) (old : BitVec 64) (flags : StatusFlags) : MachineData :=
  {storeWord s 104 (old + s.regs.rbp.toBitVec) with
    regs := {s.regs with rax := UInt64.ofBitVec (old + s.regs.rbp.toBitVec)},
    status := flags}

theorem add_occupancy_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (old : BitVec 64)
    (readWord : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 104) 8 =
      some (Int.ofBytes (wordBytes old)))
    (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (occupancyAdded s old flags, root + 297)) :
    Eventually (step e) P (s, root + 284) := by
  hash_combine_step 58 using hc
  simp only [MachineData.load, readWord, SszX86.ofBytes_wordBytes, Effects.All]
  hash_combine_step 59 using hc
  hash_combine_step 60 using hc
  apply Delimited.store_cps
  · exact ⟨_, readWord⟩
  word_simpa [occupancyAdded, storeWord, Effects.All] using next _

theorem buffer_complete_test_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rax.toNat < 64 then root + 399 else root + 303)) :
    Eventually (step e) P (s, root + 297) := by
  have target := hc.targets ("hash_combine_u399", 399) (by decide)
  hash_combine_step 61 using hc
  hash_combine_step 62 using hc
  simp only [StatusFlags.from_result, Udivti3.cf_sub, target, Effects.All,
    BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq]
  split <;> rename_i branch <;> word_simpa [branch] using next _

theorem buffer_reset_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData)
    (mapping : Mapped s.dmem (s.regs.rsp.toBitVec + 104) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (storeWord s 104 0, root + 331)) :
    Eventually (step e) P (s, root + 322) := by
  hash_combine_step 68 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load _ _ 8 0 8 mapping (by decide)
  word_simpa [storeWord, Effects.All] using next

theorem right_residual_store_runs (e : Executable) (root : Int64)
    (hc : CodeAt e root) (s : MachineData)
    (mapping : Mapped s.dmem (s.regs.rsp.toBitVec + 104) 8)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (storeWord s 104 s.regs.r14.toBitVec, root + 399)) :
    Eventually (step e) P (s, root + 394) := by
  hash_combine_step 84 using hc
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using
      Large.mapped_load _ _ 8 0 8 mapping (by decide)
  word_simpa [storeWord, Effects.All] using next

end SszX86.Hash.Combine
