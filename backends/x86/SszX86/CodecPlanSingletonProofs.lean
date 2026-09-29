import SszX86.CodecPlanSingletonCopy

namespace SszX86.CodecPlanSingleton
open SszX86.UintCodec

/-- Exact original-state resources for the physical destination, whenever the
checked reservation selects one. This asserts mapping and ownership, never a
future execution or initialization fact. A failed reservation needs no payload. -/
structure PayloadOwned (s : MachineData) (address capacity used : BitVec 64) : Prop where
  selected : ∀ r, SszNative.TypedArena.reserve ⟨40, 3⟩
      address.toNat capacity.toNat used.toNat 1 = some r →
    Large.Mapped s.dmem (BitVec.ofNat 64 r.pointer) 40 ∧
    Apart s.regs.rdx.toBitVec 40 (BitVec.ofNat 64 r.pointer) 40 ∧
    Apart (BitVec.ofNat 64 r.pointer) 40 s.regs.rdi.toBitVec 68 ∧
    Apart (BitVec.ofNat 64 r.pointer) 40 (s.regs.rsi.toBitVec + 16#64) 8 ∧
    Apart s.regs.rsp.toBitVec 8 (BitVec.ofNat 64 r.pointer) 40

def resultMem (s : MachineData) (w : PlanWords) (reservation : Option SszNative.Arena.Reservation) : DataMem :=
  match reservation with
  | none => errorMem s.dmem s.regs.rdi.toBitVec
  | some r =>
    successMem (copyMem
      (Mem.storeInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 (BitVec.ofNat 64 r.used).toInt)
      (BitVec.ofNat 64 r.pointer) w) s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer)

def Returned (s : MachineData) (ra : BitVec 64) (w : PlanWords)
    (reservation : Option SszNative.Arena.Reservation) (t : MachineState) : Prop :=
  t.2 = Int64.ofBitVec ra ∧ t.1.dmem = resultMem s w reservation ∧
  t.1.zmms = s.zmms ∧ t.1.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 ∧
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .rsp →
    t.1.regs.get64 r = s.regs.get64 r

private theorem result_return_load (s : MachineData) (w : PlanWords)
    (reservation : Option SszNative.Arena.Reservation) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra)))
    (out : Apart s.regs.rsp.toBitVec 8 s.regs.rdi.toBitVec 68)
    (cursor : Apart s.regs.rsp.toBitVec 8 (s.regs.rsi.toBitVec + 16#64) 8)
    (payload : ∀ r, reservation = some r → Apart s.regs.rsp.toBitVec 8 (BitVec.ofNat 64 r.pointer) 40) :
    Mem.loadInt (resultMem s w reservation) s.regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  rw [← ret]
  apply memmove_loadInt_congr
  intro i hi
  cases reservation with
  | none => exact error_frame _ _ _ (out i hi)
  | some r =>
    unfold resultMem
    rw [success_frame]
    · rw [copy_frame _ _ _ _ (payload r rfl i hi)]
      apply memmove_store_lookup_outside
      intro j hj
      exact cursor i hi j (by simpa only [Int.toBytes_length] using hj)
    · intro j hj
      exact out i hi j (by omega)
    · intro j hj
      simpa only [memmove_addr_add] using out i hi (64+j) (by omega)

/-- Complete native Plan singleton reservation and copy. Every refusal returns
ScratchExhausted(32768), leaves the arena cursor unchanged, and publishes exactly
its active error fields. Success commits before copying and preserves allocation
padding, output padding, and every byte outside the literal store footprint. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64) (w : PlanWords) (ra : BitVec 64)
    (header : Header s address capacity used)
    (input : w.At s.dmem s.regs.rdx.toBitVec)
    (outMapped : Large.Mapped s.dmem s.regs.rdi.toBitVec 68)
    (payload : PayloadOwned s address capacity used)
    (sourceCursor : Apart s.regs.rdx.toBitVec 40 (s.regs.rsi.toBitVec + 16#64) 8)
    (outCursor : Apart s.regs.rdi.toBitVec 68 (s.regs.rsi.toBitVec + 16#64) 8)
    (returnOut : Apart s.regs.rsp.toBitVec 8 s.regs.rdi.toBitVec 68)
    (returnCursor : Apart s.regs.rsp.toBitVec 8 (s.regs.rsi.toBitVec + 16#64) 8)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    Eventually (step e) (Returned s ra w (SszNative.TypedArena.reserve ⟨40, 3⟩
      address.toNat capacity.toNat used.toNat 1)) (s, base) := by
  apply eventually_trans (step e) (Reserved s base address capacity used)
    (Returned s ra w (SszNative.TypedArena.reserve ⟨40, 3⟩ address.toNat capacity.toNat used.toNat 1))
  · exact reserve_runs e base hc s address capacity used header
  · rintro ⟨t, pc⟩ ⟨frame, failure | success⟩
    · rcases failure with ⟨failedReserve, rfl⟩
      have outReg : t.regs.rdi = s.regs.rdi :=
        frame.2.2 .rdi (by decide) (by decide) (by decide) (by decide)
      have stackReg : t.regs.rsp = s.regs.rsp :=
        frame.2.2 .rsp (by decide) (by decide) (by decide) (by decide)
      apply failure_cps e base hc t
      · simpa only [frame.1, outReg] using outMapped
      intro flags
      apply (ret_cps e base hc (failed t flags) ra _ _ _).2
      · have h := result_return_load s w none ra ret returnOut returnCursor
          (by intro r h; cases h)
        simpa only [resultMem, failed, frame.1, outReg, stackReg] using h
      · refine ⟨rfl, ?_, frame.2.1, ?_, ?_⟩
        · simp only [failed, resultMem, failedReserve, frame.1, outReg]
        · simp only [failed, stackReg, UInt64.toBitVec_ofBitVec]
        · intro r h1 h2 h3 h4 h5 h6 h7
          have keep := frame.2.2 r h1 h2 h5 h6
          cases r <;> simp_all [failed, Reg64s.get64]
    · rcases success with ⟨r, reserved, pointer, cursor, rfl, flags, rfl⟩
      obtain ⟨destMapped, sourceDest, destOut, destCursor, returnDest⟩ := payload.selected r reserved
      have pword : BitVec.ofNat 64 r.pointer = address +
          BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat) := by
        rw [pointer, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have uword : BitVec.ofNat 64 r.used =
          BitVec.ofNat 64 (SszNative.Arena.start address.toNat used.toNat + 40) := by rw [cursor]
      apply commit_cps e base hc (ready s address used flags)
      · exact ⟨_, header.used_load⟩
      have sourceKeep (m : DataMem) (a : Nat) (v : Int) (ha : a + 8 ≤ 40) :
          Mem.loadInt (Mem.storeInt m (s.regs.rsi.toBitVec + 16#64) 8 v)
            (s.regs.rdx.toBitVec + BitVec.ofNat 64 a) 8 =
            Mem.loadInt m (s.regs.rdx.toBitVec + BitVec.ofNat 64 a) 8 := by
        simpa only [BitVec.ofNat_zero, BitVec.add_zero] using
          load_store_apart m s.regs.rdx.toBitVec (s.regs.rsi.toBitVec + 16#64)
            40 8 a 0 8 8 v sourceCursor ha (by decide)
      have sourceKeep0 (m : DataMem) (v : Int) :
          Mem.loadInt (Mem.storeInt m (s.regs.rsi.toBitVec + 16#64) 8 v)
            s.regs.rdx.toBitVec 8 = Mem.loadInt m s.regs.rdx.toBitVec 8 := by
        simpa using sourceKeep m 0 v (by decide)
      apply copy_cps e base hc (committed (ready s address used flags)) w
      · simpa (disch := decide) only [committed, ready, PlanWords.At,
          sourceKeep, sourceKeep0] using input
      · apply Large.mapped_store
        simpa only [ready, committed, ← pword] using destMapped
      · simpa only [ready, committed, ← pword] using sourceDest
      apply publish_cps e base hc
      · unfold copied copyMem committed ready
        repeat' first | exact outMapped | apply Large.mapped_store
      intro publishFlags
      let final := published (copied (committed (ready s address used flags)) w) publishFlags
      have memory : final.dmem = resultMem s w (some r) := by
        simp only [final, published, copied, committed, ready, resultMem, pword, uword]
      have returnLoad : Mem.loadInt final.dmem final.regs.rsp.toBitVec 8 =
          some (Int.ofBytes (wordBytes ra)) := by
        rw [memory]
        exact result_return_load s w (some r) ra ret returnOut returnCursor
          (by intro r' h; cases h; exact returnDest)
      apply (ret_cps e base hc final ra _ returnLoad _).1
      refine ⟨rfl, ?_, rfl, rfl, ?_⟩
      · simpa only [reserved] using memory
      · intro reg h1 h2 h3 h4 h5 h6 h7
        cases reg <;> simp_all [final, published, copied, committed, ready, Reg64s.get64]

end SszX86.CodecPlanSingleton
