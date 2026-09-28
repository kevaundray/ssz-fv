import SszX86.NatMulLoopFrame

namespace SszX86.NatMul.Product
open SszNative
open UintCodec

structure OuterStable (s t : MachineData) : Prop where
  rsi : t.regs.rsi = s.regs.rsi
  r12 : t.regs.r12 = s.regs.r12
  r13 : t.regs.r13 = s.regs.r13
  r14 : t.regs.r14 = s.regs.r14
  rbp : t.regs.rbp = s.regs.rbp
  rsp : t.regs.rsp = s.regs.rsp
  zmms : t.zmms = s.zmms

theorem OuterStable.trans {a b c : MachineData} (ab : OuterStable a b) (bc : OuterStable b c) :
    OuterStable a c :=
  ⟨bc.rsi.trans ab.rsi, bc.r12.trans ab.r12, bc.r13.trans ab.r13,
    bc.r14.trans ab.r14, bc.rbp.trans ab.rbp, bc.rsp.trans ab.rsp, bc.zmms.trans ab.zmms⟩

/-- Fetch, inner multiplication, checked carry store, and the actual outer backedge. -/
theorem row_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (leftPointer source dst : BitVec 64)
    (leftPhysical rightPhysical leftCount row : Nat) (right buffer : List (BitVec 64))
    (factor : BitVec 64)
    (sourceApart : Large.Disjoint source dst (8*rightPhysical) (8*(leftCount+right.length)))
    (span : dst.toNat+8*(leftCount+right.length) ≤ 2^64)
    (stackSpan : s.regs.rsp.toBitVec.toNat+24 ≤ 2^64)
    (stackApart : Body.Apart s.regs.rsp.toBitVec.toNat 24 dst.toNat (8*(leftCount+right.length)))
    (leftBound : leftPhysical < 2^64) (leftFits : leftCount ≤ leftPhysical)
    (rightFits : right.length ≤ rightPhysical) (rightPositive : 0 < right.length)
    (rowBound : row < leftCount) (bufferLength : row+buffer.length = leftCount+right.length)
    (nonzero : leftPointer ≠ 0)
    (rsi : s.regs.rsi.toBitVec = source)
    (r10 : s.regs.r10.toBitVec = dst + BitVec.ofNat 64 (8*row))
    (r12 : s.regs.r12.toBitVec = BitVec.ofNat 64 leftCount)
    (r13 : s.regs.r13.toBitVec = BitVec.ofNat 64 right.length)
    (r14 : s.regs.r14.toBitVec = BitVec.ofNat 64 (leftCount+right.length))
    (r15 : s.regs.r15.toBitVec = BitVec.ofNat 64 row)
    (locals : Locals s.dmem s.regs.rsp.toBitVec leftPointer (BitVec.ofNat 64 leftPhysical) dst)
    (factorLoad : Mem.loadInt s.dmem (leftPointer+BitVec.ofNat 64 (8*row)) 8 =
      some (factor.toNat : Int))
    (rightRead : ReadAt s.dmem source 0 right) (bufferRead : ReadAt s.dmem dst row buffer)
    (hmapped : Large.Mapped s.dmem dst (8*(leftCount+right.length)))
    (P : MachineState → Prop)
    (next : ∀ t, OuterStable s t →
      t.regs.r10.toBitVec = dst + BitVec.ofNat 64 (8*(row+1)) →
      t.regs.r15.toBitVec = BitVec.ofNat 64 (row+1) →
      t.dmem = Large.fillMem s.dmem dst row (LimbMul.row factor right buffer) →
      Eventually (step e) P (t, if row+1 = leftCount then base+664 else base+512)) :
    Eventually (step e) P (s, base+512) := by
  have physical := physical_counts dst leftCount right.length span
  apply fetch_cps e base hc s leftPointer (BitVec.ofNat 64 leftPhysical) factor nonzero
  · rw [r15]
    bv_omega
  · exact locals.left
  · exact locals.payload
  · simpa [r15, BitVec.ofNat_mul, Nat.mul_comm] using factorLoad
  intro fetchFlags
  apply initialize_cps e base hc
  intro initFlags
  let start := initializedState (fetchedState s leftPointer factor fetchFlags) initFlags
  apply inner_cps e base hc source dst (8*rightPhysical) leftCount right.length row
    sourceApart span rowBound P right.length rightPositive 0 right buffer (by omega) rfl
    (by omega) (by omega) (by omega) start factor 0 (by decide)
  · exact rsi
  · exact r10
  · rfl
  · exact r13
  · exact r14
  · exact r15
  · rfl
  · rfl
  · rfl
  · exact rightRead
  · simpa using bufferRead
  intro t stable _ tCarry _ tMemory
  have tr15 : t.regs.r15.toBitVec = BitVec.ofNat 64 row := by
    rw [stable.r15]
    exact r15
  have tr13 : t.regs.r13.toBitVec = BitVec.ofNat 64 right.length := by
    rw [stable.r13]
    exact r13
  have tr14 : t.regs.r14.toBitVec = BitVec.ofNat 64 (leftCount+right.length) := by
    rw [stable.r14]
    exact r14
  have trsp : t.regs.rsp = s.regs.rsp := stable.rsp
  have memory : t.dmem = Large.fillMem s.dmem dst row
      (LimbMul.inner right.length factor right buffer 0).1 := by simpa [start] using tMemory
  have frame : BufferFrame s.dmem t.dmem dst.toNat (8*(leftCount+right.length)) := by
    rw [memory]
    exact fill_buffer_frame _ _ _ _ _ span (by rw [LimbMul.inner_length]; omega)
  have tLocals := locals.preserve frame stackSpan stackApart
  have tMapped : Large.Mapped t.dmem dst (8*(leftCount+right.length)) := by
    rw [memory]
    exact fill_mapped _ _ _ _ _ hmapped
  apply carry_guard_cps e base hc t
  · rw [tr15, tr13, tr14]
    exact carry_guard _ _ _ physical rowBound
  intro guardFlags
  apply carry_store_cps e base hc _ dst
  · simpa [carryGuardedState, trsp] using tLocals.destination
  · have address : dst + (t.regs.r15.toBitVec + t.regs.r13.toBitVec) * 8#64 =
        dst + BitVec.ofNat 64 (8*(row+right.length)) := by
      rw [tr15, tr13]
      simp [BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm]
    simpa [carryGuardedState, address] using
      Large.mapped_load t.dmem dst (8*(leftCount+right.length)) (8*(row+right.length)) 8
        tMapped (by omega)
  apply outer_advance_cps e base hc
  intro outerFlags
  have tr11 : t.regs.r11.toBitVec = BitVec.ofNat 64 (row+1) := by
    rw [stable.r11]
    simp [start, initializedState, fetchedState, r15, BitVec.ofNat_add]
  have tr12 : t.regs.r12.toBitVec = BitVec.ofNat 64 leftCount := by
    rw [stable.r12]
    exact r12
  have endTest : (t.regs.r11 = t.regs.r12) ↔ row+1 = leftCount := by
    rw [← UInt64.toBitVec_inj, tr11, tr12]
    bv_omega
  simp only [carryStoredState, carryGuardedState] at endTest ⊢
  rw [endTest]
  apply next
  · exact ⟨stable.rsi,stable.r12,stable.r13,stable.r14,stable.rbp,stable.rsp,stable.zmms⟩
  · simp only [outerAdvancedState, UInt64.toBitVec_ofBitVec, stable.r10]
    change s.regs.r10.toBitVec + 8 = _
    rw [r10]
    bv_omega
  · exact tr11
  · rw [LimbMul.row, NatAdd.Carry.fill_append]
    simp only [LimbMul.inner_length, Large.fillMem]
    simp [outerAdvancedState, memory, tCarry, tr15, tr13, BitVec.ofNat_add,
      BitVec.ofNat_mul, Nat.mul_comm]

end SszX86.NatMul.Product
