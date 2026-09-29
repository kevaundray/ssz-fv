import SszArm.HashCombineBuffered
import SszArm.HashCombineRightGuard

namespace SszArm.Hash.Combine

open Delimited (MemoryFrame)

def fillCount (value : StreamState) (right : ByteArray) : Nat :=
  min (64 - value.buffered.val) right.size

theorem fillCount_bufferBound (value : StreamState) (right : ByteArray) :
    value.buffered.val + fillCount value right ≤ 64 := by
  have bound := value.buffered.isLt
  have count := Nat.min_le_left (64 - value.buffered.val) right.size
  unfold fillCount
  omega

theorem fillCount_inputBound (value : StreamState) (right : ByteArray) :
    fillCount value right ≤ right.size := Nat.min_le_right _ _

def fillBuffer (value : StreamState) (right : ByteArray) : Vector UInt8 64 :=
  SszNative.HashStream.copy value.buffer value.buffered.val right 0 (fillCount value right)
    (fillCount_bufferBound value right) (by simpa using fillCount_inputBound value right)

def fillLength (value : StreamState) (right : ByteArray) : UInt64 :=
  value.byteLen + UInt64.ofNat right.size

structure FilledPost (origin t : ArmState) (base : BitVec 64)
    (value : StreamState) (right : ByteArray) : Prop where
  activation : Activation origin t
  pc : read_pc t = if value.buffered.val + fillCount value right < 64 then base + 364#64 else base + 248#64
  rightLength : (r (.GPR 20#5) t).toNat = right.size
  rightPointer : r (.GPR 21#5) t = r (.GPR 3#5) origin
  count : (r (.GPR 23#5) t).toNat = fillCount value right
  buffer : BytesAt t (r (.GPR 31#5) t) ⟨(fillBuffer value right).toArray⟩
  chaining : ChainingAt t (r (.GPR 31#5) t + 64#64) value.chaining
  buffered : read_mem_bytes 8 (r (.GPR 31#5) t + 96#64) t =
    BitVec.ofNat 64 (value.buffered.val + fillCount value right)
  byteLen : read_mem_bytes 8 (r (.GPR 31#5) t + 104#64) t = (fillLength value right).toBitVec

@[simp] theorem fillSetup_register (s : ArmState) (reg : BitVec 5)
    (different : reg ∉ [0#5, 1#5, 2#5, 8#5, 23#5]) :
    r (.GPR reg) (fillSetup s) = r (.GPR reg) s := by
  have h0 : reg ≠ 0#5 := by simp_all
  have h1 : reg ≠ 1#5 := by simp_all
  have h2 : reg ≠ 2#5 := by simp_all
  have h8 : reg ≠ 8#5 := by simp_all
  have h23 : reg ≠ 23#5 := by simp_all
  simp [fillSetup, fillSetupOps, block, Op.effect, put, next, compare,
    state_simp_rules, h0, h1, h2, h8, h23]

theorem fillSetup_local (s : ArmState) (error : read_err s = .None) : LocalPost s (fillSetup s) := by
  refine ⟨(fillSetup_error s).trans error, fillSetup_program s,
    fillSetup_register s 31#5 (by decide), fillSetup_register s 19#5 (by decide),
    fillSetup_register s 24#5 (by decide), ?_, ?_, ?_⟩
  · intro reg lo hi
    exact fillSetup_register s reg (by simp only [List.mem_cons, List.mem_singleton]; bv_omega)
  · intro reg lo hi
    simp [fillSetup, fillSetupOps, block, Op.effect, put, next, compare, state_simp_rules]
  · intro address outside
    exact congrFun (fillSetup_memory s) address

@[simp] theorem fillResult_register (s : ArmState) (reg : BitVec 5) (different : reg ≠ 8#5) :
    r (.GPR reg) (fillResult s) = r (.GPR reg) s := by
  simp [fillResult, fillResultOps, block, Op.effect, put, load, store, next, compare,
    branch, state_simp_rules, different]

theorem fillResult_memory (s : ArmState) : (fillResult s).mem =
    (write_mem_bytes 8 (r (.GPR 31#5) s + 96#64)
      (read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) s + r (.GPR 23#5) s) s).mem := by
  simp [fillResult, fillResultOps, block, Op.effect, put, load, store, next,
    compare, branch, state_simp_rules]

theorem fillResult_frame (s : ArmState) (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    MemoryFrame [((r (.GPR 31#5) s + 96#64).toNat, 8)] s (fillResult s) := by
  intro address outside
  rw [fillResult_memory]
  apply BoolCodec.write_mem_bytes_frame _ _ _ _ address
  · bv_omega
  · exact outside _ (by simp)

theorem fillResult_local (s : ArmState) (error : read_err s = .None)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) : LocalPost s (fillResult s) := by
  refine ⟨?_, ?_, fillResult_register s 31#5 (by decide), fillResult_register s 19#5 (by decide),
    fillResult_register s 24#5 (by decide), ?_, ?_, ?_⟩
  · simpa only [fillResult, block_error] using error
  · simp only [fillResult, block_program]
  · intro reg lo hi
    exact fillResult_register s reg (by bv_omega)
  · intro reg lo hi
    simp [fillResult, fillResultOps, block, Op.effect, put, load, store, next,
      compare, branch, state_simp_rules]
  · apply frame_mono (fillResult_frame s physical)
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨((r (.GPR 31#5) s).toNat, 224), by simp [bodyWrites], ?_, ?_⟩ <;> bv_omega

/-- The first right-slice bytes are copied into the occupied buffer, then the
actual occupancy update and branch distinguish short completion from a full block. -/
theorem fill_correct (origin s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (value : StreamState) (code : CodeAt origin base) (data : DataAt origin base)
    (owned : CombineOwned origin base left right) (activation : Activation origin s)
    (pc : read_pc s = base + 196#64)
    (state : StateAt s (r (.GPR 31#5) s) { value with byteLen := fillLength value right })
    (rightLength : (r (.GPR 20#5) s).toNat = right.size)
    (rightPointer : r (.GPR 21#5) s = r (.GPR 3#5) origin)
    (buffered : (r (.GPR 22#5) s).toNat = value.buffered.val)
    (bufferPointer : r (.GPR 25#5) s = r (.GPR 31#5) s) :
    ∃ fuel, FilledPost origin (run fuel s) base value right := by
  let a := fillSetup s
  have setupPost := fillSetup_local s activation.error
  have aActivation := activation.after owned.stackLow setupPost
  have geometry := activation.physical owned.stackLow
  have arguments := fillSetup_arguments s
  have aSP : r (.GPR 31#5) a = r (.GPR 31#5) s := setupPost.sp
  have bufferWord : r (.GPR 22#5) s = BitVec.ofNat 64 value.buffered.val := by
    have small := value.buffered.isLt
    bv_omega
  have destination : r (.GPR 0#5) a = r (.GPR 31#5) s + BitVec.ofNat 64 value.buffered.val := by
    rw [arguments.1, bufferPointer, bufferWord]
  have source : r (.GPR 1#5) a = r (.GPR 3#5) origin := arguments.2.1.trans rightPointer
  have taken : (r (.GPR 23#5) a).toNat = fillCount value right := by
    simpa only [buffered, rightLength, fillCount] using fillSetup_count s
      (by rw [buffered]; exact value.buffered.isLt)
  have aLength : (r (.GPR 2#5) a).toNat = fillCount value right := by
    rw [arguments.2.2]
    exact taken
  have bufferBound := fillCount_bufferBound value right
  have inputBound := fillCount_inputBound value right
  have aPC : read_pc a = base + 224#64 := by
    change r .PC s = _ at pc
    simp [a, fillSetup, fillSetupOps, block, Op.effect, put, next, compare,
      state_simp_rules, pc, BitVec.add_assoc]
  have dstBound : (r (.GPR 0#5) a).toNat + fillCount value right ≤ 2^64 := by
    rw [destination]
    bv_omega
  have srcBound : (r (.GPR 1#5) a).toNat + fillCount value right ≤ 2^64 := by
    rw [source]
    have physical := owned.rightBound
    omega
  have apart := protected_writes_mono owned.rightOwned
    (activation.bufferContained owned.stackLow 64 (by decide))
  have separate : Memcpy.Disjoint (r (.GPR 0#5) a) (r (.GPR 1#5) a) (fillCount value right) := by
    rw [destination, source]
    rcases apart with empty | separate
    · have zero : fillCount value right = 0 := by omega
      simp only [zero, Memcpy.Disjoint, Nat.add_zero]
      omega
    · have separation := separate ((r (.GPR 31#5) s).toNat, 64) (by simp)
      unfold Memcpy.Disjoint
      bv_omega
  have copied := copy_correct .rightFill a base (aActivation.code code) aPC
    aActivation.error aActivation.aligned
    (by simpa only [aLength] using dstBound) (by simpa only [aLength] using srcBound)
    (by simpa only [aLength] using separate)
  simp only [aLength] at copied
  let copyFuel := Memcpy.fuel (fillCount value right) + 1
  let u := run copyFuel a
  have copyLocal : LocalPost a u := by
    refine ⟨copied.error, copied.program, copied.registers 31#5 (by decide),
      copied.registers 19#5 (by decide), copied.registers 24#5 (by decide), ?_, ?_, ?_⟩
    · intro reg lo hi
      exact copied.registers reg (by simp only [List.mem_cons, List.mem_singleton]; bv_omega)
    · intro reg lo hi
      rw [copied.vectors reg (by bv_omega)]
    · apply frame_mono copied.frame
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      refine ⟨((r (.GPR 31#5) a).toNat, 224), by simp [bodyWrites], ?_, ?_⟩
      all_goals simp only [aSP, destination, aLength]; bv_omega
  have uActivation := aActivation.after owned.stackLow copyLocal
  have uSP : r (.GPR 31#5) u = r (.GPR 31#5) s := copyLocal.sp.trans aSP
  have sourceA : BytesAt a (r (.GPR 3#5) origin) right :=
    bytesAt_frame aActivation.frame owned.rightBound owned.rightOwned owned.right
  have stateA : StateAt a (r (.GPR 31#5) s) { value with byteLen := fillLength value right } :=
    stateAt_mem_eq (fillSetup_memory s) state
  have uBuffer : BytesAt u (r (.GPR 31#5) s) ⟨(fillBuffer value right).toArray⟩ := by
    exact copied.buffer (r (.GPR 31#5) s) (r (.GPR 3#5) origin) value.buffer right
      value.buffered.val 0 (fillCount value right) bufferBound (by omega) (by omega)
      owned.rightBound stateA.buffer sourceA destination (by simpa using source) aLength
  have copyProtected (offset bytes : Nat) (lo : 64 ≤ offset) (hi : offset + bytes ≤ 112) :
      Delimited.Protected [((r (.GPR 0#5) a).toNat, (r (.GPR 2#5) a).toNat)]
        (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat bytes := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    rw [destination, aLength]
    bv_omega
  have uWords : ChainingAt u (r (.GPR 31#5) s + 64#64) value.chaining :=
    stateA.chaining.frame copied.frame (by bv_omega) (copyProtected 64 32 (by decide) (by decide))
  have uBuffered : read_mem_bytes 8 (r (.GPR 31#5) s + 96#64) u = BitVec.ofNat 64 value.buffered.val := by
    rw [read_frame _ 8 copied.frame (by bv_omega) (copyProtected 96 8 (by decide) (by decide))]
    exact stateA.buffered
  have uLength : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) u = (fillLength value right).toBitVec := by
    rw [read_frame _ 8 copied.frame (by bv_omega) (copyProtected 104 8 (by decide) (by decide))]
    exact stateA.byteLen
  have uTaken : (r (.GPR 23#5) u).toNat = fillCount value right := by
    rw [copied.registers 23#5 (by decide)]
    exact taken
  have uPC : read_pc u = base + 228#64 := by rw [copied.pc, aPC]; rfl
  have uGeometry := uActivation.physical owned.stackLow
  let t := fillResult u
  have resultLocal := fillResult_local u uActivation.error (by omega)
  have tActivation := uActivation.after owned.stackLow resultLocal
  have resultFrame := fillResult_frame u (by omega)
  have total : read_mem_bytes 8 (r (.GPR 31#5) u + 96#64) u + r (.GPR 23#5) u =
      BitVec.ofNat 64 (value.buffered.val + fillCount value right) := by
    rw [uSP, uBuffered]
    have small := value.buffered.isLt
    bv_omega
  have resultProtected (offset bytes : Nat) (hi : offset + bytes ≤ 96 ∨ 104 ≤ offset)
      (bound : offset + bytes ≤ 112) :
      Delimited.Protected [((r (.GPR 31#5) u + 96#64).toNat, 8)]
        (r (.GPR 31#5) s + BitVec.ofNat 64 offset).toNat bytes := by
    right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rw [uSP]
    bv_omega
  have tBuffer : BytesAt t (r (.GPR 31#5) s) ⟨(fillBuffer value right).toArray⟩ := by
    apply bytesAt_frame resultFrame _ _ uBuffer
    · rw [Hash.vectorByteArray_size]; omega
    · simpa only [Hash.vectorByteArray_size, BitVec.ofNat_zero, BitVec.add_zero] using
        resultProtected 0 64 (by left; decide) (by decide)
  have tWords := uWords.frame resultFrame (by bv_omega) (resultProtected 64 32 (by left; decide) (by decide))
  have tLength : read_mem_bytes 8 (r (.GPR 31#5) s + 104#64) t = (fillLength value right).toBitVec := by
    rw [read_frame _ 8 resultFrame (by bv_omega) (resultProtected 104 8 (by right; decide) (by decide))]
    exact uLength
  have tBuffered : read_mem_bytes 8 (r (.GPR 31#5) t + 96#64) t =
      BitVec.ofNat 64 (value.buffered.val + fillCount value right) := by
    rw [resultLocal.sp, (Memory.mem_eq_iff_read_mem_bytes_eq.mp (fillResult_memory u)) 8]
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ _ _ _ (by bv_omega)]
    exact total
  have result : FilledPost origin t base value right := by
    refine ⟨tActivation, ?_, ?_, ?_, ?_, ?_, ?_, tBuffered, ?_⟩
    · rw [fillResult_pc u base uPC, total]
      have small : value.buffered.val + fillCount value right < 2^64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    · rw [fillResult_register u 20#5 (by decide), copied.registers 20#5 (by decide),
        fillSetup_register s 20#5 (by decide)]
      exact rightLength
    · rw [fillResult_register u 21#5 (by decide), copied.registers 21#5 (by decide),
        fillSetup_register s 21#5 (by decide)]
      exact rightPointer
    · rw [fillResult_register u 23#5 (by decide)]
      exact uTaken
    · simpa only [resultLocal.sp, uSP] using tBuffer
    · simpa only [resultLocal.sp, uSP] using tWords
    · simpa only [resultLocal.sp, uSP] using tLength
  refine ⟨7 + copyFuel + 5, ?_⟩
  rw [run_plus, run_plus, fillSetup_run s base (activation.code code) activation.error activation.aligned pc,
    fillResult_run u base (uActivation.code code) uActivation.error uActivation.aligned uPC]
  exact result

end SszArm.Hash.Combine
