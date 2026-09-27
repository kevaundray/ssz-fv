import SszArm.UintResultMemory

namespace SszArm.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def failurePrepared (s : ArmState) : ArmState := block (failureOps.map Prod.snd) s

def failureReady (s : ArmState) : ArmState :=
  block (failureReturnOps.map Prod.snd) (Memcpy.result (failurePrepared s))

/-- Exact memory image of the pre-call stores, including the SIMD-local zeros
at SP+144..191 and their real load/store transfer to SP+64..111. -/
def failureMemory (s : ArmState) : ArmState :=
  let sp := r (.GPR 31#5) s
  let out := r (.GPR 0#5) s
  let t := write_mem_bytes 8 (sp - 16#64) (r (.GPR 9#5) s) s
  let t := write_mem_bytes 8 (sp - 16#64 + 8#64) (r (.GPR 10#5) s) t
  let t := write_mem_bytes 8 (out + 8#64) 1#64 t
  let t := write_mem_bytes 8 (out + 16#64) 0#64 t
  let t := write_mem_bytes 32 (sp + 144#64) 0#256 t
  let t := write_mem_bytes 16 (sp + 176#64) 0#128 t
  let t := write_mem_bytes 32 (sp + 64#64) 0#256 t
  write_mem_bytes 16 (sp + 96#64) 0#128 t

def failureResultMemory (s : ArmState) : ArmState :=
  let out := r (.GPR 0#5) s
  let t := write_mem_bytes 48 (out + 24#64) 0#384 (failureMemory s)
  let t := write_mem_bytes 8 out 1#64 t
  write_mem_bytes 4 (out + 72#64) 32768#32 t

macro "failure_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [failurePrepared, failureOps, failureReturnOps, block, List.map_cons, List.map_nil,
     Prod.snd, Op.effect, next, put, StoreOp.effect, state_simp_rules,
     ArmState.mem_w_eq_mem, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd,
     BitVec.sub_add_cancel, BitVec.add_sub_cancel, BitVec.add_assoc])

macro "failure_return_expand" : tactic => `(tactic|
  simp (config := {decide := true, instances := true}) only
    [failureReady, failureReturnOps, block, List.map_cons, List.map_nil,
     Prod.snd, Op.effect, next, put, state_simp_rules,
     ArmState.mem_w_eq_mem, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add,
     BitVec.ofNat_add_ofNat, Nat.reduceAdd, BitVec.add_assoc])

theorem failure_prepared_memory (s : ArmState) (hs : Separated s) :
    (failurePrepared s).mem = (failureMemory s).mem := by
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  failure_expand
  tail_reads
  simp only [failureMemory]
  repeat' first
    | apply mem_write_mem_bytes_of_mem_eq
    | rw [ArmState.mem_w_eq_mem]
  try rfl

theorem failure_prepared_registers (s : ArmState) :
    r (.GPR 0#5) (failurePrepared s) = r (.GPR 0#5) s + 24#64 ∧
    r (.GPR 1#5) (failurePrepared s) = r (.GPR 31#5) s + 64#64 ∧
    r (.GPR 2#5) (failurePrepared s) = 48#64 ∧
    r (.GPR 19#5) (failurePrepared s) = 1#64 ∧
    r (.GPR 20#5) (failurePrepared s) = r (.GPR 0#5) s ∧
    r (.GPR 31#5) (failurePrepared s) = r (.GPR 31#5) s ∧
    r (.GPR 30#5) (failurePrepared s) = read_pc s + 96#64 ∧
    read_pc (failurePrepared s) = read_pc s + 99424#64 := by
  failure_expand
  try simp [BitVec.add_assoc]

/-- A zero store gives zero bytes on its actual, nonwrapping written interval. -/
@[simp] theorem write_zero_inside (s : ArmState) (n : Nat) (address a : BitVec 64)
    (value : BitVec (n * 8)) (hzero : value = 0#(n * 8))
    (hspace : address.toNat + n ≤ 2^64)
    (hlo : address.toNat ≤ a.toNat) (hhi : a.toNat < address.toNat + n) :
    (write_mem_bytes n address value s).mem a = 0#8 := by
  subst value
  rw [Memory.write_mem_bytes_eq_mem_write_bytes]
  change s.mem.write_bytes n address (0#(n * 8)) a = _
  rw [Memory.write_bytes_eq_extractLsByte hlo hhi hspace]
  exact BitVec.extractLsByte_zero

theorem read_zero_of_bytes (s : ArmState) (n : Nat) (address : BitVec 64)
    (hz : ∀ i < n, read_mem (address + BitVec.ofNat 64 i) s = 0#8) :
    read_mem_bytes n address s = 0#(n * 8) := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih =>
    have h0 := hz 0 (by omega)
    have ht : read_mem_bytes n (address + 1#64) s = 0#(n * 8) := by
      apply ih
      intro i hi
      have haddr : address + BitVec.ofNat 64 (i + 1) =
          address + 1#64 + BitVec.ofNat 64 i := by bv_omega
      simpa only [haddr] using hz (i + 1) (by omega)
    simp [read_mem_bytes, ht, show read_mem address s = 0#8 by simpa using h0]

@[simp] theorem read_zero_inside (s : ArmState) (n k : Nat) (address a : BitVec 64)
    (value : BitVec (n * 8)) (hzero : value = 0#(n * 8))
    (hspace : address.toNat + n ≤ 2^64)
    (hlo : address.toNat ≤ a.toNat) (hhi : a.toNat + k ≤ address.toNat + n) :
    read_mem_bytes k a (write_mem_bytes n address value s) = 0#(k * 8) := by
  apply read_zero_of_bytes
  intro i hi
  change (write_mem_bytes n address value s).mem (a + BitVec.ofNat 64 i) = _
  apply write_zero_inside
  · exact hzero
  all_goals bv_omega

/-- This is proved from the SIMD stores, never assumed of the incoming state. -/
def SourceZero48 (s : ArmState) : Prop :=
  ∀ i < 48, read_mem (r (.GPR 1#5) s + BitVec.ofNat 64 i) s = 0#8

theorem source_zero48 (s : ArmState) (hs : Separated s) :
    SourceZero48 (failurePrepared s) := by
  have hm := failure_prepared_memory s hs
  have hr := (failure_prepared_registers s).2.1
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  intro i hi
  rw [hr]
  change (failurePrepared s).mem _ = _
  rw [hm]
  by_cases h32 : i < 32
  · simp (disch := first | rfl | tail_side)
      [failureMemory, write_mem_bytes_frame, write_zero_inside]
  · simp (disch := first | rfl | tail_side)
      [failureMemory, write_zero_inside]

/-- The linked memcpy theorem is used at its real call interface. The source and
destination are disjoint and nonwrapping; the saved LR remains a real register. -/
theorem memcpy_zero_memory (s : ArmState)
    (hn : r (.GPR 2#5) s = 48#64) (hz : SourceZero48 s)
    (hd : (r (.GPR 0#5) s).toNat + 48 ≤ 2^64)
    (hs : (r (.GPR 1#5) s).toNat + 48 ≤ 2^64)
    (hsep : Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) 48) :
    (Memcpy.result s).mem = (write_mem_bytes 48 (r (.GPR 0#5) s) 0#384 s).mem := by
  funext a
  have hn' : r (.GPR 2) s = 48#64 := hn
  have hm := Memcpy.result_memory s
    (by
      change (r (.GPR 0#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64
      rw [hn]
      exact hd)
    (by
      change (r (.GPR 1#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64
      rw [hn]
      exact hs)
    (by
      change Memcpy.Disjoint (r (.GPR 0#5) s) (r (.GPR 1#5) s) (r (.GPR 2#5) s).toNat
      rw [hn]
      exact hsep) a
  rw [hm, hn']
  change (if (r (.GPR 0#5) s).toNat ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 48
    then s.mem (r (.GPR 1#5) s + BitVec.ofNat 64 (a.toNat - (r (.GPR 0#5) s).toNat))
    else s.mem a) = _
  by_cases h : (r (.GPR 0#5) s).toNat ≤ a.toNat ∧ a.toNat < (r (.GPR 0#5) s).toNat + 48
  · rw [if_pos h, write_zero_inside s 48 _ a 0#384 rfl hd h.1 h.2]
    exact hz (a.toNat - (r (.GPR 0#5) s).toNat) (by omega)
  · rw [if_neg h, write_mem_bytes_frame s _ 48 _ a hd (by omega)]

theorem failure_copy_memory (s : ArmState) (hs : Separated s) :
    (Memcpy.result (failurePrepared s)).mem =
      (write_mem_bytes 48 (r (.GPR 0#5) s + 24#64) 0#384 (failureMemory s)).mem := by
  have hr := failure_prepared_registers s
  have hm := memcpy_zero_memory (failurePrepared s) hr.2.2.1 (source_zero48 s hs)
    (by rw [hr.1]; have := hs.outputHigh; bv_omega)
    (by rw [hr.2.1]; have := hs.stackHigh; bv_omega)
    (by
      rw [hr.1, hr.2.1]
      have h := hs.working
      have hlo := hs.stackLow
      have hhi := hs.stackHigh
      have hout := hs.outputHigh
      unfold Memcpy.Disjoint
      bv_omega)
  rw [hm, hr.1]
  exact mem_write_mem_bytes_of_mem_eq (failure_prepared_memory s hs) _ _ _

theorem failure_ready_memory (s : ArmState) (hs : Separated s) :
    (failureReady s).mem = (failureResultMemory s).mem := by
  have hr := failure_prepared_registers s
  have h19 := Memcpy.result_frame (failurePrepared s) (.GPR 19#5) (by simp [Memcpy.Preserved])
  have h20 := Memcpy.result_frame (failurePrepared s) (.GPR 20#5) (by simp [Memcpy.Preserved])
  failure_return_expand
  rw [h19, h20, hr.2.2.2.1, hr.2.2.2.2.1]
  unfold failureResultMemory
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  apply mem_write_mem_bytes_of_mem_eq
  simp only [ArmState.mem_w_eq_mem]
  exact failure_copy_memory s hs

theorem failure_ready_frame (s : ArmState) (hs : Separated s) :
    Frame s (failureReady s) := by
  intro a ha hb
  rw [failure_ready_memory s hs]
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  simp (disch := first | rfl | tail_side)
    [failureResultMemory, failureMemory, write_mem_bytes_frame]

theorem failure_ready_result (s : ArmState) (hs : Separated s) :
    SszNative.UintCodec.scratchExhaustedAt (widthLoad (failureReady s))
      (r (.GPR 0#5) s).toNat := by
  have hm : ∀ n a, read_mem_bytes n a (failureReady s) =
      read_mem_bytes n a (failureResultMemory s) := by
    exact Memory.mem_eq_iff_read_mem_bytes_eq.mp (failure_ready_memory s hs)
  rcases hs with ⟨hlo, hhi, hout, hwork, hact⟩
  change SszNative.UintCodec.errorAt _ _ _ _ _
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals
    simp (disch := first | rfl | tail_side)
      [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, hm,
       failureResultMemory, failureMemory, read_zero_inside]

end SszArm.UintCodec.Tail
