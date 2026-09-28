import SszX86.NatMulMemsetEmbedded
import SszX86.EmitMemcpyCallMemory

namespace SszX86.NatMul.MemsetCall
open UintCodec
open Std.ExtHashMap
open Emit

abbrev callState := Emit.callState

structure Post (s : MachineData) (ra : BitVec 64) (n : Nat)
    (t : MachineState) : Prop where
  returned : MemsetReturned (callState s ra) ra t
  output : Emit.ListBytesAt t.1.dmem s.regs.rdi.toBitVec (List.replicate n 0)
  frame : MemoryFrame s.dmem t.1.dmem (fun a =>
    InSpan a s.regs.rdi.toBitVec n ∨ InSpan a (s.regs.rsp.toBitVec - 8) 8)

/-- Extract the old bytes from the current mapped destination, rather than
assuming an initialized buffer or a future helper result. -/
theorem fill_memory_of_mapped (m : DataMem) (dst : BitVec 64) (n : Nat)
    (bound : n < 2^64) (hm : Large.Mapped m dst n) :
    ∃ old frame, old.length = n ∧ FillMem m dst old (Eq frame) := by
  let old := Emit.oldBytes m dst n
  refine ⟨old, m \ old.At dst, Emit.oldBytes_length _ _ _, ?_⟩
  exact Emit.split_memory m (old.At dst)
    (Emit.bytes_submap m dst old (by simpa [old, Emit.oldBytes_length] using Nat.le_of_lt bound)
      (Emit.oldBytes_at m dst n hm))

/-- The linked helper performs the zeroing and its original RET. -/
theorem helper_runs (e : Executable) (helper : Int64) (hc : MemsetCodeAt e helper)
    (s : MachineData) (ra : BitVec 64) (n : Nat)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 n)
    (zero : s.regs.rsi = 0) (bound : n < 2^64)
    (hm : Large.Mapped s.dmem s.regs.rdi.toBitVec n)
    (apart : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) n 8) :
    Eventually (step e) (Post s ra n) (callState s ra, helper) := by
  have hm' : Large.Mapped (callState s ra).dmem s.regs.rdi.toBitVec n :=
    Large.mapped_store _ _ _ _ _ _ hm
  obtain ⟨old, frame, length, owned⟩ := fill_memory_of_mapped
    (callState s ra).dmem s.regs.rdi.toBitVec n bound hm'
  have run := memset_correct helper (callState s ra) n old frame ra length count bound owned
    (Emit.call_return_slot s ra) (by
      intro i hi j hj
      exact Ne.symm (apart j hj i hi))
  have byte : memsetByte (callState s ra) = 0 := by
    simp [memsetByte, callState, Emit.callState, zero]
  rw [byte] at run
  apply eventually_weaken (step e) _ _ _ _ (memset_eventually e helper hc _ _ run)
  intro t post
  refine ⟨post.1, Emit.listBytesAt_of_sep t.1.dmem s.regs.rdi.toBitVec
    (List.replicate n 0) _ (by simpa using Nat.le_of_lt bound) post.2.1, ?_⟩
  intro a outside
  have notOutput : a ∉ (List.replicate n (0 : UInt8)).At s.regs.rdi.toBitVec := by
    intro inside
    obtain ⟨i, hi, equal⟩ :=
      (mem_At_iff (List.replicate n (0 : UInt8)) s.regs.rdi.toBitVec a).1 inside
    exact outside (Or.inl ⟨i, by simpa only [List.length_replicate] using hi, equal⟩)
  rw [post.2.2 a notOutput]
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside (Or.inr ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩)

/-- CALL at 487 has six actual bytes; its relative target is 148928 and
its stored return address is 493, not the five-byte CALL approximation. -/
theorem call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P (callState s (base + 493).toBitVec, base + 148928)) :
    Eventually (step e) P (s, base + 487) := by
  have slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 hm (by decide)
  natmul_step 4 row 12 using hc
  apply Delimited.store_cps
  · exact slot
  simpa [callState, Emit.callState, Effects.All, Int64.add_assoc] using next

theorem runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemsetCodeAt e (base + 148928))
    (s : MachineData) (n : Nat)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 n)
    (zero : s.regs.rsi = 0) (bound : n < 2^64)
    (hm : Large.Mapped s.dmem s.regs.rdi.toBitVec n)
    (slot : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (apart : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) n 8) :
    Eventually (step e) (Post s (base + 493).toBitVec n) (s, base + 487) := by
  apply call_cps e base hc s _ slot
  exact helper_runs e (base + 148928) helper s _ n count zero bound hm apart

end SszX86.NatMul.MemsetCall
