import SszX86.EmitMemcpyCallMemory

namespace SszX86.Emit
open UintCodec BoolCodec

inductive CopySite where
  | bytes | bitList | bitVector

def CopySite.pc : CopySite → Nat
  | .bytes => 293 | .bitList => 498 | .bitVector => 732

def CopySite.next : CopySite → Nat
  | .bytes => 299 | .bitList => 504 | .bitVector => 738

/-- Each native CALL stores its real continuation before entering linked memcpy. -/
theorem copy_call_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (site : CopySite) (s : MachineData) (P : MachineState → Prop)
    (hmap : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (next : Eventually (step e) P
      (callState s (base + Int64.ofNat site.next).toBitVec, base + 110736)) :
    Eventually (step e) P (s, base + Int64.ofNat site.pc) := by
  have slot : ∃ old, Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 8) 8 = some old := by
    simpa only [BitVec.add_zero] using
      Large.mapped_load s.dmem (s.regs.rsp.toBitVec - 8) 8 0 8 hmap (by decide)
  cases site with
  | bytes =>
    emit_step 66 using hc
    apply Delimited.store_cps
    · exact slot
    simpa [callState, CopySite.pc, CopySite.next, Effects.All, Int64.add_assoc] using next
  | bitList =>
    emit_step 89 using hc
    apply Delimited.store_cps
    · exact slot
    simpa [callState, CopySite.pc, CopySite.next, Effects.All, Int64.add_assoc] using next
  | bitVector =>
    emit_step 151 using hc
    apply Delimited.store_cps
    · exact slot
    simpa [callState, CopySite.pc, CopySite.next, Effects.All, Int64.add_assoc] using next

/-- Accepted memcpy, including real CALL/RET, with ownership derived from the
current state. No helper-exit or future-memory premise is exposed. -/
theorem copy_call_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736)) (site : CopySite)
    (s : MachineData) (bytes : List UInt8)
    (count : s.regs.rdx.toBitVec = BitVec.ofNat 64 bytes.length)
    (bound : bytes.length < 2 ^ 64)
    (source : ListBytesAt s.dmem s.regs.rsi.toBitVec bytes)
    (hmap : Large.Mapped s.dmem s.regs.rdi.toBitVec bytes.length)
    (slot : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 8) 8)
    (apart : Large.Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec bytes.length bytes.length)
    (sourceStack : Large.Disjoint s.regs.rsi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8)
    (outputStack : Large.Disjoint s.regs.rdi.toBitVec (s.regs.rsp.toBitVec - 8) bytes.length 8) :
    Eventually (step e) (CopyPost s (base + Int64.ofNat site.next).toBitVec bytes)
      (s, base + Int64.ofNat site.pc) := by
  apply copy_call_cps e base hc site s _ slot
  exact copy_helper_runs e (base + 110736) helper s _ bytes count bound source hmap apart
    sourceStack outputStack

end SszX86.Emit
