import SszX86.CodecIsFixedDecode
import SszX86.MemmoveMemory

namespace SszX86.CodecIsFixed
open BoolCodec UintCodec

def savedMem (s : MachineData) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt s.dmem
    (s.regs.rsp.toBitVec - 8) 8 s.regs.r14.toBitVec.toInt)
    (s.regs.rsp.toBitVec - 16) 8 s.regs.rbx.toBitVec.toInt)
    (s.regs.rsp.toBitVec - 24) 8 s.regs.rax.toBitVec.toInt

def savedState (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 24)}
    dmem := savedMem s}

theorem push_load (m : DataMem) (sp : BitVec 64) (offset : Nat)
    (hm : Large.Mapped m (sp - 24) 24) (lo : 8 ≤ offset) (hi : offset ≤ 24) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 offset) 8 = some old := by
  have address : sp - BitVec.ofNat 64 offset =
      (sp - 24) + BitVec.ofNat 64 (24 - offset) := by bv_omega
  rw [address]
  exact Large.mapped_load m (sp - 24) 24 (24 - offset) 8 hm (by omega)

macro "codec_is_fixed_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (codec_is_fixed_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.CodecIsFixed.push_load (offset := $off)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- Original PC0 through the three real PUSH instructions; all overwritten
stack contents may be arbitrary. -/
theorem pushes_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hm : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 24) 24)
    (next : Eventually (step e) P (savedState s, base + 4)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 = s.regs.rsp - 24 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  codec_is_fixed_push 0, 8 using hc, hm
  codec_is_fixed_push 1, 16 using hc, hm
  codec_is_fixed_push 2, 24 using hc, hm
  simpa [savedState, savedMem, Width.bytesv, BitVec.sub_sub, stackReg] using next

theorem saved_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (savedMem s) p n := by
  unfold savedMem
  repeat' first | exact hm | apply Large.mapped_store

/-- No byte outside the 24-byte activation changes in the entry sequence. -/
theorem saved_lookup (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 24, a ≠ s.regs.rsp.toBitVec - 24 + BitVec.ofNat 64 i) :
    (savedMem s).get? a = s.dmem.get? a := by
  have unchanged (m : DataMem) (off : Nat) (range : 8 ≤ off ∧ off ≤ 24) (value : Int) :
      (Mem.storeInt m (s.regs.rsp.toBitVec - BitVec.ofNat 64 off) 8 value).get? a =
        m.get? a := by
    apply memmove_store_lookup_outside
    intro j hj
    have bound : j < 8 := by simpa only [Int.toBytes_length] using hj
    have address : s.regs.rsp.toBitVec - BitVec.ofNat 64 off + BitVec.ofNat 64 j =
        s.regs.rsp.toBitVec - 24 + BitVec.ofNat 64 (24 - off + j) := by bv_omega
    rw [address]
    exact outside _ (by omega)
  unfold savedMem
  simp only [show (8 : BitVec 64) = 8#64 by decide,
    show (16 : BitVec 64) = 16#64 by decide,
    show (24 : BitVec 64) = 24#64 by decide]
  rw [unchanged _ 24 (by decide), unchanged _ 16 (by decide), unchanged _ 8 (by decide)]

theorem saved_load (s : MachineData) (p : BitVec 64) (n : Nat)
    (outside : ∀ i < n, ∀ j < 24,
      p + BitVec.ofNat 64 i ≠ s.regs.rsp.toBitVec - 24 + BitVec.ofNat 64 j) :
    Mem.loadInt (savedMem s) p n = Mem.loadInt s.dmem p n := by
  apply memmove_loadInt_congr
  intro i hi
  exact saved_lookup s _ (outside i hi)

end SszX86.CodecIsFixed
