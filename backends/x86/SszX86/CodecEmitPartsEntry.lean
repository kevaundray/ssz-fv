import SszX86.CodecEmitPartsSteps
import SszX86.EmitPush
import SszX86.DelimitedReservation

namespace SszX86.CodecEmitParts
open UintCodec

macro "codec_parts_push " row:num ", " off:num " using " hc:term
    ", " hm:term : tactic => `(tactic|
  (codec_parts_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply SszX86.Dispatch.push_load (offset := $off)
     · repeat' first | exact hm' | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

theorem pushes_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (next : Eventually (step e) P (Emit.savedState s, base + 10)) :
    Eventually (step e) P (s, base) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, base + 0) by
    simpa only [Int64.add_zero] using run
  codec_parts_push 0, 8 using code, mapped
  codec_parts_push 1, 16 using code, mapped
  codec_parts_push 2, 24 using code, mapped
  codec_parts_push 3, 32 using code, mapped
  codec_parts_push 4, 40 using code, mapped
  codec_parts_push 5, 48 using code, mapped
  simpa [Dispatch.savedState, Dispatch.savedMem, Width.bytesv, BitVec.sub_sub, stackReg]
    using next

def entryMemory (s : MachineData) : DataMem :=
  Mem.storeInt
    (Mem.storeInt (Emit.savedMem s) (s.regs.rsp.toBitVec - 184) 8 s.regs.r9.toBitVec.toInt)
    (s.regs.rsp.toBitVec - 192) 8 s.regs.rdi.toBitVec.toInt

def entryState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with dmem := entryMemory s,
    regs := {s.regs with rsp := s.regs.rsp - 200, r12 := s.regs.rdx}, status := flags}

/-- Six saved registers, the 152-byte local frame, and both ABI spills are
performed by their linked instructions before testing the optional plan. -/
theorem entry_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapped : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 200) 200)
    (next : ∀ auxiliary, Eventually (step e) P
      (entryState s (.from_result s.regs.r8.toBitVec
        {cf := false, of := false, af := auxiliary}), base + 33)) :
    Eventually (step e) P (s, base) := by
  have pushes : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48 := by
    have restricted := Delimited.mapped_subrange s.dmem (s.regs.rsp.toBitVec - 200)
      200 152 48 mapped (by decide)
    have address : s.regs.rsp.toBitVec - 200 + BitVec.ofNat 64 152 =
        s.regs.rsp.toBitVec - 48 := by bv_omega
    simpa only [address] using restricted
  have afterPushes : Large.Mapped (Emit.savedMem s) (s.regs.rsp.toBitVec - 200) 200 := by
    unfold Emit.savedMem Dispatch.savedMem
    repeat' apply Large.mapped_store
    exact mapped
  have outAddress : (s.regs.rsp.toBitVec - 48) - 152 + 16#64 =
      s.regs.rsp.toBitVec - 184 := by bv_omega
  have resultAddress : (s.regs.rsp.toBitVec - 48) - 152 + 8#64 =
      s.regs.rsp.toBitVec - 192 := by bv_omega
  have stackReg : s.regs.rsp - 48 - 152 = s.regs.rsp - 200 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  apply pushes_cps e base code s P pushes
  codec_parts_step 6 using code
  codec_parts_step 7 using code
  apply Delimited.store_cps
  · have load := Large.mapped_load (Emit.savedMem s) (s.regs.rsp.toBitVec - 200)
      200 16 8 afterPushes (by decide)
    convert load using 1 <;>
      simp [Dispatch.savedState, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat] <;> bv_omega
  simp only [Effects.All]
  codec_parts_step 8 using code
  codec_parts_step 9 using code
  constructor <;> codec_parts_step 10 using code
  all_goals apply Delimited.store_cps
  all_goals
    first
    | (have region := Large.mapped_store (Emit.savedMem s)
        (s.regs.rsp.toBitVec - 200) (s.regs.rsp.toBitVec - 184) 200 8
        s.regs.r9.toBitVec.toInt afterPushes
       have load := Large.mapped_load _ (s.regs.rsp.toBitVec - 200) 200 8 8 region (by decide)
       convert load using 1 <;>
         simp [Dispatch.savedState, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat, outAddress] <;> bv_omega)
    | simpa [entryState, entryMemory, Dispatch.savedState, outAddress, resultAddress,
        stackReg, Effects.All] using next _

end SszX86.CodecEmitParts
