import SszX86.EmitMemcpyCall
import SszX86.Udivti3Math
import SszX86.DelimitedRetain

namespace SszX86.Emit.Bytes
open BoolCodec UintCodec

def tagged (s : MachineData) : MachineData :=
  {s with regs := {s.regs with rax := 2}, status := Memcmp.subFlags 2#32 2#32}

theorem type_guard (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (tag : s.regs.rax.toBitVec = 2#64 ∨ s.regs.rax.toBitVec = 3#64)
    (next : Eventually (step e) P (tagged s, base + 268)) :
    Eventually (step e) P (s, base + 256) := by
  have mask2 : (2 : UInt64) &&& 4294967294 = 2 := by decide
  have mask3 : (3 : UInt64) &&& 4294967294 = 2 := by decide
  rcases tag with tag | tag
  all_goals
    emit_step 57 using hcode
    simp only [tag]
    constructor <;>
      emit_step 58 using hcode <;>
      emit_step 59 using hcode <;>
      simp_all [tagged, Memcmp.subFlags, StatusFlags.from_result, BitVec.take, BitVec.signed, Effects.All]

def lengthLoaded (s : MachineData) (count : Nat) : MachineData :=
  {s with regs := {s.regs with r13 := UInt64.ofNat count}}

theorem length_load (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (count : Nat) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 16) 8 = some (count : Int))
    (next : Eventually (step e) P (lengthLoaded s count, base + 273)) :
    Eventually (step e) P (s, base + 268) := by
  simp only [show (16 : BitVec 64) = 16#64 by decide] at stored
  emit_step 60 using hcode
  simpa [MachineData.load, Effects.All, stored, lengthLoaded,
    BitVec.ofInt_natCast, Delimited.uint64_literal] using next

def compared (s : MachineData) : MachineData :=
  {s with status := Udivti3.subFlags s.regs.r13.toBitVec s.regs.r9.toBitVec}

theorem capacity_guard (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (fits : s.regs.r13.toNat ≤ s.regs.r9.toNat)
    (next : Eventually (step e) P (compared s, base + 282)) :
    Eventually (step e) P (s, base + 273) := by
  have branch : Eventually (step e) P (compared s, base + 276) := by
    emit_step 62 using hcode
    simp only [compared, Udivti3.subFlags_cf, Udivti3.subFlags_zf]
    by_cases equal : s.regs.r13.toBitVec = s.regs.r9.toBitVec
    · simpa [compared, equal, Effects.All] using next
    · have strict : s.regs.r13.toNat < s.regs.r9.toNat := by
        have different : s.regs.r13.toNat ≠ s.regs.r9.toNat := by
          intro same
          exact equal (BitVec.eq_of_toNat_eq same)
        omega
      simpa [compared, strict, Effects.All] using next
  emit_step 61 using hcode
  simpa [compared, Udivti3.subFlags, BitVec.take, BitVec.signed] using branch

def copyReady (s : MachineData) (src : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rsi := UInt64.ofBitVec src, rdi := s.regs.r14, rdx := s.regs.r13}}

theorem copy_prepare (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (src : BitVec 64) (P : MachineState → Prop)
    (stored : Mem.loadInt s.dmem (s.regs.r12.toBitVec + 8) 8 = some (src.toNat : Int))
    (next : Eventually (step e) P (copyReady s src, base + 293)) :
    Eventually (step e) P (s, base + 282) := by
  have cast : BitVec.ofInt 64 (src.toNat : Int) = src := by bv_omega
  simp only [show (8 : BitVec 64) = 8#64 by decide] at stored
  emit_step 63 using hcode
  simp only [MachineData.load, Effects.All, stored, cast]
  emit_step 64 using hcode
  emit_step 65 using hcode
  simpa [copyReady] using next

def written (s : MachineData) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem s.regs.rbx.toBitVec 8 s.regs.r13.toBitVec.toInt}

theorem finish (e : Executable) (base : Int64) (hcode : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 8)
    (next : Eventually (step e) P (written s, base + 1593)) :
    Eventually (step e) P (s, base + 299) := by
  emit_step 67 using hcode
  apply Delimited.store_cps
  · simpa only [BitVec.add_zero] using Large.mapped_load _ _ 8 0 8 hmap (by decide)
  simp only [Effects.All]
  emit_step 68 using hcode
  simpa only [written] using next

end SszX86.Emit.Bytes
