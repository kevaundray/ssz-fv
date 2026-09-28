import SszX86.NatFromU128Commit
import SszX86.NatFromU128Output
import SszNatAddMemory

namespace SszX86.NatFromU128
open SszNative UintCodec BoolCodec
open NatToU128 (ByteFrame narrow_load_preserved narrow_width_preserved)

structure Owned (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) : Prop where
  low : s.regs.rsi.toBitVec = wide.setWidth 64
  high : s.regs.rdx.toBitVec = (wide >>> 64).setWidth 64
  header : Reservation.Header s address capacity used
  arena_bound : address.toNat + capacity.toNat ≤ 2^64
  arena_nonzero : 0 < capacity.toNat → 0 < address.toNat
  free_mapped : Large.Mapped s.dmem (address + used) (capacity.toNat - used.toNat)
  header_bound : s.regs.rcx.toNat + 24 ≤ 2^64
  output_bound : s.regs.rdi.toNat + 68 ≤ 2^64
  output_mapped : OutputMapped s
  return_bound : s.regs.rsp.toNat + 8 ≤ 2^64
  return_load : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))
  output_header : Body.Apart s.regs.rdi.toNat 68 s.regs.rcx.toNat 24
  output_return : Body.Apart s.regs.rdi.toNat 68 s.regs.rsp.toNat 8
  free_output : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rdi.toNat 68
  free_header : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rcx.toNat 24
  free_return : Body.Apart (address.toNat + used.toNat) (capacity.toNat - used.toNat) s.regs.rsp.toNat 8
  cursor_return : Body.Apart (s.regs.rcx.toNat + 16) 8 s.regs.rsp.toNat 8

theorem wide_small_iff (wide : BitVec 128) :
    wide.toNat < 2^64 ↔ (wide >>> 64).setWidth 64 = 0#64 := by
  have bound := wide.isLt
  simp only [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

abbrev outcome (address capacity used : BitVec 64) (wide : BitVec 128) :=
  NatArithmetic.fromWide address.toNat capacity.toNat used.toNat wide

def resultMem (s : MachineData) (address capacity used : BitVec 64) (wide : BitVec 128) : DataMem :=
  if wide.toNat < 2^64 then
    successMem s.dmem s.regs.rdi.toBitVec 0 (wide.setWidth 64)
  else match SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 with
    | none => errorMem s.dmem s.regs.rdi.toBitVec
    | some r => successMem
        (commitMem s.dmem s.regs.rcx.toBitVec (BitVec.ofNat 64 r.pointer)
          (BitVec.ofNat 64 r.used) (wide.setWidth 64) ((wide >>> 64).setWidth 64))
        s.regs.rdi.toBitVec (BitVec.ofNat 64 r.pointer) 2

theorem reserve_geometry (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    0 < r.pointer ∧ r.pointer % 8 = 0 ∧
      address.toNat + used.toNat ≤ r.pointer ∧
      r.pointer + 16 = address.toNat + r.used ∧
      r.used ≤ capacity.toNat ∧ r.pointer + 16 ≤ 2^64 ∧ r.used < 2^64 := by
  obtain ⟨checks, rfl⟩ :=
    (SszNative.Arena.reserve_eq_some_iff_checks _ _ _ 2 (by decide) r).1 reserved
  dsimp only
  have cursor := SszNative.Arena.used_le_start address.toNat used.toNat
  have fits : SszNative.Arena.start address.toNat used.toNat + 16 ≤ capacity.toNat :=
    checks.2.2.2.2.2
  have positive := owned.arena_nonzero (by omega)
  have bound := owned.arena_bound
  refine ⟨by omega, ?_, by omega, ?_, fits, ?_, checks.2.2.2.2.1⟩
  · rw [SszNative.Arena.start_pointer]
    exact SszNative.Arena.aligned_mod _
  · simp only [SszNative.Arena.finish, Nat.add_assoc]
  · omega

theorem reserve_mapped (s : MachineData) (wide : BitVec 128)
    (address capacity used ra : BitVec 64) (owned : Owned s wide address capacity used ra)
    (r : SszNative.Arena.Reservation)
    (reserved : SszNative.Arena.reserve address.toNat capacity.toNat used.toNat 2 = some r) :
    Large.Mapped s.dmem (BitVec.ofNat 64 r.pointer) 16 := by
  have geometry := reserve_geometry s wide address capacity used ra owned r reserved
  have hm := Delimited.Reservation.mapped_subrange s.dmem (address + used)
    (capacity.toNat-used.toNat) (r.pointer-(address.toNat+used.toNat)) 16 owned.free_mapped
    (by omega)
  have pointer : address + used + BitVec.ofNat 64 (r.pointer-(address.toNat+used.toNat)) =
      BitVec.ofNat 64 r.pointer := by bv_omega
  rw [pointer] at hm
  exact hm

/-- Exact permitted writes: the success pair/status or the complete error;
only an actual allocation permits the cursor and its two payload words. -/
def Frame (s : MachineData) (m : DataMem) (address capacity used : BitVec 64)
    (wide : BitVec 128) : Prop :=
  ∀ a : BitVec 64,
    (match (outcome address capacity used wide).result with
      | .ok _ => Body.Outside a.toNat s.regs.rdi.toNat 16 ∧
          Body.Outside a.toNat (s.regs.rdi.toNat+64) 4
      | .error _ => Body.Outside a.toNat s.regs.rdi.toNat 68) →
    (∀ r, (outcome address capacity used wide).allocation = some r →
      Body.Outside a.toNat (s.regs.rcx.toNat+16) 8 ∧ Body.Outside a.toNat r.pointer 16) →
    m.get? a = s.dmem.get? a

theorem commit_frame (m : DataMem) (arena pointer finish low high a : BitVec 64)
    (header : ∀ i < 8, a ≠ arena + 16#64 + BitVec.ofNat 64 i)
    (payload : ∀ i < 16, a ≠ pointer + BitVec.ofNat 64 i) :
    (commitMem m arena pointer finish low high).get? a = m.get? a := by
  dsimp only [commitMem]
  refine Eq.trans (b := (Mem.storeInt (Mem.storeInt m (arena+16) 8 finish.toInt)
    pointer 8 low.toInt).get? a) ?_ ?_
  · apply memmove_store_lookup_outside
    intro i hi
    simpa only [memmove_addr_add] using payload (8+i)
      (by simp only [Int.toBytes_length] at hi; omega)
  refine Eq.trans (b := (Mem.storeInt m (arena+16) 8 finish.toInt).get? a) ?_ ?_
  · apply memmove_store_lookup_outside
    intro i hi
    exact payload i (by simp only [Int.toBytes_length] at hi; omega)
  · apply memmove_store_lookup_outside
    intro i hi
    exact header i (by simpa only [Int.toBytes_length] using hi)

theorem success_frame (m : DataMem) (out pointer payload a : BitVec 64)
    (pair : ∀ i < 16, a ≠ out + BitVec.ofNat 64 i)
    (status : ∀ i < 4, a ≠ out + 64#64 + BitVec.ofNat 64 i) :
    (successMem m out pointer payload).get? a = m.get? a := by
  refine Eq.trans (b := (NatAdd.pairMem m out pointer payload).get? a) ?_ ?_
  · apply memmove_store_lookup_outside
    intro i hi
    exact status i (by simpa only [Int.toBytes_length] using hi)
  · simp (disch := first | assumption | omega | decide) only
      [NatAdd.pairMem, store_frame (limit := 16)]

theorem publication_frame (m : DataMem) (out pointer payload : BitVec 64)
    (bound : out.toNat + 68 ≤ 2^64) :
    ByteFrame m (successMem m out pointer payload) out.toNat 68 ∧
    ByteFrame m (errorMem m out) out.toNat 68 := by
  constructor <;> intro a outside
  · exact NatAdd.success_mem_frame m out pointer payload a
      (fun i hi => Body.outside_byte out a 68 i bound outside hi)
  · exact NatAdd.error_mem_frame m out a
      (fun i hi => Body.outside_byte out a 68 i bound outside hi)

end SszX86.NatFromU128
