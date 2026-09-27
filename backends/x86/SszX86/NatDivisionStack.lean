import SszX86.NatDivisionCore
import SszX86.DelimitedStackMemory

namespace SszX86.NatDivision

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The seven saves occupy 56 bytes; the remaining lower word belongs to CALL. -/
theorem activation_load (m : DataMem) (sp : BitVec 64) (distance : Nat)
    (hm : UintCodec.Large.Mapped m (sp - 64) 64)
    (lo : 8 ≤ distance) (hi : distance ≤ 64) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 distance) 8 = some old := by
  have address : sp - BitVec.ofNat 64 distance =
      (sp - 64) + BitVec.ofNat 64 (64-distance) := by bv_omega
  rw [address]
  exact UintCodec.Large.mapped_load m (sp - 64) 64 (64-distance) 8 hm (by omega)

def pushedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.rbp.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 16) 8 s.regs.r15.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 24) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 32) 8 s.regs.r13.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 40) 8 s.regs.r12.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 48) 8 s.regs.rbx.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 56) 8 s.regs.rax.toBitVec.toInt

def pushedState (s : MachineData) : MachineData :=
  {s with dmem := pushedMem s
          regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 56)}}

macro "natdiv_push " row:num " at " distance:num " using " hc:term
    " mapped " hm:term : tactic => `(tactic|
  (natdiv_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have hm' := $hm
     apply activation_load (distance := $distance)
     · repeat' first | exact hm' | apply UintCodec.Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- Every PUSH is executed, including the scratch save of RAX at offset 56. -/
theorem pushes_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 64) 64)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (pushedState s, base + 11)) :
    Eventually (step e) P (s, base + 0) := by
  natdiv_push 0 at 8 using hc mapped hm
  natdiv_push 1 at 16 using hc mapped hm
  natdiv_push 2 at 24 using hc mapped hm
  natdiv_push 3 at 32 using hc mapped hm
  natdiv_push 4 at 40 using hc mapped hm
  natdiv_push 5 at 48 using hc mapped hm
  natdiv_push 6 at 56 using hc mapped hm
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 56 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  simpa [pushedState, pushedMem, Width.bytesv, BitVec.sub_sub, stackReg] using hp

/-- ABI arguments are retained in RBX/R13/R12 before testing the operand pointer. -/
def prologueState (s : MachineData) : MachineData :=
  {pushedState s with regs := {(pushedState s).regs with
    r12 := s.regs.r8, r13 := s.regs.rcx, rbx := s.regs.rdi}}

theorem prologue_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : UintCodec.Large.Mapped s.dmem (s.regs.rsp.toBitVec - 64) 64)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (prologueState s, base + 20)) :
    Eventually (step e) P (s, base) := by
  have run : Eventually (step e) P (s, base + 0) := by
    apply pushes_cps e base hc s hm P
    natdiv_step 7 using hc
    natdiv_step 8 using hc
    natdiv_step 9 using hc
    simpa [prologueState, pushedState] using hp
  simpa using run

/-- The scratch word at offset zero is not restored; these six words are. -/
structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) : Prop where
  rbx : Mem.loadInt m (sp + 8#64) 8 = some (original.regs.rbx.toBitVec.toInt.take 64)
  r12 : Mem.loadInt m (sp + 16#64) 8 = some (original.regs.r12.toBitVec.toInt.take 64)
  r13 : Mem.loadInt m (sp + 24#64) 8 = some (original.regs.r13.toBitVec.toInt.take 64)
  r14 : Mem.loadInt m (sp + 32#64) 8 = some (original.regs.r14.toBitVec.toInt.take 64)
  r15 : Mem.loadInt m (sp + 40#64) 8 = some (original.regs.r15.toBitVec.toInt.take 64)
  rbp : Mem.loadInt m (sp + 48#64) 8 = some (original.regs.rbp.toBitVec.toInt.take 64)

/-- Only the 48 saved-register bytes are needed to transport the restoration invariant. -/
theorem savedAt_congr (m n : DataMem) (sp : BitVec 64) (original : MachineData)
    (same : ∀ i < 48, n.get? (sp + 8#64 + BitVec.ofNat 64 i) =
      m.get? (sp + 8#64 + BitVec.ofNat 64 i)) (saved : SavedAt m sp original) :
    SavedAt n sp original := by
  have contents (distance : Nat) (lo : 8 ≤ distance) (hi : distance + 8 ≤ 56) :
      Mem.loadInt n (sp + BitVec.ofNat 64 distance) 8 =
        Mem.loadInt m (sp + BitVec.ofNat 64 distance) 8 := by
    apply memmove_loadInt_congr
    intro i inside
    have address : sp + BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
        sp + 8#64 + BitVec.ofNat 64 (distance-8+i) := by bv_omega
    rw [address]
    exact same (distance-8+i) (by omega)
  exact ⟨(contents 8 (by decide) (by decide)).trans saved.rbx,
    (contents 16 (by decide) (by decide)).trans saved.r12,
    (contents 24 (by decide) (by decide)).trans saved.r13,
    (contents 32 (by decide) (by decide)).trans saved.r14,
    (contents 40 (by decide) (by decide)).trans saved.r15,
    (contents 48 (by decide) (by decide)).trans saved.rbp⟩

/-- The scratch word at main RSP lies strictly below all six saved registers. -/
theorem savedAt_scratch (m : DataMem) (sp : BitVec 64) (original : MachineData)
    (value : Int) (saved : SavedAt m sp original) :
    SavedAt (Mem.storeInt m sp 8 value) sp original := by
  apply savedAt_congr m _ sp original _ saved
  intro i hi
  apply memmove_store_lookup_outside
  intro j hj
  have inside : j < 8 := by simpa only [Int.toBytes_length] using hj
  bv_omega

/-- Saved-register loads follow from the actual stores, not an entry premise. -/
theorem pushed_saved (s : MachineData) :
    SavedAt (pushedMem s) (s.regs.rsp.toBitVec - 56) s := by
  have address (a : Nat) (ha : a ≤ 56) :
      s.regs.rsp.toBitVec - 56 + BitVec.ofNat 64 a =
        s.regs.rsp.toBitVec - BitVec.ofNat 64 (56-a) := by bv_omega
  constructor
  all_goals
    simp (disch := decide) only [address, Nat.reduceSub]
    simp (disch := first | decide | omega) only
      [pushedMem, BitVec.ofNat_eq_ofNat, Delimited.stack_load_apart,
        BoolCodec.load_store_same, Nat.reduceMul]

/-- Stack writes retain physical mappedness, irrespective of the stored values. -/
theorem pushed_mapped (s : MachineData) (p : BitVec 64) (count : Nat)
    (hm : UintCodec.Large.Mapped s.dmem p count) :
    UintCodec.Large.Mapped (pushedMem s) p count := by
  unfold pushedMem
  repeat' apply UintCodec.Large.mapped_store
  exact hm

/-- A stack store's byte footprint is bounded without a nonwrapping-capacity premise. -/
theorem stack_store_frame (m : DataMem) (sp a : BitVec 64)
    (span distance count : Nat) (value : Int)
    (hoff : distance ≤ span) (hcount : count ≤ distance)
    (outside : ∀ i < span, a ≠ (sp - BitVec.ofNat 64 span) + BitVec.ofNat 64 i) :
    (Mem.storeInt m (sp - BitVec.ofNat 64 distance) count value).get? a = m.get? a := by
  apply memmove_store_lookup_outside
  intro i hi
  have index : i < count := by simpa only [Int.toBytes_length] using hi
  have address : sp - BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
      (sp - BitVec.ofNat 64 span) + BitVec.ofNat 64 (span-distance+i) := by bv_omega
  rw [address]
  exact outside (span-distance+i) (by omega)

theorem pushed_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 56, a ≠ (s.regs.rsp.toBitVec - 56) + BitVec.ofNat 64 i) :
    (pushedMem s).get? a = s.dmem.get? a := by
  simp (disch := first | assumption | decide | omega) only
    [pushedMem, BitVec.ofNat_eq_ofNat, stack_store_frame (span := 56)]

theorem pushed_activation_frame (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 64, a ≠ (s.regs.rsp.toBitVec - 64) + BitVec.ofNat 64 i) :
    (pushedMem s).get? a = s.dmem.get? a := by
  simp (disch := first | assumption | decide | omega) only
    [pushedMem, BitVec.ofNat_eq_ofNat, stack_store_frame (span := 64)]

/-- The incoming return address lies above all seven writes. -/
theorem pushed_return_slot (s : MachineData) :
    Mem.loadInt (pushedMem s) s.regs.rsp.toBitVec 8 =
      Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
  apply memmove_loadInt_congr
  intro i hi
  apply pushed_frame
  intro j hj
  bv_omega

end SszX86.NatDivision
