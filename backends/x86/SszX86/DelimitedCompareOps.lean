import SszX86.DelimitedCore
import SszNatABI

namespace SszX86.Delimited

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def compareMem (s : MachineData) (pointer payload : BitVec 64) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec + 32) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 24) 8 s.regs.rdi.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 16) 8 s.regs.rdx.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec + 8) 8 pointer.toInt
  Mem.storeInt m s.regs.rsp.toBitVec 8 payload.toInt

def compareState (s : MachineData) (pointer payload : BitVec 64) : MachineData :=
  {s with
    dmem := compareMem s pointer payload
    regs := {s.regs with
      rdi := s.regs.r8
      rsi := s.regs.r15
      rdx := UInt64.ofBitVec pointer
      rcx := UInt64.ofBitVec payload
      r9 := UInt64.ofBitVec pointer
      r10 := UInt64.ofBitVec payload
      r12 := s.regs.rcx
      r14 := s.regs.r8}}

macro "delimited_local_store " row:num " at " offset:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply mapped_load_zero (capacity := 40) (byteCount := 8))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 40)
      (offset := $offset) («width» := 8))
  `(tactic|
    (delimited_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

/-- The capacity words are loaded from OptionNat before replacing the argument
registers. All five spills are inside the forty-byte caller-owned local area. -/
theorem compare_arguments_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer payload : BitVec 64)
    (hpointer : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (pointer.toNat : Int))
    (hpayload : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (payload.toNat : Int))
    (hm : UintCodec.Large.Mapped s.dmem s.regs.rsp.toBitVec 40)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (compareState s pointer payload, base + 424)) :
    Eventually (step e) P (s, base + 374) := by
  delimited_step 86 using hc
  delimited_load hpointer
  delimited_step 87 using hc
  delimited_load hpayload
  delimited_local_store 88 at 32 using hc mapped hm
  delimited_local_store 89 at 24 using hc mapped hm
  delimited_step 90 using hc
  delimited_step 91 using hc
  delimited_local_store 92 at 16 using hc mapped hm
  delimited_local_store 93 at 8 using hc mapped hm
  delimited_step 94 using hc
  delimited_step 95 using hc
  delimited_local_store 96 at 0 using hc mapped hm
  delimited_step 97 using hc
  delimited_step 98 using hc
  simpa [compareState, compareMem] using hp

def afterCompareState (s : MachineData) (source out low : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := s.regs.r14
      rdx := UInt64.ofBitVec source
      rcx := s.regs.r12
      rdi := UInt64.ofBitVec out
      r14 := UInt64.ofBitVec low}}

theorem compare_restore_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (source out low : BitVec 64)
    (hsource : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (source.toNat : Int))
    (hout : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (out.toNat : Int))
    (hlow : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (low.toNat : Int))
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (afterCompareState s source out low, base + 450)) :
    Eventually (step e) P (s, base + 429) := by
  delimited_step 100 using hc
  delimited_step 101 using hc
  delimited_load hsource
  delimited_step 102 using hc
  delimited_step 103 using hc
  delimited_load hout
  delimited_step 104 using hc
  delimited_load hlow
  simpa [afterCompareState] using hp

/-- Signed JLE consumes the one-byte Ordering only. The high 56 bits are dead. -/
theorem compare_branch_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (ord : Ordering)
    (value : s.regs.rax.toBitVec.setWidth 8 = SszNative.NatABI.orderingByte ord)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if ord = .gt then base + 454 else base + 523)) :
    Eventually (step e) P (s, base + 450) := by
  have target := hc.targets ("delimited_u523", 523) (by decide)
  have negative : (255#8).msb = true := by decide
  delimited_step 105 using hc
  constructor <;> delimited_step 106 using hc
  all_goals
    cases ord <;>
      simpa [value, SszNative.NatABI.orderingByte, target, negative,
        StatusFlags.from_result, Effects.All] using hp _

end SszX86.Delimited
