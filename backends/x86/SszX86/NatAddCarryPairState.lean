import SszX86.NatAddCarryMath

namespace SszX86.NatAdd.Carry.Pair
open Kraken.X64.Parser

abbrev get (s : MachineData) (r : Reg64) : BitVec 64 := s.regs.get64 r

def firstWord (s : MachineData) (first : BitVec 64) : BitVec 64 :=
  get s .r14 + first

def firstCarry (s : MachineData) (first : BitVec 64) : Bool :=
  (Udivti3.addFlags (get s .r14) first).cf

def secondWord (s : MachineData) (first second : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (firstCarry s first).toNat + second

def secondCarry (s : MachineData) (first second : BitVec 64) : Bool :=
  (Udivti3.addFlags (BitVec.ofNat 64 (firstCarry s first).toNat) second).cf

def firstAddress (s : MachineData) : BitVec 64 :=
  get s .rbx + get s .rsi * 8#64 - 8#64

def secondAddress (s : MachineData) : BitVec 64 :=
  get s .rbx + get s .rsi * 8#64

def memory (s : MachineData) (first second : BitVec 64) : DataMem :=
  Mem.storeInt (Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt)
    (secondAddress s) 8 (secondWord s first second).toInt

def pairState (s : MachineData) (first second : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    dmem := memory s first second
    regs := {s.regs with
      rdx := s.regs.rsi
      rsi := UInt64.ofBitVec (get s .rsi + 2#64)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++
        BitVec.ofNat 8 (firstCarry s first).toNat)
      r12 := UInt64.ofBitVec second
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (secondCarry s first second).toNat)
      r15 := UInt64.ofBitVec (get s .rsi + 1#64)}
    status := flags}

def firstState (s : MachineData) (first : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rdx := s.regs.rsi
      rsi := 0
      r15 := UInt64.ofBitVec first
      r14 := UInt64.ofBitVec (firstWord s first)
      rbp := UInt64.ofBitVec ((get s .rbp).extractLsb' 8 56 ++
        BitVec.ofNat 8 (firstCarry s first).toNat)}
    status := flags}

def firstStoredState (s : MachineData) (first : BitVec 64) (flags : StatusFlags) : MachineData :=
  {firstState s first flags with
    dmem := Mem.storeInt s.dmem (firstAddress s) 8 (firstWord s first).toInt}

def secondReadyState (s : MachineData) (first : BitVec 64) (flags : StatusFlags) : MachineData :=
  {firstStoredState s first flags with
    regs := {(firstState s first flags).regs with
      r15 := UInt64.ofBitVec (get s .rsi + 1#64)}}

def secondLoadedState (s : MachineData) (first second : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {secondReadyState s first flags with
    regs := {(secondReadyState s first flags).regs with r12 := UInt64.ofBitVec second}}

def secondAddedState (s : MachineData) (first second : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {secondLoadedState s first second flags with
    regs := {(secondLoadedState s first second flags).regs with
      rsi := UInt64.ofBitVec (secondWord s first second)
      r14 := UInt64.ofBitVec (BitVec.ofNat 64 (secondCarry s first second).toNat)}}

def secondStoredState (s : MachineData) (first second : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {secondAddedState s first second flags with dmem := memory s first second}

end SszX86.NatAdd.Carry.Pair
