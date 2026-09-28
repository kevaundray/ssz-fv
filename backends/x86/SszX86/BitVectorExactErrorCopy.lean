import SszX86.BitVectorAddErrorDecode
import SszX86.BitVectorFrame

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- Nine native copy words; the last includes status and unspecified padding. -/
structure ExactErrorImage where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64

def exactCopyThreeMem (m : DataMem) (dst : BitVec 64) (a b c : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (dst + BitVec.ofNat 64 0) 8 a.toInt
  let m := Mem.storeInt m (dst + BitVec.ofNat 64 8) 8 b.toInt
  Mem.storeInt m (dst + BitVec.ofNat 64 16) 8 c.toInt

def exactCopyThree (s : MachineData) (a b c : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with
      rsi := UInt64.ofBitVec (s.regs.rsi.toBitVec + 24#64)
      rdi := UInt64.ofBitVec (s.regs.rdi.toBitVec + 24#64)
      r11 := UInt64.ofBitVec c}
    dmem := exactCopyThreeMem s.dmem s.regs.rdi.toBitVec a b c}

theorem exact_chunk_read (m : DataMem) (src dst : BitVec 64)
    (a n b k : Nat) (value : Int)
    (apart : Large.Disjoint src dst 24 24)
    (ha : a + n ≤ 24) (hb : b + k ≤ 24) :
    Mem.loadInt (Mem.storeInt m (dst + BitVec.ofNat 64 b) k value)
      (src + BitVec.ofNat 64 a) n = Mem.loadInt m (src + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  simp only [memmove_addr_add]
  exact apart (a + i) (by omega) (b + j) (by omega)

theorem exact_chunk_read_zero (m : DataMem) (src dst : BitVec 64)
    (a n k : Nat) (value : Int)
    (apart : Large.Disjoint src dst 24 24)
    (ha : a + n ≤ 24) (hb : k ≤ 24) :
    Mem.loadInt (Mem.storeInt m dst k value) (src + BitVec.ofNat 64 a) n =
      Mem.loadInt m (src + BitVec.ofNat 64 a) n := by
  simpa only [BitVec.add_zero] using
    exact_chunk_read m src dst a n 0 k value apart ha (by simpa only [Nat.zero_add] using hb)

theorem error_wrapped_address (value : Int) :
    BitVec.ofInt 64 (value.bmod 18446744073709551616) = BitVec.ofInt 64 value := by
  simpa only [BitVec.toInt_ofInt, Nat.reducePow] using
    (BitVec.ofInt_toInt (x := BitVec.ofInt 64 value))

macro "bitvector_exact_load " row:num " using " hc:term " word " hl:term : tactic => `(tactic|
  (bitvector_remaining_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      error_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      exact_chunk_read, exact_chunk_read_zero, ($hl), Delimited.word_cast]))

macro "bitvector_exact_store " row:num " at " off:num " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 24) (byteCount := 8))
  else
    `(tactic| apply Large.mapped_load (capacity := 24) («offset» := $off) («width» := 8))
  `(tactic|
    (bitvector_remaining_step $row using $hc
     try simp only [error_wrapped_address, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply Large.mapped_store
       · decide
     simp only [Effects.All]))

macro "bitvector_exact_three " first:num " using " hc:term
    " words " h0:term ", " h1:term ", " h2:term " mapped " hm:term : tactic => do
  let n := first.getNat
  let r1 := Lean.Syntax.mkNumLit (toString (n + 1))
  let r2 := Lean.Syntax.mkNumLit (toString (n + 2))
  let r3 := Lean.Syntax.mkNumLit (toString (n + 3))
  let r4 := Lean.Syntax.mkNumLit (toString (n + 4))
  let r5 := Lean.Syntax.mkNumLit (toString (n + 5))
  let r6 := Lean.Syntax.mkNumLit (toString (n + 6))
  let r7 := Lean.Syntax.mkNumLit (toString (n + 7))
  let r8 := Lean.Syntax.mkNumLit (toString (n + 8))
  let r9 := Lean.Syntax.mkNumLit (toString (n + 9))
  let r10 := Lean.Syntax.mkNumLit (toString (n + 10))
  let r11 := Lean.Syntax.mkNumLit (toString (n + 11))
  `(tactic|
    (bitvector_exact_load $first using $hc word $h0
     bitvector_exact_store $r1 at 0 using $hc mapped $hm
     bitvector_remaining_step $r2 using $hc
     bitvector_remaining_step $r3 using $hc
     bitvector_exact_load $r4 using $hc word $h1
     bitvector_exact_store $r5 at 8 using $hc mapped $hm
     bitvector_remaining_step $r6 using $hc
     bitvector_remaining_step $r7 using $hc
     bitvector_exact_load $r8 using $hc word $h2
     bitvector_exact_store $r9 at 16 using $hc mapped $hm
     bitvector_remaining_step $r10 using $hc
     bitvector_remaining_step $r11 using $hc))

theorem exact_error_copy0_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a b c : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rdi.toBitVec 24)
    (apart : Large.Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec 24 24)
    (h0 : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (a.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (b.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (exactCopyThree s a b c, base + 4720)) :
    Eventually (step e) P (s, base + 4678) := by
  bitvector_exact_three 102 using hc words h0, h1, h2 mapped hm
  simpa [exactCopyThree, exactCopyThreeMem, error_wrapped_address,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc, UInt64.add_assoc] using next

theorem exact_error_copy1_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a b c : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rdi.toBitVec 24)
    (apart : Large.Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec 24 24)
    (h0 : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (a.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (b.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (exactCopyThree s a b c, base + 4762)) :
    Eventually (step e) P (s, base + 4720) := by
  bitvector_exact_three 114 using hc words h0, h1, h2 mapped hm
  simpa [exactCopyThree, exactCopyThreeMem, error_wrapped_address,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc, UInt64.add_assoc] using next

theorem exact_error_copy2_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (a b c : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rdi.toBitVec 24)
    (apart : Large.Disjoint s.regs.rsi.toBitVec s.regs.rdi.toBitVec 24 24)
    (h0 : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (a.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 8#64) 8 = some (b.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsi.toBitVec + 16#64) 8 = some (c.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (exactCopyThree s a b c, base + 4804)) :
    Eventually (step e) P (s, base + 4762) := by
  bitvector_exact_three 126 using hc words h0, h1, h2 mapped hm
  simpa [exactCopyThree, exactCopyThreeMem, error_wrapped_address,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc, UInt64.add_assoc] using next

end SszX86.BitVector
