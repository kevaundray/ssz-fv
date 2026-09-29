import SszX86.HashCombineExec

namespace SszX86.Hash.Combine
open SszX86.WordNormalize

abbrev savedMem := Dispatch.savedMem
abbrev savedState := Dispatch.savedState

macro "hash_combine_push " row:num " at " off:num " using " hc:term
    " withMapping " hm:term : tactic => `(tactic|
  (hash_combine_step $row using $hc
   try simp only [BitVec.sub_sub]
   apply Delimited.store_cps
   · have mapping := $hm
     apply Dispatch.push_load (offset := $off)
     · repeat' first | exact mapping | apply Large.mapped_store
     · decide
     · decide
   simp only [Effects.All]))

/-- The exact six pushes, in their shipped order. -/
theorem pushes_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (hm : Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (savedState s, root + 10)) :
    Eventually (step e) P (s, root) := by
  have stackReg : s.regs.rsp - 8 - 8 - 8 - 8 - 8 - 8 = s.regs.rsp - 48 := by
    apply UInt64.toBitVec_inj.1
    simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  suffices run : Eventually (step e) P (s, root + 0) by
    simpa only [Int64.add_zero] using run
  hash_combine_push 0 at 8 using hc withMapping hm
  hash_combine_push 1 at 16 using hc withMapping hm
  hash_combine_push 2 at 24 using hc withMapping hm
  hash_combine_push 3 at 32 using hc withMapping hm
  hash_combine_push 4 at 40 using hc withMapping hm
  hash_combine_push 5 at 48 using hc withMapping hm
  word_simpa [savedState, savedMem, Dispatch.savedState, Dispatch.savedMem,
    Width.bytesv, BitVec.sub_sub, stackReg, UInt64.toBitVec_sub,
    UInt64.toBitVec_ofNat] using next

def reserved (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 120)},
    status := flags}

theorem reserve_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (reserved s flags, root + 14)) :
    Eventually (step e) P (s, root + 10) := by
  hash_combine_step 6 using hc
  word_simpa [reserved] using next _

/-- One initializer store is kept opaque across all later initializer rows. -/
def storeWord (s : MachineData) (offset : Nat) (value : BitVec 64) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem
    (s.regs.rsp.toBitVec + BitVec.ofNat 64 offset) 8 value.toInt}

def zeroBuffer (s : MachineData) : MachineData :=
  storeWord (storeWord (storeWord (storeWord (storeWord (storeWord
    (storeWord (storeWord s 64 0) 56 0) 48 0) 40 0) 32 0) 24 0) 16 0) 8 0

macro "hash_combine_zero " row:num " at " off:num " using " hc:term
    " withMapping " hm:term : tactic => `(tactic|
  (hash_combine_step $row using $hc
   apply Delimited.store_cps
   · have mapping := $hm
     apply Large.mapped_load (capacity := 120) (offset := $off) (width := 8)
     · repeat' first | exact mapping | apply Large.mapped_store
     · decide
   simp only [Effects.All]))

/-- Eight descending qword stores initialize all 64 buffer cells, not merely
its live prefix. No other part of the 112-byte state is written here. -/
theorem zero_buffer_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rsp.toBitVec 120)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (zeroBuffer s, root + 101)) :
    Eventually (step e) P (s, root + 29) := by
  hash_combine_zero 12 at 64 using hc withMapping hm
  hash_combine_zero 13 at 56 using hc withMapping hm
  hash_combine_zero 14 at 48 using hc withMapping hm
  hash_combine_zero 15 at 40 using hc withMapping hm
  hash_combine_zero 16 at 32 using hc withMapping hm
  hash_combine_zero 17 at 24 using hc withMapping hm
  hash_combine_zero 18 at 16 using hc withMapping hm
  hash_combine_zero 19 at 8 using hc withMapping hm
  word_simpa [zeroBuffer, storeWord] using next

def chainPointer (s : MachineData) : MachineData :=
  {s with regs := {s.regs with r12 := UInt64.ofBitVec (s.regs.rsp.toBitVec + 72)}}

theorem chain_pointer_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (chainPointer s, root + 106)) :
    Eventually (step e) P (s, root + 101) := by
  hash_combine_step 20 using hc
  word_simpa [chainPointer] using next

def initialWord (s : MachineData) (offset : Nat) (value : BitVec 64) : MachineData :=
  {storeWord s offset value with regs := {s.regs with rax := UInt64.ofBitVec value}}

/-- Each packed immediate is exactly two little-endian IV words. -/
def initializedChain (s : MachineData) : MachineData :=
  initialWord (initialWord (initialWord (initialWord s
    72 0xbb67ae856a09e667) 80 0xa54ff53a3c6ef372)
    88 0x9b05688c510e527f) 96 0x5be0cd191f83d9ab

macro "hash_combine_iv " immRow:num " encodedStoreRow " storeRow:num " at " off:num
    " using " hc:term " withMapping " hm:term : tactic => `(tactic|
  (hash_combine_step $immRow using $hc
   hash_combine_step $storeRow using $hc
   apply Delimited.store_cps
   · have mapping := $hm
     apply Large.mapped_load (capacity := 120) (offset := $off) (width := 8)
     · repeat' first | exact mapping | apply Large.mapped_store
     · decide
   simp only [Effects.All]))

theorem initial_chain_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rsp.toBitVec 120)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (initializedChain s, root + 166)) :
    Eventually (step e) P (s, root + 106) := by
  hash_combine_iv 21 encodedStoreRow 22 at 72 using hc withMapping hm
  hash_combine_iv 23 encodedStoreRow 24 at 80 using hc withMapping hm
  hash_combine_iv 25 encodedStoreRow 26 at 88 using hc withMapping hm
  hash_combine_iv 27 encodedStoreRow 28 at 96 using hc withMapping hm
  word_simpa [initializedChain, initialWord, storeWord] using next

/-- The left length is recorded before entering the direct-block loop. -/
def initialCounters (s : MachineData) : MachineData :=
  storeWord (storeWord s 104 0) 112 s.regs.rdx.toBitVec

theorem initial_counters_runs (e : Executable) (root : Int64) (hc : CodeAt e root)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rsp.toBitVec 120)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (initialCounters s, root + 180)) :
    Eventually (step e) P (s, root + 166) := by
  hash_combine_zero 29 at 104 using hc withMapping hm
  hash_combine_step 30 using hc
  apply Delimited.store_cps
  · apply Large.mapped_load (capacity := 120) (offset := 112) (width := 8)
    · exact Large.mapped_store _ _ _ _ _ _ hm
    · decide
  word_simpa [initialCounters, storeWord, Effects.All] using next

/-- Six saves, 120 local bytes, and the called finalizer's return slot plus
192-byte owned stack give the actual deepest 368-byte stack footprint. -/
theorem stack_layout :
    6 * 8 + 120 = 168 ∧ 168 + 8 + 192 = 368 ∧
    168 - 8 = 160 ∧ 160 - 64 = 96 ∧ 160 - 112 = 48 := by
  decide

end SszX86.Hash.Combine
