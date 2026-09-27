import SszX86.UintResultMemory

namespace SszX86.UintCodec.Tail

open BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private theorem store_cps (s : MachineData) (address : BitVec 64) {w : Width}
    (value : w.type) (ret : MachineData → Effects) (post : MachineState → Prop)
    (hmap : ∃ old, Mem.loadInt s.dmem address w.bytes = some old)
    (next : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All post) :
    (MachineData.store s address value ret).All post := by
  obtain ⟨old, hl⟩ := hmap
  simpa only [MachineData.store, Effects.All, hl] using next

private theorem mapped_load_zero (m : DataMem) (out : BitVec 64) (hm : Mapped m out)
    (byteCount : Nat) (hb : byteCount ≤ 80) :
    ∃ value, Mem.loadInt m out byteCount = some value := by
  simpa using mapped_load m out hm 0 byteCount (by simpa using hb)

macro "uint_tail_store " row:num " at " offset:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if offset.getNat == 0 then
    `(tactic| apply mapped_load_zero (byteCount := $byteCount))
  else
    `(tactic| apply mapped_load (offset := $offset) («width» := $byteCount))
  `(tactic|
    (uint_width_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply store_cps
     · $loadTac
       · repeat' first | exact $hm | apply mapped_store
       · decide
     simp only [Effects.All]))

/-- The actual 5502/5506/5510 stores, shared tag, and jump to the epilogue. -/
theorem success_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (successReady s, base + 7720)) :
    Eventually (step e) P (s, base + 5502) := by
  uint_tail_store 159 at 16 width 1 using hc mapped hm
  uint_tail_store 160 at 24 width 8 using hc mapped hm
  uint_tail_store 161 at 32 width 8 using hc mapped hm
  uint_tail_store 162 at 0 width 8 using hc mapped hm
  uint_width_step 163 using hc
  simpa [successReady, successMem] using hp

/-- The original descriptor pair is copied verbatim, including Large pointers;
the actual length is a Small Nat. Every scope store and jump is executed. -/
theorem scope_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (scopeReady s, base + 7720)) :
    Eventually (step e) P (s, base + 2851) := by
  uint_tail_store 74 at 64 width 8 using hc mapped hm
  uint_tail_store 75 at 56 width 8 using hc mapped hm
  uint_tail_store 76 at 8 width 8 using hc mapped hm
  uint_tail_store 77 at 16 width 8 using hc mapped hm
  uint_tail_store 78 at 24 width 8 using hc mapped hm
  uint_tail_store 79 at 32 width 8 using hc mapped hm
  uint_width_step 80 using hc
  uint_tail_store 109 at 40 width 8 using hc mapped hm
  uint_tail_store 110 at 48 width 8 using hc mapped hm
  uint_tail_store 111 at 72 width 4 using hc mapped hm
  uint_width_step 112 using hc
  uint_tail_store 217 at 0 width 8 using hc mapped hm
  simpa [scopeReady, scopeMem] using hp

private theorem activation_load (m : DataMem) (sp : BitVec 64)
    (hm : ActivationMapped m sp) (offset byteCount : Nat) (hb : offset + byteCount ≤ 368) :
    ∃ value, Mem.loadInt m (sp + BitVec.ofNat 64 offset) byteCount = some value := by
  apply memmove_loadInt_exists
  intro i hi
  rw [memmove_addr_add]
  exact hm (offset + i) (by omega)

private theorem activation_store (m : DataMem) (sp address : BitVec 64)
    (byteCount : Nat) (value : Int) (hm : ActivationMapped m sp) :
    ActivationMapped (Mem.storeInt m address byteCount value) sp := by
  intro i hi
  obtain ⟨old, hold⟩ := hm i hi
  change m[sp + BitVec.ofNat 64 i]? = some old at hold
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases hnew : ((Int.toBytes byteCount value).At address)[sp + BitVec.ofNat 64 i]? with
  | none => exact ⟨old, by simp [hold]⟩
  | some byte => exact ⟨byte, by simp⟩

macro "uint_tail_stack_store " row:num " at " offset:num
    " using " hc:term " mapped " hm:term : tactic => `(tactic|
  (uint_width_step $row using $hc
   try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
   apply store_cps
   · apply activation_load (offset := $offset) (byteCount := 8)
     · repeat' first | exact $hm | apply activation_store
     · decide
   simp only [Effects.All]))

theorem scratch_zero (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : ActivationMapped s.dmem s.regs.rsp.toBitVec)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P
      ({s with dmem := zeroMem s.dmem s.regs.rsp.toBitVec}, base + 2987)) :
    Eventually (step e) P (s, base + 2918) := by
  uint_tail_stack_store 86 at 120 using hc mapped hm
  uint_tail_stack_store 87 at 128 using hc mapped hm
  uint_tail_stack_store 88 at 136 using hc mapped hm
  uint_tail_stack_store 89 at 144 using hc mapped hm
  uint_tail_stack_store 90 at 152 using hc mapped hm
  uint_tail_stack_store 91 at 160 using hc mapped hm
  simpa [zeroMem, memmove_addr_add] using hp

private theorem zero_mem_load (m : DataMem) (sp : BitVec 64)
    (hb : sp.toNat + 368 ≤ 2^64) (offset : Nat)
    (hi : offset ∈ [120, 128, 136, 144, 152, 160]) :
    Mem.loadInt (zeroMem m sp) (sp + BitVec.ofNat 64 offset) 8 = some 0 := by
  have hw : (sp + 120#64).toNat + 80 ≤ 2^64 := by bv_omega
  have hl (i : Nat) (he : offset = 120 + i) :
      sp + BitVec.ofNat 64 offset = sp + 120#64 + BitVec.ofNat 64 i := by
    rw [memmove_addr_add, he]
  simp at hi
  rw [hl (offset - 120) (by omega)]
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := first | assumption | omega | decide) only
      [zeroMem, load_store_offset_disjoint, load_store_same,
       Nat.reduceMul, Nat.reduceSub]
    try decide

private theorem output_stack_load (m : DataMem) (out sp : BitVec 64)
    (ho : out.toNat + 80 ≤ 2^64) (hp : sp.toNat + 368 ≤ 2^64)
    (hsep : out.toNat + 80 ≤ sp.toNat ∨ sp.toNat + 368 ≤ out.toNat)
    (offset storeOffset byteCount : Nat) (value : Int)
    (hoff : offset + 8 ≤ 368) (hs : storeOffset + byteCount ≤ 80) :
    Mem.loadInt (Mem.storeInt m (out + BitVec.ofNat 64 storeOffset) byteCount value)
      (sp + BitVec.ofNat 64 offset) 8 = Mem.loadInt m (sp + BitVec.ofNat 64 offset) 8 := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

macro "uint_tail_zero_load " row:num " at " offset:num " using " hc:term
    " word " hz:term : tactic => `(tactic|
  (uint_width_step $row using $hc
   simp (disch := first | assumption | omega | decide) only
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
      output_stack_load (offset := $offset), ($hz $offset (by decide))]))

private def copyReady (s : MachineData) : MachineData :=
  {s with
    regs := {s.regs with rax := 0, rcx := 0}
    dmem := scratchCopyMem s.dmem s.regs.rdi.toBitVec}

private def ZeroWords (m : DataMem) (sp : BitVec 64) : Prop :=
  ∀ offset ∈ [120, 128, 136, 144, 152, 160],
    Mem.loadInt m (sp + BitVec.ofNat 64 offset) 8 = some 0

/-- Isolate the copy from the six earlier stores: instruction elaboration sees
an arbitrary memory and proved load equations, rather than reducing hash maps. -/
private theorem scratch_copy (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec) (hs : Separated s)
    (hz : ZeroWords s.dmem s.regs.rsp.toBitVec) (P : MachineState → Prop)
    (hp : Eventually (step e) P (copyReady s, base + 7720)) :
    Eventually (step e) P (s, base + 2987) := by
  have ho := hs.outputHigh
  have hsp := hs.stackHigh
  have hsep := hs.disjoint
  uint_tail_store 92 at 8 width 8 using hc mapped hm
  uint_tail_store 93 at 16 width 8 using hc mapped hm
  uint_tail_zero_load 94 at 120 using hc word hz
  uint_tail_zero_load 95 at 128 using hc word hz
  uint_tail_store 96 at 24 width 8 using hc mapped hm
  uint_tail_store 97 at 32 width 8 using hc mapped hm
  uint_tail_zero_load 98 at 136 using hc word hz
  uint_tail_store 99 at 40 width 8 using hc mapped hm
  uint_tail_zero_load 100 at 144 using hc word hz
  uint_tail_store 101 at 48 width 8 using hc mapped hm
  uint_tail_zero_load 102 at 152 using hc word hz
  uint_tail_store 103 at 56 width 8 using hc mapped hm
  uint_tail_zero_load 104 at 160 using hc word hz
  uint_tail_store 105 at 64 width 8 using hc mapped hm
  uint_width_step 106 using hc
  uint_tail_store 216 at 72 width 4 using hc mapped hm
  uint_tail_store 217 at 0 width 8 using hc mapped hm
  simpa [copyReady, scratchCopyMem] using hp

/-- Real local stores initialize all six words before their actual loads copy
them into the error result. There is no zero-initialization precondition. -/
theorem scratch_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Mapped s.dmem s.regs.rdi.toBitVec)
    (ha : ActivationMapped s.dmem s.regs.rsp.toBitVec) (hs : Separated s)
    (P : MachineState → Prop)
    (hp : Eventually (step e) P (scratchReady s, base + 7720)) :
    Eventually (step e) P (s, base + 2918) := by
  apply scratch_zero e base hc s ha P
  refine scratch_copy e base hc
    {s with dmem := zeroMem s.dmem s.regs.rsp.toBitVec}
    ?_ ⟨hs.outputHigh, hs.stackHigh, hs.disjoint⟩ ?_ P ?_
  · unfold zeroMem
    repeat' first | exact hm | apply mapped_store
  · intro offset hi
    exact zero_mem_load s.dmem s.regs.rsp.toBitVec hs.stackHigh offset hi
  · simpa only [copyReady, scratchReady] using hp

end SszX86.UintCodec.Tail
