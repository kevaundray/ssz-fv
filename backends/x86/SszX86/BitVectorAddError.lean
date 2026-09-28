import SszX86.BitVectorAddErrorDecode
import SszX86.BitVectorFrame

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

/-- The private error's eight complete words, status, and unspecified padding. -/
structure AddErrorImage where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  reason : BitVec 32
  padding : BitVec 32

def addErrorStageMem (m : DataMem) (sp : BitVec 64) (v : AddErrorImage) : DataMem :=
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 176) 8 v.w7.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 168) 8 v.w6.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 160) 8 v.w5.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 152) 8 v.w4.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 144) 8 v.w3.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 136) 8 v.w2.toInt
  let m := Mem.storeInt m (sp + BitVec.ofNat 64 128) 8 v.w1.toInt
  Mem.storeInt m (sp + BitVec.ofNat 64 120) 8 v.w0.toInt

def addErrorStage (s : MachineData) (v : AddErrorImage) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec v.w6
      rdx := UInt64.ofBitVec v.w5
      rsi := UInt64.ofBitVec v.w4
      rdi := UInt64.ofBitVec v.w3
      r8 := UInt64.ofBitVec v.w2
      r9 := UInt64.ofBitVec v.w0
      r10 := UInt64.ofBitVec v.w1
      r11 := UInt64.ofBitVec (v.padding.setWidth 64)}
    dmem := addErrorStageMem s.dmem s.regs.rsp.toBitVec v}

def addErrorOutputMem (m : DataMem) (out : BitVec 64) (v : AddErrorImage) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 v.w7.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 v.w6.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 v.w5.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 v.w4.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 v.w3.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 v.w2.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 v.w1.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 v.w0.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 v.reason.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 76) 4 v.padding.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def addErrorState (s : MachineData) (out : BitVec 64) (v : AddErrorImage) : MachineData :=
  {addErrorStage s v with
    regs := {(addErrorStage s v).regs with
      rbx := UInt64.ofBitVec v.w7
      r14 := UInt64.ofBitVec out}
    dmem := addErrorOutputMem (addErrorStageMem s.dmem s.regs.rsp.toBitVec v) out v}

theorem error_signed_nat {n : Nat} (v : BitVec n) :
    (v.toInt.take n).toNat = v.toNat := by
  have h := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := v))
  simp only [BitVec.toNat_ofInt] at h
  simpa [Int.take] using h

theorem error_signed_take (v : BitVec 64) :
    v.toInt.take 64 = (v.toNat : Int) := by
  have h := error_signed_nat v
  have nonnegative := Int.emod_nonneg v.toInt (by decide : (2^64 : Int) ≠ 0)
  simp only [Int.take] at h ⊢
  omega

theorem error_local_read (m : DataMem) (sp : BitVec 64)
    (a n b k : Nat) (value : Int) (bound : sp.toNat + 224 ≤ 2^64)
    (ha : a + n ≤ 224) (hb : b + k ≤ 224) (apart : a + n ≤ b ∨ b + k ≤ a) :
    Mem.loadInt (Mem.storeInt m (sp + BitVec.ofNat 64 b) k value)
      (sp + BitVec.ofNat 64 a) n = Mem.loadInt m (sp + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

macro "bitvector_add_load " row:num " using " hc:term " word " hl:term : tactic => `(tactic|
  (bitvector_remaining_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, error_local_read, ($hl), Delimited.word_cast]))

macro "bitvector_add_store " row:num " at " off:num " using " hc:term " mapped " hm:term : tactic => `(tactic|
  (bitvector_remaining_step $row using $hc
   try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
   apply Delimited.store_cps
   · apply Large.mapped_load (capacity := 224) («offset» := $off) («width» := 8)
     · repeat' first | exact $hm | apply Large.mapped_store
     · decide
   simp only [Effects.All]))

/-- Native staging, including the otherwise dead stores at SP136..176. -/
theorem add_error_stage_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (v : AddErrorImage)
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 224)
    (bound : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64)
    (h0 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (v.w0.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (v.w1.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (v.w2.toNat : Int))
    (h3 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 = some (v.w3.toNat : Int))
    (h4 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 48#64) 8 = some (v.w4.toNat : Int))
    (h5 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56#64) 8 = some (v.w5.toNat : Int))
    (h6 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64#64) 8 = some (v.w6.toNat : Int))
    (h7 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 = some (v.w7.toNat : Int))
    (hpadding : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 84#64) 4 = some (v.padding.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorStage s v, base + 1882)) :
    Eventually (step e) P (s, base + 1776) := by
  bitvector_add_load 55 using hc word h7
  bitvector_add_store 56 at 176 using hc mapped hm
  bitvector_add_load 57 using hc word h6
  bitvector_add_store 58 at 168 using hc mapped hm
  bitvector_add_load 59 using hc word h5
  bitvector_add_store 60 at 160 using hc mapped hm
  bitvector_add_load 61 using hc word h4
  bitvector_add_store 62 at 152 using hc mapped hm
  bitvector_add_load 63 using hc word h3
  bitvector_add_store 64 at 144 using hc mapped hm
  bitvector_add_load 65 using hc word h2
  bitvector_add_store 66 at 136 using hc mapped hm
  bitvector_add_load 67 using hc word h0
  bitvector_add_load 68 using hc word h1
  bitvector_add_store 69 at 128 using hc mapped hm
  bitvector_add_store 70 at 120 using hc mapped hm
  bitvector_add_load 71 using hc word hpadding
  simpa only [addErrorStage, addErrorStageMem, UInt64.toBitVec_ofBitVec] using next

def addErrorOutputHigh (s : MachineData) : MachineData :=
  let out := s.regs.r14.toBitVec
  let m := Mem.storeInt s.dmem (out + 64#64) 8 s.regs.rbx.toBitVec.toInt
  let m := Mem.storeInt m (out + 56#64) 8 s.regs.rcx.toBitVec.toInt
  let m := Mem.storeInt m (out + 48#64) 8 s.regs.rdx.toBitVec.toInt
  {s with dmem := Mem.storeInt m (out + 40#64) 8 s.regs.rsi.toBitVec.toInt}

def addErrorOutputLow (s : MachineData) : MachineData :=
  let out := s.regs.r14.toBitVec
  let m := Mem.storeInt s.dmem (out + 32#64) 8 s.regs.rdi.toBitVec.toInt
  let m := Mem.storeInt m (out + 24#64) 8 s.regs.r8.toBitVec.toInt
  let m := Mem.storeInt m (out + 16#64) 8 s.regs.r10.toBitVec.toInt
  let m := Mem.storeInt m (out + 8#64) 8 s.regs.r9.toBitVec.toInt
  let m := Mem.storeInt m (out + 72#64) 4 (s.regs.rax.toBitVec.setWidth 32).toInt
  let m := Mem.storeInt m (out + 76#64) 4 (s.regs.r11.toBitVec.setWidth 32).toInt
  {s with dmem := Mem.storeInt m out 8 1}

theorem add_error_output_high_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem s.regs.r14.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorOutputHigh s, base + 1911)) :
    Eventually (step e) P (s, base + 1895) := by
  bitvector_remaining_output 74 at 64 width 8 using hc mapped hm
  bitvector_remaining_output 75 at 56 width 8 using hc mapped hm
  bitvector_remaining_output 76 at 48 width 8 using hc mapped hm
  bitvector_remaining_output 77 at 40 width 8 using hc mapped hm
  simpa [addErrorOutputHigh, Width.bytes] using next

theorem add_error_output_low_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem s.regs.r14.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorOutputLow s, base + 7720)) :
    Eventually (step e) P (s, base + 1911) := by
  bitvector_remaining_output 78 at 32 width 8 using hc mapped hm
  bitvector_remaining_output 79 at 24 width 8 using hc mapped hm
  bitvector_remaining_output 80 at 16 width 8 using hc mapped hm
  bitvector_remaining_output 81 at 8 width 8 using hc mapped hm
  bitvector_remaining_output 82 at 72 width 4 using hc mapped hm
  bitvector_remaining_output 83 at 76 width 4 using hc mapped hm
  bitvector_remaining_output 84 at 0 width 8 using hc mapped hm
  bitvector_remaining_step 85 using hc
  simpa only [addErrorOutputLow, BitVec.toInt_setWidth, UInt64.toNat_toBitVec,
    show (2^32 : Nat) = 4294967296 by decide] using next

theorem add_error_outputs_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem s.regs.r14.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorOutputLow (addErrorOutputHigh s), base + 7720)) :
    Eventually (step e) P (s, base + 1895) := by
  apply add_error_output_high_cps e base hc s hm P
  apply add_error_output_low_cps e base hc _ _ P next
  dsimp [addErrorOutputHigh]
  repeat' first | exact hm | apply Large.mapped_store

def addErrorLoaded (s : MachineData) (out last : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rbx := UInt64.ofBitVec last, r14 := UInt64.ofBitVec out}}

theorem add_error_reload_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out last : BitVec 64)
    (hlast : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 176#64) 8 = some (last.toNat : Int))
    (houtput : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorLoaded s out last, base + 1895)) :
    Eventually (step e) P (s, base + 1882) := by
  bitvector_remaining_step 72 using hc
  bitvector_load hlast
  bitvector_remaining_step 73 using hc
  bitvector_load houtput
  simpa only [addErrorLoaded] using next

/-- The complete add-failure path, with its original output pointer reloaded. -/
theorem add_error_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (out : BitVec 64) (v : AddErrorImage)
    (hm : Large.Mapped s.dmem s.regs.rsp.toBitVec 224)
    (outputMapped : Large.Mapped s.dmem out 80)
    (bound : s.regs.rsp.toBitVec.toNat + 224 ≤ 2^64)
    (houtput : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int))
    (h0 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 16#64) 8 = some (v.w0.toNat : Int))
    (h1 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 24#64) 8 = some (v.w1.toNat : Int))
    (h2 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 32#64) 8 = some (v.w2.toNat : Int))
    (h3 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 40#64) 8 = some (v.w3.toNat : Int))
    (h4 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 48#64) 8 = some (v.w4.toNat : Int))
    (h5 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 56#64) 8 = some (v.w5.toNat : Int))
    (h6 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 64#64) 8 = some (v.w6.toNat : Int))
    (h7 : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 72#64) 8 = some (v.w7.toNat : Int))
    (hreason : s.regs.rax.toBitVec.setWidth 32 = v.reason)
    (hpadding : Mem.loadInt s.dmem (s.regs.rsp.toBitVec + 84#64) 4 = some (v.padding.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (addErrorState s out v, base + 7720)) :
    Eventually (step e) P (s, base + 1776) := by
  apply add_error_stage_cps e base hc s v hm bound h0 h1 h2 h3 h4 h5 h6 h7 hpadding P
  have stageStack : (addErrorStage s v).regs.rsp = s.regs.rsp := rfl
  have stageOutput : Large.Mapped (addErrorStage s v).dmem out 80 := by
    dsimp [addErrorStage, addErrorStageMem]
    repeat' first | exact outputMapped | apply Large.mapped_store
  have saved : Mem.loadInt (addErrorStage s v).dmem
      (s.regs.rsp.toBitVec + 176#64) 8 = some (v.w7.toNat : Int) := by
    simp (disch := first | assumption | omega | decide) only
      [addErrorStage, addErrorStageMem, error_local_read, load_store_same,
       Nat.reduceMul, error_signed_take]
  have output : Mem.loadInt (addErrorStage s v).dmem
      (s.regs.rsp.toBitVec + 8#64) 8 = some (out.toNat : Int) := by
    simpa (disch := first | assumption | omega | decide) only
      [addErrorStage, addErrorStageMem, error_local_read] using houtput
  apply add_error_reload_cps e base hc (addErrorStage s v) out v.w7
  · simpa only [stageStack] using saved
  · simpa only [stageStack] using output
  apply add_error_outputs_cps e base hc
  · exact stageOutput
  simpa only [addErrorState, addErrorOutputMem, addErrorOutputLow, addErrorOutputHigh,
    addErrorLoaded, addErrorStage, UInt64.toBitVec_ofBitVec,
    BitVec.setWidth_setWidth_of_le v.padding (by decide : 32 ≤ 64),
    BitVec.setWidth_eq, hreason, BitVec.add_zero] using next

theorem add_error_frame (m : DataMem) (sp out a : BitVec 64) (v : AddErrorImage)
    (outsideOutput : ∀ i < 80, a ≠ out + BitVec.ofNat 64 i)
    (outsideStage : ∀ i < 64, a ≠ (sp + 120#64) + BitVec.ofNat 64 i) :
    (addErrorOutputMem (addErrorStageMem m sp v) out v).get? a = m.get? a := by
  have outside : ∀ i, 120 ≤ i → i < 184 → a ≠ sp + BitVec.ofNat 64 i := by
    intro i hlo hhi he
    apply outsideStage (i - 120) (by omega)
    simpa only [memmove_addr_add, show 120 + (i - 120) = i by omega] using he
  simp (disch := first | assumption | omega | decide) only
    [addErrorOutputMem, store_frame (limit := 80)]
  have storeOutside (m' : DataMem) (off count : Nat) (value : Int)
      (hlo : 120 ≤ off) (hhi : off + count ≤ 184) :
      (Mem.storeInt m' (sp + BitVec.ofNat 64 off) count value).get? a = m'.get? a := by
    apply memmove_store_lookup_outside
    intro i hi
    rw [memmove_addr_add]
    apply outside
    · omega
    · simp only [Int.toBytes_length] at hi
      omega
  simp (disch := omega) only [addErrorStageMem, storeOutside]

theorem add_error_observed (m : DataMem) (out : BitVec 64) (v : AddErrorImage)
    (bound : out.toNat + 80 ≤ 2^64) :
    observe (addErrorOutputMem m out v) out 0 8 = some 1 ∧
    observe (addErrorOutputMem m out v) out 8 8 = some v.w0.toNat ∧
    observe (addErrorOutputMem m out v) out 16 8 = some v.w1.toNat ∧
    observe (addErrorOutputMem m out v) out 24 8 = some v.w2.toNat ∧
    observe (addErrorOutputMem m out v) out 32 8 = some v.w3.toNat ∧
    observe (addErrorOutputMem m out v) out 40 8 = some v.w4.toNat ∧
    observe (addErrorOutputMem m out v) out 48 8 = some v.w5.toNat ∧
    observe (addErrorOutputMem m out v) out 56 8 = some v.w6.toNat ∧
    observe (addErrorOutputMem m out v) out 64 8 = some v.w7.toNat ∧
    observe (addErrorOutputMem m out v) out 72 4 = some v.reason.toNat ∧
    observe (addErrorOutputMem m out v) out 76 4 = some v.padding.toNat := by
  simp (disch := first | assumption | omega | decide) only
    [observe, addErrorOutputMem, load_store_offset_disjoint, load_store_same,
     Nat.reduceMul]
  simp only [error_signed_nat, Option.map_some]
  decide

end SszX86.BitVector
