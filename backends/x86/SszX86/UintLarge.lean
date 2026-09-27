import SszX86.UintLimbMemory
import SszArena

namespace SszX86.UintCodec.Large
open Kraken.X64.Parser
open SszNative WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "limb_run " pc:num " using " hc:term : tactic => `(tactic|
  (refine instruction_cps _ _ $hc $pc (by decide) _ 0#8
     (by intro h; omega) _ ?_
   intro limbFlags
   simp only [instruction, next, put, putF, compare, get,
     Reg64s.set64, Reg64s.get64, subFlags_cf, subFlags_zf]))

def byteState (s : MachineData) (byte : BitVec 8) (flags : StatusFlags) : MachineData :=
  let word := byte.setWidth 64 <<< shift s
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (get s .rax + 1#64)
      rcx := UInt64.ofBitVec (get s .rcx + 8#64)
      r12 := UInt64.ofBitVec (get s .r12 ||| word)
      r13 := UInt64.ofBitVec word
      r15 := UInt64.ofBitVec (get s .r15 - 1#64)}
    status := flags}

/-- One actual byte iteration: CMP/JAE, MOVZX, SHL, OR, ADD, INC,
DEC/JNE. The bounds-panic edge is impossible from the unsigned source bound. -/
theorem byte_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (byte : BitVec 8)
    (hb : (get s .rax).toNat < (get s .rsi).toNat)
    (hl : Mem.loadInt s.dmem (get s .rdx + get s .rax) 1 = some (byte.toNat : Int))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (byteState s byte flags, if get s .r15 = 1#64 then base + 5622 else base + 5696)) :
    Eventually (step e) P (s, base + 5696) := by
  simp only [get, Reg64s.get64] at hb
  limb_run 5696 using hc
  limb_run 5699 using hc
  try simp only [hb, decide_true, ↓reduceIte]
  refine instruction_cps e base hc 5705 (by decide) _ byte ?_ P ?_
  · intro _
    exact hl
  intro flags
  simp only [instruction, next, put, Reg64s.set64]
  limb_run 5710 using hc
  limb_run 5713 using hc
  limb_run 5716 using hc
  limb_run 5720 using hc
  limb_run 5723 using hc
  limb_run 5726 using hc
  by_cases hz : get s .r15 = 1#64
  · simp only [get, Reg64s.get64] at hz
    simp only [hz, beq_self_eq_true, ↓reduceIte]
    limb_run 5728 using hc
    simpa [byteState, shift, get, Reg64s.get64, hz] using hp _
  · simp only [get, Reg64s.get64] at hz
    simp only [beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true, ↓reduceIte]
    simpa [byteState, shift, get, Reg64s.get64, hz] using hp _

/-- This state names real register contents at the inner-loop invariant. -/
def innerState (s : MachineData) (data : Ssz.Bytes) (start chunk j : Nat)
    (last : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rax := UInt64.ofBitVec (BitVec.ofNat 64 (start + j))
      rcx := UInt64.ofBitVec (BitVec.ofNat 64 (8 * j))
      r12 := UInt64.ofBitVec (packPrefix data start j)
      r13 := UInt64.ofBitVec last
      r15 := UInt64.ofBitVec (BitVec.ofNat 64 (chunk - j))}
    status := flags}

private theorem inner_shift (s : MachineData) (data : Ssz.Bytes)
    (start chunk j : Nat) (last : BitVec 64) (flags : StatusFlags) (hj : j < 8) :
    shift (innerState s data start chunk j last flags) = 8 * j := by
  simp only [shift, innerState, get, Reg64s.get64,
    BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64), BitVec.toNat_ofNat]
  have h8 : 8 * j < 64 := by omega
  have h256 : 8 * j < 256 := by omega
  rw [Nat.mod_eq_of_lt h256]
  exact Nat.and_two_pow_sub_one_eq_mod (8 * j) 6 |>.trans (Nat.mod_eq_of_lt h8)

private theorem byte_inner (s : MachineData) (data : Ssz.Bytes)
    (start chunk j : Nat) (last : BitVec 64) (flags flags' : StatusFlags)
    (hj : j < chunk) (hc : chunk ≤ 8) :
    byteState (innerState s data start chunk j last flags)
      (data[start + j]?.getD 0).toBitVec flags' =
      innerState s data start chunk (j + 1)
        (BitVec.ofNat 64 (data[start + j]?.getD 0).toNat <<< (8 * j)) flags' := by
  have hs := inner_shift s data start chunk j last flags (by omega)
  have hsub : BitVec.ofNat 64 (chunk - j) - 1#64 =
      BitVec.ofNat 64 (chunk - (j + 1)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le (chunk - j) 1 (by decide) (by omega)]
    congr 1
  have hbyte : (data[start + j]?.getD 0).toBitVec.setWidth 64 =
      BitVec.ofNat 64 (data[start + j]?.getD 0).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  unfold byteState
  rw [hs]
  simp [innerState, get, Reg64s.get64, hsub, hbyte,
    packPrefix, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_add,
    BitVec.add_assoc]

/-- Induction is over all remaining bytes, not an unrolled bounded test universe.
Every recursive edge is discharged by the actual byte instruction certificate. -/
theorem inner_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (start chunk : Nat)
    (hs : BytesAt s.dmem (get s .rdx) data)
    (hlen : get s .rsi = BitVec.ofNat 64 data.size)
    (hsize : data.size < 2^63) (hrange : start + chunk ≤ data.size)
    (hchunk : chunk ≤ 8) (P : MachineState → Prop)
    (hp : ∀ last flags, Eventually (step e) P
      (innerState s data start chunk chunk last flags, base + 5622)) :
    ∀ j, j < chunk → ∀ last flags, Eventually (step e) P
      (innerState s data start chunk j last flags, base + 5696) := by
  intro j
  induction hrem : chunk - j using Nat.strongRecOn generalizing j with
  | ind rem ih =>
    intro hj last flags
    let byte := (data[start + j]?.getD 0).toBitVec
    have hidx : start + j < data.size := by omega
    have hb : start + j < 2^64 := by omega
    apply byte_cps e base hc _ byte
    · change (BitVec.ofNat 64 (start + j)).toNat < (get s .rsi).toNat
      rw [hlen]
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (show data.size < 2^64 by omega)] using hidx
    · exact hs (start + j) hidx
    intro flags'
    rw [byte_inner s data start chunk j last flags flags' hj hchunk]
    have he : get (innerState s data start chunk j last flags) .r15 = 1#64 ↔
        j + 1 = chunk := by
      simp only [innerState, get, Reg64s.get64]
      constructor
      · intro h
        have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat] at hn
        have hc8 : chunk - j < 2^64 := by omega
        rw [Nat.mod_eq_of_lt hc8] at hn
        omega
      · intro h
        have hsub : chunk - j = 1 := by omega
        simp [hsub]
    by_cases hend : j + 1 = chunk
    · simp only [he.mpr hend, ↓reduceIte]
      simpa only [hend] using hp _ flags'
    · simp only [show ¬ get (innerState s data start chunk j last flags) .r15 = 1#64
        from fun h => hend (he.mp h), ↓reduceIte]
      exact ih (chunk - (j + 1)) (by omega) (j + 1) rfl (by omega) _ flags'

/-- The head's current byte count is positive, so CMP count,8*index cannot
reach the zero-limb block. Both real NOPs execute before the first byte. -/
theorem head_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (count index : Nat)
    (hcount : count < 2^63) (hi : 8 * index < count)
    (hb : get s .rbx = BitVec.ofNat 64 (count - 8 * index))
    (hpCount : get s .rbp = BitVec.ofNat 64 count)
    (hindex : get s .r14 = BitVec.ofNat 64 index)
    (hstart : get s .r11 = BitVec.ofNat 64 (8 * index))
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (innerState s data (8 * index) (min (count - 8 * index) 8) 0
        (get s .r13) flags, base + 5696)) :
    Eventually (step e) P (s, base + 5647) := by
  have hb64 : count - 8 * index < 2^64 := by omega
  have hcount64 : count < 2^64 := by omega
  have hstart64 : 8 * index < 2^64 := by omega
  have hne : BitVec.ofNat 64 count ≠ BitVec.ofNat 64 (8 * index) := by
    intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount64,
      Nat.mod_eq_of_lt hstart64] at hn
    omega
  have hmin : (if (BitVec.ofNat 64 (count - 8 * index)).toNat < 8 then
      BitVec.ofNat 64 (count - 8 * index) else 8#64) =
      BitVec.ofNat 64 (min (count - 8 * index) 8) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
    split <;> rename_i h
    · rw [Nat.min_eq_left (by omega)]
    · rw [Nat.min_eq_right (by omega)]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hmin
  limb_run 5647 using hc
  limb_run 5651 using hc
  limb_run 5657 using hc
  limb_run 5661 using hc
  limb_run 5669 using hc
  limb_run 5672 using hc
  simp only [get, Reg64s.get64] at hb hpCount hindex hstart
  simp only [hpCount, hindex, ← BitVec.ofNat_mul, Nat.mul_comm index 8,
    beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]
  limb_run 5674 using hc
  limb_run 5677 using hc
  limb_run 5679 using hc
  limb_run 5682 using hc
  limb_run 5692 using hc
  simpa [innerState, get, Reg64s.get64, hb, hstart, hmin,
    packPrefix, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] using hp _

/-- Exactly the registers and SIMD state preserved by Large filling. -/
structure Fixed (s t : MachineData) : Prop where
  rdx : t.regs.rdx = s.regs.rdx
  rsi : t.regs.rsi = s.regs.rsi
  rbp : t.regs.rbp = s.regs.rbp
  r8 : t.regs.r8 = s.regs.r8
  r9 : t.regs.r9 = s.regs.r9
  r10 : t.regs.r10 = s.regs.r10
  rdi : t.regs.rdi = s.regs.rdi
  rsp : t.regs.rsp = s.regs.rsp
  zmms : t.zmms = s.zmms

theorem Fixed.refl (s : MachineData) : Fixed s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Fixed.trans {s t u : MachineData} (h : Fixed s t) (h' : Fixed t u) :
    Fixed s u :=
  ⟨h'.rdx.trans h.rdx, h'.rsi.trans h.rsi, h'.rbp.trans h.rbp,
   h'.r8.trans h.r8, h'.r9.trans h.r9, h'.r10.trans h.r10,
   h'.rdi.trans h.rdi, h'.rsp.trans h.rsp, h'.zmms.trans h.zmms⟩

private theorem add_negative_eight (x : BitVec 64) :
    x + BitVec.ofInt 64 (-8) = x - 8#64 := by
  bv_omega

private def tailValue (s : MachineData) (bx : BitVec 64) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rbx := UInt64.ofBitVec bx
      r11 := UInt64.ofBitVec (get s .r11 + 8#64)
      r14 := UInt64.ofBitVec (get s .r14 + 1#64)}
    dmem := Mem.storeInt s.dmem (get s .r9 + get s .r14 * 8#64) 8 (get s .r12).toInt
    status := flags}

def tailState (s : MachineData) (flags : StatusFlags) : MachineData :=
  tailValue s (get s .rbx - 8#64) flags

private def advanceState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      r11 := UInt64.ofBitVec (get s .r11 + 8#64)
      r14 := UInt64.ofBitVec (get s .r14 + 1#64)}
    status := flags}

/-- Check the outer-loop control suffix with a symbolic input state. This cut
keeps the preceding negative immediate out of its interpreter proof term. -/
private theorem advance_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (advanceState s flags,
        if get s .r14 = get s .r10 then base + 5502 else base + 5647)) :
    Eventually (step e) P (s, base + 5630) := by
  limb_run 5630 using hc
  limb_run 5634 using hc
  limb_run 5637 using hc
  limb_run 5641 using hc
  by_cases he : s.regs.r14.toBitVec = s.regs.r10.toBitVec
  all_goals simpa [advanceState, get, Reg64s.get64, he, beq_iff_eq] using hp _

/-- Abstract the written RBX value before composing native blocks. The only
extra premise is its arithmetic equality, not an execution or memory effect. -/
private theorem tail_value_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old : Int)
    (hm : Mem.loadInt s.dmem (get s .r9 + get s .r14 * 8#64) 8 = some old)
    (bx : BitVec 64) (hv : get s .rbx + BitVec.ofInt 64 (-8) = bx)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (tailValue s bx flags,
        if get s .r14 = get s .r10 then base + 5502 else base + 5647)) :
    Eventually (step e) P (s, base + 5622) := by
  let stored : MachineData := {s with
    dmem := Mem.storeInt s.dmem (get s .r9 + get s .r14 * 8#64) 8 (get s .r12).toInt}
  apply store_cps e base hc s old hm
  change Eventually (step e) P (stored, base + 5626)
  refine instruction_cps e base hc 5626 (by decide) stored 0#8
    (by intro h; omega) P ?_
  intro addFlags
  change Eventually (step e) P
    (putF stored .rbx (get s .rbx + BitVec.ofInt 64 (-8)) addFlags, base + 5630)
  rw [hv]
  apply advance_cps e base hc
  intro flags
  by_cases he : s.regs.r14.toBitVec = s.regs.r10.toBitVec
  all_goals
    simpa (config := {instances := true})
      [advanceState, tailValue, stored, putF, put, get,
       Reg64s.set64, Reg64s.get64, he] using hp flags

/-- Store, two ADDs, CMP, flag-preserving LEA, and JE to the native exit. -/
theorem tail_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old : Int)
    (hm : Mem.loadInt s.dmem (get s .r9 + get s .r14 * 8#64) 8 = some old)
    (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      (tailState s flags, if get s .r14 = get s .r10 then base + 5502 else base + 5647)) :
    Eventually (step e) P (s, base + 5622) := by
  exact tail_value_cps e base hc s old hm (get s .rbx - 8#64)
    (add_negative_eight _) P hp

private theorem fixed_inner (s : MachineData) (data : Ssz.Bytes)
    (start chunk j : Nat) (last : BitVec 64) (flags : StatusFlags) :
    Fixed s (innerState s data start chunk j last flags) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fixed_tail (s : MachineData) (flags : StatusFlags) :
    Fixed s (tailState s flags) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem decode_cons (data : Ssz.Bytes) (start count : Nat) (h : 0 < count) :
    decodeWords data start count =
      packPrefix data start (min count 8) ::
        decodeWords data (start + min count 8) (count - min count 8) := by
  conv =>
    lhs
    rw [decodeWords]
  simp only [show count ≠ 0 by omega, ↓reduceIte]

/-- All outer iterations, with exact memory rather than an abstract loop
execution premise. The induction decreases the number of unconsumed bytes. -/
theorem loop_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (data : Ssz.Bytes) (count : Nat) (hcount : 0 < count)
    (hsize : data.size < 2^63) (hdata : count ≤ data.size)
    (P : MachineState → Prop) :
    ∀ index (s : MachineData),
    8 * index < count →
    get s .rbx = BitVec.ofNat 64 (count - 8 * index) →
    get s .rbp = BitVec.ofNat 64 count →
    get s .r14 = BitVec.ofNat 64 index →
    get s .r11 = BitVec.ofNat 64 (8 * index) →
    get s .r10 = BitVec.ofNat 64 ((count + 7) / 8 - 1) →
    get s .rsi = BitVec.ofNat 64 data.size →
    BytesAt s.dmem (get s .rdx) data →
    Mapped s.dmem (get s .r9) (8 * ((count + 7) / 8)) →
    Disjoint (get s .rdx) (get s .r9) data.size (8 * ((count + 7) / 8)) →
    (∀ t, Fixed s t →
      t.dmem = fillMem s.dmem (get s .r9) index
        (decodeWords data (8 * index) (count - 8 * index)) →
      Eventually (step e) P (t, base + 5502)) →
    Eventually (step e) P (s, base + 5647) := by
  intro index
  induction hrem : count - 8 * index using Nat.strongRecOn generalizing index with
  | ind rem ih =>
    intro s hi hbx hbp hindex hstart hlimit hlen hsource hmap hdis hp
    rw [← hrem] at hbx hp
    let chunk := min (count - 8 * index) 8
    have hchunk : chunk ≤ 8 := Nat.min_le_right _ _
    have hchunkpos : 0 < chunk := by dsimp [chunk]; omega
    have hiw : index < (count + 7) / 8 := by omega
    have hw64 : (count + 7) / 8 < 2^64 := by omega
    have hcb : count < 2^63 := by omega
    apply head_cps e base hc s data count index hcb hi hbx hbp hindex hstart
    intro flags
    refine inner_cps e base hc s data (8 * index) chunk hsource hlen hsize
      (by dsimp [chunk]; omega) hchunk P ?_ 0 hchunkpos (get s .r13) flags
    · intro last flags'
      let packed := innerState s data (8 * index) chunk chunk last flags'
      have haddr : get packed .r9 + get packed .r14 * 8#64 =
          get s .r9 + BitVec.ofNat 64 (8 * index) := by
        simp only [packed, innerState, get, Reg64s.get64] at hindex ⊢
        rw [hindex, ← BitVec.ofNat_mul, Nat.mul_comm index 8]
      obtain ⟨old, hold⟩ := mapped_load s.dmem (get s .r9)
        (8 * ((count + 7) / 8)) (8 * index) 8 hmap (by omega)
      apply tail_cps e base hc packed old
      · rw [haddr]
        simpa only [packed, innerState] using hold
      intro flags''
      let t := tailState packed flags''
      have hfixed : Fixed s t :=
        (fixed_inner s data _ _ _ _ _).trans (fixed_tail packed flags'')
      have hm : t.dmem = Mem.storeInt s.dmem
          (get s .r9 + BitVec.ofNat 64 (8 * index)) 8
          (packPrefix data (8 * index) chunk).toInt := by
        dsimp only [t, tailState, tailValue]
        rw [haddr]
        simp only [packed, innerState, get, Reg64s.get64]
      have hbranch : get packed .r14 = get packed .r10 ↔
          count - 8 * index ≤ 8 := by
        change get s .r14 = get s .r10 ↔ _
        rw [hindex, hlimit]
        constructor
        · intro he
          have hn := congrArg BitVec.toNat he
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show index < 2^64 by omega),
            Nat.mod_eq_of_lt (show (count + 7) / 8 - 1 < 2^64 by omega)] at hn
          omega
        · intro he
          congr 1
          omega
      by_cases hlast : count - 8 * index ≤ 8
      · simp only [hbranch.mpr hlast, ↓reduceIte]
        apply hp t hfixed
        have hch : chunk = count - 8 * index := Nat.min_eq_left hlast
        rw [decode_cons data (8 * index) (count - 8 * index) (by omega)]
        change t.dmem = fillMem s.dmem (get s .r9) index
          (packPrefix data (8 * index) chunk ::
            decodeWords data (8 * index + chunk) (count - 8 * index - chunk))
        simp only [hch, Nat.sub_self, decodeWords, ↓reduceIte, fillMem]
        simpa only [hch] using hm
      · have hnot : ¬ get packed .r14 = get packed .r10 :=
          fun h => hlast (hbranch.mp h)
        simp only [hnot, ↓reduceIte]
        have hch : chunk = 8 := Nat.min_eq_right (by omega)
        have hn : 8 * (index + 1) < count := by omega
        apply ih (count - 8 * (index + 1)) (by omega) (index + 1) rfl t hn
        · change get s .rbx - 8#64 = _
          rw [hbx]
          have he : count - 8 * (index + 1) = (count - 8 * index) - 8 := by omega
          rw [he]
          exact BitVec.ofNat_sub_ofNat_of_le (count - 8 * index) 8 (by decide) (by omega)
        · exact hbp
        · change get s .r14 + 1#64 = _
          rw [hindex, BitVec.ofNat_add]
        · change get s .r11 + 8#64 = _
          rw [hstart]
          simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
        · exact hlimit
        · exact hlen
        · change BytesAt t.dmem (get s .rdx) data
          rw [hm]
          exact bytes_store s.dmem (get s .rdx) (get s .r9) data
            (8 * ((count + 7) / 8)) index _ hsource hdis (by omega)
        · change Mapped t.dmem (get s .r9) _
          rw [hm]
          exact mapped_store _ _ _ _ _ _ hmap
        · exact hdis
        · intro u htu hum
          apply hp u (hfixed.trans htu)
          rw [hum]
          change fillMem t.dmem (get s .r9) (index + 1)
            (decodeWords data (8 * (index + 1)) (count - 8 * (index + 1))) = _
          rw [decode_cons data (8 * index) (count - 8 * index) (by omega)]
          rw [show min (count - 8 * index) 8 = 8 from hch]
          change fillMem t.dmem (get s .r9) (index + 1)
            (decodeWords data (8 * (index + 1)) (count - 8 * (index + 1))) =
            fillMem (Mem.storeInt s.dmem (get s .r9 + BitVec.ofNat 64 (8 * index))
              8 (packPrefix data (8 * index) 8).toInt) (get s .r9) (index + 1)
              (decodeWords data (8 * index + 8) (count - 8 * index - 8))
          rw [hm, hch]
          congr 2 <;> omega

/-- Caller-owned source and destination at the Large fill entry. No allocator,
store-effect equation, or execution assumption is part of this precondition. -/
structure Ready (s : MachineData) (data : Ssz.Bytes) (count : Nat) : Prop where
  large : 9 ≤ count
  count_le : count ≤ data.size
  size_lt : data.size < 2^63
  length : get s .rsi = BitVec.ofNat 64 data.size
  count_rbx : get s .rbx = BitVec.ofNat 64 count
  count_rbp : get s .rbp = BitVec.ofNat 64 count
  words : get s .r8 = BitVec.ofNat 64 (Arena.wordsForBytes count)
  limit : get s .r10 = BitVec.ofNat 64 (Arena.wordsForBytes count - 1)
  offset : get s .r11 = 0#64
  index : get s .r14 = 0#64
  pointer_nonzero : 0 < (get s .r9).toNat
  pointer_aligned : (get s .r9).toNat % 8 = 0
  source_bound : (get s .rdx).toNat + data.size ≤ 2^64
  destination_bound : (get s .r9).toNat + 8 * Arena.wordsForBytes count ≤ 2^64
  source : BytesAt s.dmem (get s .rdx) data
  destination : Mapped s.dmem (get s .r9) (8 * Arena.wordsForBytes count)
  disjoint : Disjoint (get s .rdx) (get s .r9) data.size (8 * Arena.wordsForBytes count)

/-- The actual native exit, its intact descriptor registers, exact arbitrary-
length words, unchanged source, and every caller byte outside the destination. -/
structure Result (base : Int64) (s : MachineData) (data : Ssz.Bytes) (count : Nat)
    (st : MachineState) : Prop where
  pc : st.2 = base + 5502
  fixed : Fixed s st.1
  pointer : get st.1 .r9 = get s .r9
  words : get st.1 .r8 = BitVec.ofNat 64 (Arena.wordsForBytes count)
  contents : NatMemory.wordsAt (widthLoad st.1.dmem) (get s .r9).toNat
    (decodeWords data 0 count)
  source : BytesAt st.1.dmem (get s .rdx) data
  frame : ∀ address, (∀ j < 8 * Arena.wordsForBytes count,
      address ≠ get s .r9 + BitVec.ofNat 64 j) →
    st.1.dmem.get? address = s.dmem.get? address

/-- Complete Large filling of any selected nonempty prefix of at least nine
bytes. All ISA undefined flag choices are included in `Eventually`. -/
theorem fills (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (count : Nat) (h : Ready s data count) :
    Eventually (step e) (Result base s data count) (s, base + 5647) := by
  apply loop_cps e base hc data count (by have := h.large; omega)
    h.size_lt h.count_le (Result base s data count) 0 s
  · have := h.large
    omega
  · simpa using h.count_rbx
  · exact h.count_rbp
  · exact h.index
  · exact h.offset
  · simpa only [Arena.wordsForBytes_eq] using h.limit
  · exact h.length
  · exact h.source
  · simpa only [Arena.wordsForBytes_eq] using h.destination
  · simpa only [Arena.wordsForBytes_eq] using h.disjoint
  · intro t hf hm
    simp only [Nat.mul_zero, Nat.sub_zero] at hm
    apply Eventually.done
    refine ⟨rfl, hf, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg UInt64.toBitVec hf.r9
    · exact (congrArg UInt64.toBitVec hf.r8).trans h.words
    · rw [hm]
      apply fill_wordsAt
      simpa only [decodeWords_length, ← Arena.wordsForBytes_eq] using h.destination_bound
    · rw [hm]
      apply fill_bytes _ _ _ _ 0 (8 * Arena.wordsForBytes count) _ h.source h.disjoint
      simp only [Nat.zero_add, decodeWords_length, Arena.wordsForBytes_eq]
      exact Nat.le_refl _
    · intro address ha
      rw [hm]
      apply fill_frame
      intro j _ hj
      apply ha j
      simpa only [Nat.zero_add, decodeWords_length, ← Arena.wordsForBytes_eq] using hj

/-- The selected prefix equals the full integer only under the trimming
relation. Arbitrary truncated `count` is deliberately not given this claim. -/
theorem fills_significant (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (count : Nat) (h : Ready s data count)
    (hcount : count = significantBytes data data.size) :
    Eventually (step e)
      (fun st => Result base s data count st ∧
        Limbs.value (decodeWords data 0 count) = Ssz.readUint data 0 data.size)
      (s, base + 5647) := by
  apply eventually_weaken _ _ _ _ _ (fills e base hc s data count h)
  intro st hst
  refine ⟨hst, ?_⟩
  rw [decodeWords_value, hcount, readUint_significantBytes]

end SszX86.UintCodec.Large
