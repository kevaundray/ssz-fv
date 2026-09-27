import SszX86.UintByteOps

namespace SszX86.UintCodec.Small
open Kraken.X64.Parser
open SszNative.WordDecode

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- The native group deliberately destroys RBX/R14/R15 and advances RDX.
RDI, RSP, RSI, R12, R13, the whole vector file and every memory byte survive.
In particular all saved callee registers and the return address on the stack
remain available to the already checked common epilogue. -/
def Frame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .rbp →
    r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r14 → r ≠ .r15 →
    t.regs.get64 r = s.regs.get64 r

theorem Frame.refl (s : MachineData) : Frame s s :=
  ⟨rfl, rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem Frame.trans {s t u : MachineData} (h : Frame s t) (g : Frame t u) : Frame s u := by
  refine ⟨g.1.trans h.1, g.2.1.trans h.2.1, ?_⟩
  intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact (g.2.2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11).trans
    (h.2.2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

theorem Frame.rdi {s t : MachineData} (h : Frame s t) : t.regs.rdi = s.regs.rdi := by
  apply UInt64.toBitVec_inj.1
  exact h.2.2 .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem Frame.rsp {s t : MachineData} (h : Frame s t) : t.regs.rsp = s.regs.rsp := by
  apply UInt64.toBitVec_inj.1
  exact h.2.2 .rsp (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- This is ordinary mapped memory, not a hypothesis about instruction effects. -/
def BytesAt (s : MachineData) (data : Ssz.Bytes) : Prop :=
  ∀ i, i < data.size →
    Mem.loadInt s.dmem (s.regs.rdx.toBitVec + BitVec.ofNat 64 i) 1 =
      some ((data[i]?.getD 0).toNat : Int)

/-- RAX is the pre-decrement byte count; R10 is decremented first. -/
def scanState (s : MachineData) (n : Nat) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat n, r10 := UInt64.ofNat n}, status := flags}

def emptyState (s : MachineData) (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with rax := 0, r10 := UInt64.ofBitVec (-1#64)}, status := flags}

macro "uint_small_simp" : tactic => `(tactic|
  simp (config := {instances := true})
    [instruction, next, put, putF, get, compare, shift, low8, low32,
     replace8, scanState, emptyState, Reg64s.get64, Reg64s.set64,
     StatusFlags.from_result, BitVec.take, BitVec.drop, BitVec.replaceLow,
     BitVec.add_assoc, UInt64.toBitVec_ofNat'])

/-- One continuation binder per real instruction, not one copy per AF/OF choice. -/
macro "uint_small_op " pc:num " using " hc:term : tactic => `(tactic|
  (refine instruction_cps _ _ $hc $pc (by decide) _ 0#8 (by simp [loads]) _ ?_
   intro flags
   uint_small_simp))

macro "uint_small_byte " pc:num " at " i:term " in " data:term
    " using " hc:term " reads " hm:term : tactic => `(tactic|
  (refine instruction_cps _ _ $hc $pc (by decide) _ (($data)[$i]?.getD 0).toBitVec ?_ _ ?_
   · intro _
     simpa [address, get, scanState, emptyState, put, putF, compare,
       Reg64s.get64, Reg64s.set64, BitVec.add_assoc] using $hm
   intro flags
   uint_small_simp))

/-- Arbitrary-length descending trim. The all-zero case includes the last SUB
and its taken borrow branch; no byte at index -1 is ever read. -/
theorem trim_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (hb : data.size < 2^63)
    (hm : BytesAt s data) (P : MachineState → Prop) :
    ∀ n, n ≤ data.size → ∀ flags,
    (significantBytes data n = 0 → ∀ flags,
      Eventually (step e) P (emptyState s flags, base + 5499)) →
    (0 < significantBytes data n → ∀ flags,
      Eventually (step e) P
        (scanState s (significantBytes data n - 1) flags, base + 2820)) →
    Eventually (step e) P (scanState s n flags, base + 2800) := by
  intro n
  induction n with
  | zero =>
    intro hn flags hz hnz
    uint_small_op 2800 using hc
    uint_small_op 2804 using hc
    simpa [emptyState, scanState] using hz rfl (subFlags 0#64 1#64)
  | succ n ih =>
    intro hn flags hz hnz
    have hn64 : n + 1 < 2^64 := by omega
    have hmod : (n + 1) % 2^64 = n + 1 := Nat.mod_eq_of_lt hn64
    have hsub : BitVec.ofNat 64 (n+1) - 1#64 = BitVec.ofNat 64 n := by bv_omega
    uint_small_op 2800 using hc
    try simp only [hsub]
    uint_small_op 2804 using hc
    simp [hmod]
    refine instruction_cps e base hc 2810 (by decide) _ (data[n]?.getD 0).toBitVec ?_ P ?_
    · intro _
      simpa [address, get, scanState, put, compare, Reg64s.get64, Reg64s.set64,
        UInt64.toBitVec_ofNat', ← BitVec.add_assoc, BitVec.add_sub_cancel]
        using hm n (by omega)
    · intro fl
      uint_small_simp
      uint_small_op 2815 using hc
      uint_small_op 2818 using hc
      by_cases hzbyte : data[n]?.getD 0 = 0
      · simp [hzbyte]
        apply ih (by omega)
        · intro he fl'
          exact hz (by simpa [significantBytes, hzbyte] using he) fl'
        · intro he fl'
          simpa [significantBytes, hzbyte] using hnz
            (by simpa [significantBytes, hzbyte] using he) fl'
      · have hnzbits : (data[n]?.getD 0).toBitVec ≠ 0#8 := by
          intro he
          apply hzbyte
          apply UInt8.toBitVec_inj.1
          simpa using he
        simp [hnzbits]
        simpa (config := {instances := true})
          [significantBytes, hzbyte, scanState, UInt64.instOfNat] using hnz
          (by simp [significantBytes, hzbyte]) (subFlags (data[n]?.getD 0).toBitVec 0#8)

macro "uint_small_group_setup " hc:term : tactic => `(tactic|
  (uint_small_op 5354 using $hc
   uint_small_op 5357 using $hc
   uint_small_op 5361 using $hc
   uint_small_op 5364 using $hc
   uint_small_op 5367 using $hc))

/-- The linked four-byte group, including the partial AL write, all four shifts,
R11's bit-position update, and the actual loop CMP/JNE. -/
macro "uint_small_group " j:num " in " data:term " using " hc:term
    " reads " hm:term : tactic => `(tactic|
  (uint_small_byte 5370 at $j in $data using $hc reads ($hm $j (by omega))
   uint_small_op 5375 using $hc
   uint_small_op 5378 using $hc
   uint_small_op 5380 using $hc
   uint_small_op 5382 using $hc
   uint_small_byte 5385 at ($j + 1) in $data using $hc reads ($hm ($j + 1) (by omega))
   uint_small_op 5391 using $hc
   uint_small_op 5394 using $hc
   uint_small_op 5397 using $hc
   uint_small_byte 5400 at ($j + 2) in $data using $hc reads ($hm ($j + 2) (by omega))
   uint_small_op 5406 using $hc
   uint_small_op 5409 using $hc
   uint_small_op 5412 using $hc
   uint_small_op 5415 using $hc
   uint_small_byte 5418 at ($j + 3) in $data using $hc reads ($hm ($j + 3) (by omega))
   uint_small_op 5424 using $hc
   uint_small_op 5426 using $hc
   uint_small_op 5428 using $hc
   uint_small_op 5431 using $hc
   uint_small_op 5435 using $hc
   uint_small_op 5438 using $hc
   uint_small_op 5442 using $hc
   uint_small_op 5445 using $hc))

macro "uint_small_tail_setup " hc:term : tactic => `(tactic|
  (uint_small_op 5450 using $hc
   uint_small_op 5454 using $hc
   uint_small_op 5456 using $hc
   uint_small_op 5460 using $hc
   uint_small_op 5463 using $hc
   uint_small_op 5466 using $hc))

/-- The linked single-byte tail, including its partial CL write and INC. -/
macro "uint_small_tail " j:num " in " data:term " using " hc:term
    " reads " hm:term : tactic => `(tactic|
  (uint_small_byte 5468 at $j in $data using $hc reads ($hm $j (by omega))
   uint_small_op 5473 using $hc
   uint_small_op 5476 using $hc
   uint_small_op 5479 using $hc
   uint_small_op 5482 using $hc
   uint_small_op 5485 using $hc
   uint_small_op 5488 using $hc
   uint_small_op 5492 using $hc
   uint_small_op 5495 using $hc))

private theorem byte_word (b : UInt8) : b.toBitVec.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]

private theorem or_left_comm (a b c : BitVec 64) :
    a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [← BitVec.or_assoc, BitVec.or_comm a b, BitVec.or_assoc]

macro "uint_small_packed " hp:term : tactic => `(tactic|
  (apply $hp
   · refine ⟨rfl, rfl, ?_⟩
     intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
     cases r <;> simp_all [Reg64s.get64]
   · rfl
   · simp [packPrefix, byte_word, BitVec.or_assoc, BitVec.or_comm, or_left_comm]))

/-- Each fixed-count trace is checked separately; the public theorem below
dispatches to these certificates without expanding eight ISA traces at once. -/
private def PackCase (count : Nat) : Prop :=
  ∀ (e : Executable) (base : Int64), CodeAt e base →
  ∀ (s : MachineData) (data : Ssz.Bytes), count ≤ data.size → BytesAt s data →
  ∀ (P : MachineState → Prop),
    (∀ t, Frame s t → t.regs.r9 = 0 →
      t.regs.r8.toBitVec = packPrefix data 0 count →
      Eventually (step e) P (t, base + 5502)) →
    Eventually (step e) P
      ({s with regs := {s.regs with rbp := UInt64.ofNat count}}, base + 2830)

private theorem pack1 : PackCase 1 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_op 2840 using hc
  uint_small_op 2843 using hc
  uint_small_op 2846 using hc
  uint_small_tail_setup hc
  uint_small_tail 0 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack2 : PackCase 2 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_op 2840 using hc
  uint_small_op 2843 using hc
  uint_small_op 2846 using hc
  uint_small_tail_setup hc
  uint_small_tail 0 in data using hc reads hm
  uint_small_tail 1 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack3 : PackCase 3 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_op 2840 using hc
  uint_small_op 2843 using hc
  uint_small_op 2846 using hc
  uint_small_tail_setup hc
  uint_small_tail 0 in data using hc reads hm
  uint_small_tail 1 in data using hc reads hm
  uint_small_tail 2 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack4 : PackCase 4 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_group_setup hc
  uint_small_group 0 in data using hc reads hm
  uint_small_op 5447 using hc
  uint_small_op 5450 using hc
  uint_small_op 5454 using hc
  uint_small_op 5499 using hc
  uint_small_packed hp

private theorem pack5 : PackCase 5 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_group_setup hc
  uint_small_group 0 in data using hc reads hm
  uint_small_op 5447 using hc
  uint_small_tail_setup hc
  uint_small_tail 4 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack6 : PackCase 6 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_group_setup hc
  uint_small_group 0 in data using hc reads hm
  uint_small_op 5447 using hc
  uint_small_tail_setup hc
  uint_small_tail 4 in data using hc reads hm
  uint_small_tail 5 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack7 : PackCase 7 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_group_setup hc
  uint_small_group 0 in data using hc reads hm
  uint_small_op 5447 using hc
  uint_small_tail_setup hc
  uint_small_tail 4 in data using hc reads hm
  uint_small_tail 5 in data using hc reads hm
  uint_small_tail 6 in data using hc reads hm
  uint_small_op 5497 using hc
  uint_small_packed hp

private theorem pack8 : PackCase 8 := by
  intro e base hc s data hsize hm P hp
  uint_small_op 2830 using hc
  uint_small_op 2834 using hc
  uint_small_group_setup hc
  uint_small_group 0 in data using hc reads hm
  uint_small_group 4 in data using hc reads hm
  uint_small_op 5447 using hc
  uint_small_op 5450 using hc
  uint_small_op 5454 using hc
  uint_small_op 5499 using hc
  uint_small_packed hp

/-- All eight nonempty Small cases. The input array is NOT restricted to eight
bytes: only the count surviving the unbounded trim is at most eight. The traces
use the real group once for 4--7, twice for 8, and its real 0--3-byte tail. -/
theorem pack_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes) (count : Nat)
    (hpos : 0 < count) (hsmall : count ≤ 8) (hsize : count ≤ data.size)
    (hbp : s.regs.rbp.toBitVec = BitVec.ofNat 64 count)
    (hm : BytesAt s data) (P : MachineState → Prop)
    (hp : ∀ t, Frame s t → t.regs.r9 = 0 →
      t.regs.r8.toBitVec = packPrefix data 0 count →
      Eventually (step e) P (t, base + 5502)) :
    Eventually (step e) P (s, base + 2830) := by
  have hreg : UInt64.ofNat count = s.regs.rbp := by
    apply UInt64.toBitVec_inj.1
    simpa only [UInt64.toBitVec_ofNat'] using hbp.symm
  suffices run : Eventually (step e) P
      ({s with regs := {s.regs with rbp := UInt64.ofNat count}}, base + 2830) by
    simpa only [hreg] using run
  have hcases : count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 ∨
      count = 5 ∨ count = 6 ∨ count = 7 ∨ count = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pack1 e base hc s data hsize hm P hp
  · exact pack2 e base hc s data hsize hm P hp
  · exact pack3 e base hc s data hsize hm P hp
  · exact pack4 e base hc s data hsize hm P hp
  · exact pack5 e base hc s data hsize hm P hp
  · exact pack6 e base hc s data hsize hm P hp
  · exact pack7 e base hc s data hsize hm P hp
  · exact pack8 e base hc s data hsize hm P hp

/-- The exact two exits, selected iff by the significant byte count. Success is
stopped BEFORE the first result store. The Large exit is .LBB93_130 at 2896,
BEFORE its SHR and any arena access. Its input/arena arguments are intact. -/
def Post (s : MachineData) (data : Ssz.Bytes) (base : Int64) (st : MachineState) : Prop :=
  Frame s st.1 ∧
  if significantBytes data data.size ≤ 8 then
    st.2 = base + 5502 ∧ st.1.regs.r9 = 0 ∧
      st.1.regs.r8.toNat = Ssz.readUint data 0 data.size
  else
    st.2 = base + 2896 ∧
      st.1.regs.r10.toNat = significantBytes data data.size - 1 ∧
      st.1.regs.rbp.toNat = significantBytes data data.size ∧
      st.1.regs.rdx = s.regs.rdx ∧ st.1.regs.r14 = s.regs.r14 ∧
      st.1.regs.rbx = s.regs.rbx

private theorem exits_ne (base : Int64) : base + 5502 ≠ base + 2896 := by
  intro he
  have h := congrArg (fun p : Int64 => p - base) he
  simp only [Int64.add_comm base 5502, Int64.add_comm base 2896,
    Int64.add_sub_cancel] at h
  exact (show (5502 : Int64) ≠ 2896 by decide) h

/-- Both directions of both exit characterizations, including all-zero arrays. -/
theorem Post.outcomes (s : MachineData) (data : Ssz.Bytes) (base : Int64)
    (st : MachineState) (h : Post s data base st) :
    (st.2 = base + 5502 ↔ significantBytes data data.size ≤ 8) ∧
    (st.2 = base + 2896 ↔ 9 ≤ significantBytes data data.size) := by
  rcases h with ⟨_, h⟩
  by_cases hs : significantBytes data data.size ≤ 8
  · simp only [hs, ↓reduceIte] at h
    refine ⟨⟨fun _ => hs, fun _ => h.1⟩, ⟨?_, ?_⟩⟩
    · intro he
      exact False.elim (exits_ne base (h.1.symm.trans he))
    · intro hl
      omega
  · simp only [hs, ↓reduceIte] at h
    refine ⟨⟨?_, ?_⟩, ⟨fun _ => by omega, fun _ => h.1⟩⟩
    · intro he
      exact False.elim (exits_ne base (he.symm.trans h.1))
    · intro he
      exact False.elim (hs he)

/-- Complete finite execution from the width check's successful fallthrough.
There is no restriction on the number of high zero bytes and no mapping or
separation requirement on the output, arena or stack: this path does not access
them. The numeric result always denotes the ENTIRE original upstream array. -/
theorem trim_and_pack (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes)
    (ha : s.regs.rax = s.regs.r14) (ht : s.regs.r10 = s.regs.r14)
    (hz : s.regs.r8 = 0) (hlen : data.size = s.regs.r14.toNat)
    (hb : data.size < 2^63)
    (_hrange : s.regs.rdx.toNat + data.size ≤ 2^64)
    (hm : BytesAt s data) :
    Eventually (step e) (Post s data base) (s, base + 2800) := by
  have hcount := significantBytes_le data data.size
  have hcount64 : significantBytes data data.size < 2^64 := by omega
  have hrax : UInt64.ofNat data.size = s.regs.rax := by rw [ha, hlen]; simp
  have hr10 : UInt64.ofNat data.size = s.regs.r10 := by rw [ht, hlen]; simp
  have hstart : scanState s data.size s.status = s := by
    have hregs : {s.regs with rax := UInt64.ofNat data.size, r10 := UInt64.ofNat data.size} = s.regs := by
      calc
        _ = {s.regs with rax := s.regs.rax, r10 := UInt64.ofNat data.size} := by rw [hrax]
        _ = {s.regs with rax := s.regs.rax, r10 := s.regs.r10} := by rw [hr10]
        _ = s.regs := by cases s.regs; rfl
    simp only [scanState, hregs]
  suffices run : Eventually (step e) (Post s data base)
      (scanState s data.size s.status, base + 2800) by
    simpa only [hstart] using run
  apply trim_cps e base hc s data hb hm (Post s data base) data.size (Nat.le_refl _)
  · intro hzero flags
    uint_small_op 5499 using hc
    apply Eventually.done
    refine ⟨?_, ?_⟩
    · refine ⟨rfl, rfl, ?_⟩
      intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      cases r <;> simp_all [Reg64s.get64]
    · have hvalue := readUint_significantBytes data data.size
      simp only [hzero, Ssz.readUint] at hvalue
      simp [hzero, hz, hvalue.symm]
  · intro hpos flags
    have hpred : significantBytes data data.size - 1 + 1 = significantBytes data data.size := by omega
    have hlea : BitVec.ofNat 64 (significantBytes data data.size - 1) + 1#64 =
        BitVec.ofNat 64 (significantBytes data data.size) := by
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) hpred
    uint_small_op 2820 using hc
    try simp only [hlea]
    uint_small_op 2824 using hc
    uint_small_op 2828 using hc
    by_cases hsmall : significantBytes data data.size ≤ 8
    · simp [hpred, Nat.mod_eq_of_lt hcount64, show significantBytes data data.size < 9 by omega]
      apply pack_cps e base hc _ data (significantBytes data data.size) hpos hsmall hcount
      · simp (config := {instances := true})
          [UInt64.instOfNat, UInt64.toBitVec_ofNat', hlea]
      · simpa [BytesAt] using hm
      · intro t hf hr9 hr8
        apply Eventually.done
        refine ⟨?_, ?_⟩
        · apply Frame.trans (t := _) ?_ hf
          refine ⟨rfl, rfl, ?_⟩
          intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
          cases r <;> simp_all [Reg64s.get64]
        · simp only [hsmall, ↓reduceIte]
          refine ⟨True.intro, hr9, ?_⟩
          change t.regs.r8.toBitVec.toNat = _
          rw [hr8, packPrefix_toNat data 0 _ hsmall, readUint_significantBytes]
    · simp [hpred, Nat.mod_eq_of_lt hcount64, show ¬ significantBytes data data.size < 9 by omega]
      apply Eventually.done
      refine ⟨?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        cases r <;> simp_all [Reg64s.get64]
      · simp (config := {instances := true})
          [hsmall, UInt64.instOfNat, hpred, Nat.mod_eq_of_lt hcount64,
           Nat.mod_eq_of_lt (show significantBytes data data.size - 1 < 2^64 by omega)]

/-- Compositional form: every actual undefined-flag path reaches one of the two
contract exits, after which an arbitrary client continuation may execute. -/
theorem trim_and_pack_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (data : Ssz.Bytes)
    (ha : s.regs.rax = s.regs.r14) (ht : s.regs.r10 = s.regs.r14)
    (hz : s.regs.r8 = 0) (hlen : data.size = s.regs.r14.toNat)
    (hb : data.size < 2^63) (hrange : s.regs.rdx.toNat + data.size ≤ 2^64)
    (hm : BytesAt s data) (P : MachineState → Prop)
    (hp : ∀ t, Post s data base t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 2800) := by
  exact eventually_trans _ _ _ _
    (trim_and_pack e base hc s data ha ht hz hlen hb hrange hm) hp

end SszX86.UintCodec.Small
