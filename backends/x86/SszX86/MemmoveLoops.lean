import SszX86.MemmoveExec
import SszX86.MemmoveMemory

namespace SszX86

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The register offset is a prefix length in the forward direction and a
one-past remaining-prefix endpoint in the backward direction. -/
def memmovePosition (back : Bool) (n k : Nat) : Nat :=
  if back then n - k else k

def memmoveChunkOffset (back : Bool) (n k c : Nat) : Nat :=
  if back then n - (k + c) else k

def MemmoveImage (back : Bool) (m m0 : DataMem) (dst : BitVec 64)
    (xs : List UInt8) (k : Nat) : Prop :=
  if back then MoveInv m m0 dst xs (xs.length - k) xs.length
  else MoveInv m m0 dst xs 0 k

def MemmoveDirection (back : Bool) (src dst : BitVec 64) : Prop :=
  if back then src.toNat ≤ dst.toNat else dst.toNat ≤ src.toNat

structure MemmoveLoop (back : Bool) (m0 : DataMem) (src dst : BitVec 64)
    (xs : List UInt8) (k : Nat) (s : MachineData) : Prop where
  bounded : k ≤ xs.length
  count : s.regs.rdx.toBitVec = BitVec.ofNat 64 (xs.length - k)
  source : s.regs.rsi.toBitVec = src + BitVec.ofNat 64 (memmovePosition back xs.length k)
  destination : s.regs.rdi.toBitVec = dst + BitVec.ofNat 64 (memmovePosition back xs.length k)
  image : MemmoveImage back s.dmem m0 dst xs k

theorem memmove_advance_position (back : Bool) (p : BitVec 64) (n k c : Nat)
    (hb : n < 2^64) (hk : k + c ≤ n) :
    memmoveAdvance back (p + BitVec.ofNat 64 (memmovePosition back n k)) c =
      p + BitVec.ofNat 64 (memmovePosition back n (k + c)) := by
  cases back
  · simp only [memmoveAdvance, memmovePosition, Bool.false_eq_true, ite_false,
      BitVec.ofNat_add, BitVec.add_assoc]
  · simp only [memmoveAdvance, memmovePosition, ite_true]
    calc
      (p + BitVec.ofNat 64 (n - k)) - BitVec.ofNat 64 c =
          p + (BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 c) := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      _ = p + BitVec.ofNat 64 (n - (k + c)) := by
        rw [BitVec.ofNat_sub_ofNat_of_le (n - k) c (by omega) (by omega),
          Nat.sub_sub]

theorem memmove_addr_position (back : Bool) (p : BitVec 64) (n k c : Nat)
    (hb : n < 2^64) (hk : k + c ≤ n) :
    memmoveAddr back (p + BitVec.ofNat 64 (memmovePosition back n k)) c =
      p + BitVec.ofNat 64 (memmoveChunkOffset back n k c) := by
  cases back
  · rfl
  · exact memmove_advance_position true p n k c hb hk

theorem memmove_chunk (back : Bool) (m0 : DataMem) (src dst : BitVec 64)
    (xs : List UInt8) (k c : Nat) (s : MachineData)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64)
    (hk : k + c ≤ xs.length) (inv : MemmoveLoop back m0 src dst xs k s) :
    let chunk := (xs.drop (memmoveChunkOffset back xs.length k c)).take c
    Mem.loadInt s.dmem (memmoveAddr back s.regs.rsi.toBitVec c) c =
      some (Int.ofBytes chunk) ∧
    (∃ old, Mem.loadInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec c) c = some old) ∧
    MemmoveImage back
      (Mem.storeBytes s.dmem (memmoveAddr back s.regs.rdi.toBitVec c) chunk)
      m0 dst xs (k + c) := by
  dsimp only
  rw [inv.source, inv.destination,
    memmove_addr_position back src xs.length k c hb hk,
    memmove_addr_position back dst xs.length k c hb hk]
  cases back
  · exact memmove_forward_chunk input direction k c hk inv.image
  · exact memmove_backward_chunk input direction k c hk inv.image

theorem memmove_directional_chunk_length (back : Bool) (xs : List UInt8) (k c : Nat)
    (hk : k + c ≤ xs.length) :
    ((xs.drop (memmoveChunkOffset back xs.length k c)).take c).length = c := by
  rw [List.length_take, List.length_drop]
  cases back <;> simp only [memmoveChunkOffset, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem memmoveBulk_loop (back : Bool) (m0 : DataMem) (src dst : BitVec 64)
    (xs : List UInt8) (k : Nat) (s : MachineData)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64)
    (hk : k + 8 ≤ xs.length) (inv : MemmoveLoop back m0 src dst xs k s) :
    let v := Int.ofBytes ((xs.drop (memmoveChunkOffset back xs.length k 8)).take 8)
    Mem.loadInt s.dmem (memmoveAddr back s.regs.rsi.toBitVec 8) 8 = some v ∧
    (∃ old, Mem.loadInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 8) 8 = some old) ∧
    MemmoveLoop back m0 src dst xs (k + 8) (memmoveBulkState back s v) := by
  dsimp only
  obtain ⟨hs, hd, hm⟩ := memmove_chunk back m0 src dst xs k 8 s input direction hb hk inv
  refine ⟨hs, hd, hk, ?_, ?_, ?_, ?_⟩
  · change s.regs.rdx.toBitVec - 8#64 = _
    rw [inv.count, BitVec.ofNat_sub_ofNat_of_le (xs.length - k) 8 (by decide) (by omega)]
    congr 1
  · change memmoveAdvance back s.regs.rsi.toBitVec 8 = _
    rw [inv.source]
    exact memmove_advance_position back src xs.length k 8 hb hk
  · change memmoveAdvance back s.regs.rdi.toBitVec 8 = _
    rw [inv.destination]
    exact memmove_advance_position back dst xs.length k 8 hb hk
  · change MemmoveImage back (Mem.storeInt _ _ _ _) _ _ _ _
    unfold Mem.storeInt
    rw [memcpy_roundtrip 8 _ (memmove_directional_chunk_length back xs k 8 hk)]
    exact hm

theorem memmoveByte_loop (back : Bool) (m0 : DataMem) (src dst : BitVec 64)
    (xs : List UInt8) (k : Nat) (s : MachineData)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64)
    (hk : k + 1 ≤ xs.length) (inv : MemmoveLoop back m0 src dst xs k s) :
    let v := Int.ofBytes ((xs.drop (memmoveChunkOffset back xs.length k 1)).take 1)
    Mem.loadInt s.dmem (memmoveAddr back s.regs.rsi.toBitVec 1) 1 = some v ∧
    (∃ old, Mem.loadInt s.dmem (memmoveAddr back s.regs.rdi.toBitVec 1) 1 = some old) ∧
    MemmoveLoop back m0 src dst xs (k + 1) (memmoveByteState back s v) := by
  dsimp only
  obtain ⟨hs, hd, hm⟩ := memmove_chunk back m0 src dst xs k 1 s input direction hb hk inv
  refine ⟨hs, hd, hk, ?_, ?_, ?_, ?_⟩
  · change s.regs.rdx.toBitVec - 1#64 = _
    rw [inv.count, BitVec.ofNat_sub_ofNat_of_le (xs.length - k) 1 (by decide) (by omega)]
    congr 1
  · change memmoveAdvance back s.regs.rsi.toBitVec 1 = _
    rw [inv.source]
    exact memmove_advance_position back src xs.length k 1 hb hk
  · change memmoveAdvance back s.regs.rdi.toBitVec 1 = _
    rw [inv.destination]
    exact memmove_advance_position back dst xs.length k 1 hb hk
  · change MemmoveImage back (Mem.storeInt _ _ _ _) _ _ _ _
    unfold Mem.storeInt
    rw [memcpy_roundtrip 1 _ (memmove_directional_chunk_length back xs k 1 hk)]
    exact hm

def MemmoveFinal (base : Int64) (back : Bool) (s : MachineData)
    (m0 : DataMem) (dst : BitVec 64) (xs : List UInt8) : MachineState → Prop :=
  fun st => st.2 = memmoveRetPc base back ∧ MemcpyFrame s st.1 ∧
    MoveInv st.1.dmem m0 dst xs 0 xs.length

theorem memmove_final_of_loop (base : Int64) (back : Bool) (m0 : DataMem)
    (src dst : BitVec 64) (xs : List UInt8) (s : MachineData)
    (inv : MemmoveLoop back m0 src dst xs xs.length s) :
    MemmoveFinal base back s m0 dst xs (s, memmoveRetPc base back) := by
  refine ⟨rfl, memcpyFrame_refl s, ?_⟩
  have hm := inv.image
  cases back <;> simpa only [MemmoveImage, Bool.false_eq_true, ite_false, ite_true,
    Nat.sub_self] using hm

theorem memmoveTest_frame (s : MachineData) (af : Bool) :
    MemcpyFrame s (memcpyTestState s af) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r h1 h2 h3 h4 h5
  cases r <;> simp [memcpyTestState, Reg64s.get64]

theorem memmoveCompare_frame (s : MachineData) :
    MemcpyFrame s (memmoveCompareState s) := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩

private theorem final_frame (base : Int64) (back : Bool) (s t : MachineData)
    (m0 : DataMem) (dst : BitVec 64) (xs : List UInt8) (frame : MemcpyFrame s t) :
    ∀ st, MemmoveFinal base back t m0 dst xs st → MemmoveFinal base back s m0 dst xs st := by
  intro st h
  exact ⟨h.1, memcpyFrame_trans frame h.2.1, h.2.2⟩

private theorem memmove_byte_loop (base : Int64) (back : Bool)
    (m0 : DataMem) (src dst : BitVec 64) (xs : List UInt8)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64) :
    ∀ remaining k (s : MachineData), xs.length - k = remaining →
      0 < remaining → MemmoveLoop back m0 src dst xs k s →
      Eventually (memmoveStep base) (MemmoveFinal base back s m0 dst xs)
        (s, memmoveBytePc base back) := by
  intro remaining
  refine Nat.strongRecOn remaining ?_
  intro remaining ih k s hr hpos inv
  have hk : k + 1 ≤ xs.length := by omega
  let v := Int.ofBytes ((xs.drop (memmoveChunkOffset back xs.length k 1)).take 1)
  obtain ⟨hs, ⟨old, hd⟩, inv'⟩ := memmoveByte_loop back m0 src dst xs k s input direction hb hk inv
  have hz : (memmoveByteState back s v).status.zf = decide (remaining = 1) := by
    change (memcpySubFlags s.regs.rdx.toBitVec 1#64).zf = _
    rw [inv.count, hr]
    exact memcpy_zf_sub1 remaining (by omega)
  apply memmove_byte_runs base back s v old _ hs hd
  by_cases hone : remaining = 1
  · have hkfull : k + 1 = xs.length := by omega
    have invfull : MemmoveLoop back m0 src dst xs xs.length (memmoveByteState back s v) := by
      simpa only [hkfull] using inv'
    have hdone := memmove_final_of_loop base back m0 src dst xs (memmoveByteState back s v) invfull
    have hdone' := final_frame base back s (memmoveByteState back s v) m0 dst xs
      (memmoveByte_frame back s v) _ hdone
    simpa [hz, hone] using (Eventually.done _ hdone')
  · have hrec := ih (remaining - 1) (by omega) (k + 1) (memmoveByteState back s v)
      (by omega) (by omega) inv'
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s (memmoveByteState back s v) m0 dst xs (memmoveByte_frame back s v)) hrec
    simpa [hz, hone] using hrec'

private theorem memmove_tail_loop (base : Int64) (back : Bool)
    (m0 : DataMem) (src dst : BitVec 64) (xs : List UInt8)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64)
    (k : Nat) (s : MachineData) (inv : MemmoveLoop back m0 src dst xs k s) :
    Eventually (memmoveStep base) (MemmoveFinal base back s m0 dst xs)
      (s, memmoveTailPc base back) := by
  apply memmove_tail_runs
  intro af
  have invAf : MemmoveLoop back m0 src dst xs k (memcpyTestState s af) :=
    ⟨inv.bounded, inv.count, inv.source, inv.destination, inv.image⟩
  by_cases hk : k = xs.length
  · subst k
    have hz : s.regs.rdx.toBitVec = 0 := by simpa using inv.count
    have hdone := memmove_final_of_loop base back m0 src dst xs (memcpyTestState s af) invAf
    have hdone' := final_frame base back s (memcpyTestState s af) m0 dst xs
      (memmoveTest_frame s af) _ hdone
    simpa [hz] using (Eventually.done _ hdone')
  · have hz : s.regs.rdx.toBitVec ≠ 0 := by
      intro he
      have hn := congrArg BitVec.toNat he
      rw [inv.count, BitVec.toNat_ofNat] at hn
      have hmod : (xs.length - k) % 2^64 = xs.length - k := Nat.mod_eq_of_lt (by omega)
      rw [hmod] at hn
      change xs.length - k = 0 at hn
      have := inv.bounded
      omega
    have hrec := memmove_byte_loop base back m0 src dst xs input direction hb
      (xs.length - k) k (memcpyTestState s af) rfl (by have := inv.bounded; omega) invAf
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s (memcpyTestState s af) m0 dst xs (memmoveTest_frame s af)) hrec
    simpa only [beq_iff_eq, hz, ite_false] using hrec'

private theorem memmove_bulk_loop (base : Int64) (back : Bool)
    (m0 : DataMem) (src dst : BitVec 64) (xs : List UInt8)
    (input : MoveInput m0 src dst xs.length xs)
    (direction : MemmoveDirection back src dst) (hb : xs.length < 2^64) :
    ∀ remaining k (s : MachineData), xs.length - k = remaining →
      8 ≤ remaining → MemmoveLoop back m0 src dst xs k s →
      Eventually (memmoveStep base) (MemmoveFinal base back s m0 dst xs)
        (s, memmoveBulkPc base back) := by
  intro remaining
  refine Nat.strongRecOn remaining ?_
  intro remaining ih k s hr h8 inv
  have hk : k + 8 ≤ xs.length := by omega
  let v := Int.ofBytes ((xs.drop (memmoveChunkOffset back xs.length k 8)).take 8)
  obtain ⟨hs, ⟨old, hd⟩, inv'⟩ := memmoveBulk_loop back m0 src dst xs k s input direction hb hk inv
  have hc : (memmoveBulkState back s v).status.cf = decide (remaining - 8 < 8) := by
    change (memcpySubFlags (memmoveBulkState back s v).regs.rdx.toBitVec 8#64).cf = _
    rw [inv'.count, show xs.length - (k + 8) = remaining - 8 by omega]
    exact memcpy_cf_sub8 (remaining - 8) (by omega)
  apply memmove_bulk_runs base back s v old _ hs hd
  by_cases hsmall : remaining - 8 < 8
  · have hrec := memmove_tail_loop base back m0 src dst xs input direction hb
      (k + 8) (memmoveBulkState back s v) inv'
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s (memmoveBulkState back s v) m0 dst xs (memmoveBulk_frame back s v)) hrec
    simpa only [hc, hsmall, decide_true, ite_true] using hrec'
  · have hrec := ih (remaining - 8) (by omega) (k + 8) (memmoveBulkState back s v)
      (by omega) (by omega) inv'
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s (memmoveBulkState back s v) m0 dst xs (memmoveBulk_frame back s v)) hrec
    simpa [hc, hsmall] using hrec'

/-- Whole directional execution, with an initial-memory image rather than
separated source/destination ownership. The arbitrary caller frame is exact. -/
theorem memmove_direction_runs (base : Int64) (back : Bool) (s : MachineData)
    (xs : List UInt8)
    (input : MoveInput s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs.length xs)
    (direction : MemmoveDirection back s.regs.rsi.toBitVec s.regs.rdi.toBitVec)
    (hcount : s.regs.rdx.toBitVec = BitVec.ofNat 64 xs.length) (hb : xs.length < 2^64) :
    Eventually (memmoveStep base)
      (MemmoveFinal base back s s.dmem s.regs.rdi.toBitVec xs)
      (s, if back then base + 69 else base + 15) := by
  let t := memmovePrepareState back s
  have inv : MemmoveLoop back s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec xs 0 t := by
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · simpa only [t, memmovePrepareState, Nat.sub_zero] using hcount
    · cases back <;> simp [t, memmovePrepareState, memmovePosition, hcount]
    · cases back <;> simp [t, memmovePrepareState, memmovePosition, hcount]
    · cases back
      · exact memmove_init s.dmem s.regs.rdi.toBitVec xs 0 (Nat.zero_le _)
      · simpa only [t, memmovePrepareState, MemmoveImage, ite_true, Nat.sub_zero] using
          memmove_init s.dmem s.regs.rdi.toBitVec xs xs.length (Nat.le_refl _)
  have hc : (memmovePrepareState back s).status.cf = decide (xs.length < 8) := by
    change (memcpySubFlags s.regs.rdx.toBitVec 8#64).cf = _
    rw [hcount]
    exact memcpy_cf_sub8 xs.length hb
  apply memmove_prepare_runs
  by_cases hsmall : xs.length < 8
  · have hrec := memmove_tail_loop base back s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec
      xs input direction hb 0 t inv
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s t s.dmem s.regs.rdi.toBitVec xs (memmove_prepare_frame back s)) hrec
    simpa [t, hc, hsmall] using hrec'
  · have hrec := memmove_bulk_loop base back s.dmem s.regs.rsi.toBitVec s.regs.rdi.toBitVec
      xs input direction hb xs.length 0 t (Nat.sub_zero _) (by omega) inv
    have hrec' := eventually_weaken _ _ _ _
      (final_frame base back s t s.dmem s.regs.rdi.toBitVec xs (memmove_prepare_frame back s)) hrec
    simpa [t, hc, hsmall] using hrec'

end SszX86
