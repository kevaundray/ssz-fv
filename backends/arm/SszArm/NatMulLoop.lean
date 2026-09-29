import SszArm.NatMulLoopRows
import SszArm.NatMulReserve
import SszArm.NatMulContract
import SszArm.NatAddLargeCorrectMemory

namespace SszArm.NatMul

open SszNative (NatOperand NatArithmetic)
open NatCompare (Words)
open UintCodec (widthLoad)
open Delimited (Protected MemoryFrame)

abbrev loopChanged : List (BitVec 5) :=
  [0#5, 1#5, 8#5, 9#5, 10#5, 11#5, 12#5, 13#5, 14#5, 15#5, 16#5, 17#5, 18#5]

/-- Ownership at the successful reservation checkpoint. It protects the complete
original raw extents, never just significant prefixes. The output is the actual
new allocation; no disjointness from the already-used arena prefix is required.
SP is after the 96-byte save, so its 48-byte body region fits the entry 144. -/
structure LoopEntryOwned (s : ArmState) (left right : NatOperand) (arena : BitVec 64) : Prop where
  space : LoopSpace (r (.GPR 31#5) s) (r (.GPR 20#5) s) (left.wordCount + right.wordCount)
  leftAt : left.At (widthLoad s)
  rightAt : right.At (widthLoad s)
  leftOwned : NatAdd.OperandOwned
    (loopWrites (r (.GPR 31#5) s) (r (.GPR 20#5) s) (left.wordCount + right.wordCount)) left
  rightOwned : NatAdd.OperandOwned
    (loopWrites (r (.GPR 31#5) s) (r (.GPR 20#5) s) (left.wordCount + right.wordCount)) right
  arenaPhysical : arena.toNat + 24 ≤ 2^64
  arenaOwned : Protected
    (loopWrites (r (.GPR 31#5) s) (r (.GPR 20#5) s) (left.wordCount + right.wordCount)) arena.toNat 24
  leftPointer : r (.GPR 26#5) s = left.pointer
  leftPayload : r (.GPR 28#5) s = left.payload
  rightPointer : r (.GPR 27#5) s = right.pointer
  leftCount : r (.GPR 21#5) s = BitVec.ofNat 64 left.wordCount
  rightCount : r (.GPR 22#5) s = BitVec.ofNat 64 right.wordCount
  width : r (.GPR 25#5) s = BitVec.ofNat 64 right.wordCount
  normalization : r (.GPR 23#5) s = BitVec.ofNat 64 (left.wordCount + right.wordCount - 1)

private theorem loop_owned_operand (s : ArmState) (dst : BitVec 64) (count : Nat)
    (operand : NatOperand) (stack : 48 ≤ (r (.GPR 31#5) s).toNat)
    (input : operand.At (widthLoad s))
    (owned : NatAdd.OperandOwned (loopWrites (r (.GPR 31#5) s) dst count) operand) :
    NatCompare.Operand s operand.pointer operand.payload operand.words := by
  cases operand with
  | small word => exact Or.inl ⟨rfl, rfl⟩
  | large pointer words =>
    rcases input with ⟨positive, alignment, physical, limbs⟩
    have nonnull : pointer ≠ 0#64 := by intro h; simp [h] at positive
    have lengthBound : words.length < 2^64 := by omega
    refine Or.inr ⟨nonnull, ?_, ⟨by omega, physical, ?_⟩, ?_⟩
    · simp [NatOperand.payload, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound]
    · by_cases empty : words = []
      · exact Or.inl empty
      · right
        rcases owned with zero | separate
        · have := List.length_pos.mpr empty; omega
        · have apart := separate ((r (.GPR 31#5) s).toNat - 48, 48) (by simp [loopWrites])
          simp only [Prod.fst, Prod.snd] at apart
          omega
    · intro i
      apply BitVec.eq_of_toNat_eq
      have value := Option.some.inj (limbs i)
      simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using value

private theorem loop_owned_protected (writes : List Delimited.Span) (operand : NatOperand)
    (owned : NatAdd.OperandOwned writes operand) (nonnull : operand.pointer ≠ 0#64) :
    Protected writes operand.pointer.toNat (8 * operand.words.length) := by
  cases operand with
  | small word => exact False.elim (nonnull rfl)
  | large pointer words => exact owned

/-- All observations needed by the original normalization entry. `written`
contains even a zero high limb; normalization is a separate subsequent phase. -/
structure LoopReady (s t : ArmState) (base arena : BitVec 64)
    (left right : NatOperand) (reservation : SszNative.Arena.Reservation) : Prop where
  pc : read_pc t = base + 1060#64
  error : read_err t = .None
  stable : LoopStable loopChanged s t
  words : Words t (r (.GPR 20#5) s) (SszNative.NatMul.writtenWords left right)
  written : NatAdd.WrittenAt (widthLoad t)
    (NatArithmetic.committed reservation (SszNative.NatMul.writtenWords left right))
  memory : MemoryFrame
    (loopWrites (r (.GPR 31#5) s) (r (.GPR 20#5) s) (left.wordCount + right.wordCount)) s t
  left : NatAdd.OperandPreserved s t left
  right : NatAdd.OperandPreserved s t right
  arenaBase : read_mem_bytes 8 arena t = read_mem_bytes 8 arena s
  arenaCapacity : read_mem_bytes 8 (arena + 8#64) t = read_mem_bytes 8 (arena + 8#64) s
  arenaCursor : read_mem_bytes 8 (arena + 16#64) t = read_mem_bytes 8 (arena + 16#64) s
  pointer : (r (.GPR 20#5) t).toNat = reservation.pointer
  total : (r (.GPR 19#5) t).toNat = left.wordCount + right.wordCount
  normalization : r (.GPR 23#5) t = BitVec.ofNat 64 (left.wordCount + right.wordCount - 1)
  result : r (.GPR 24#5) t = r (.GPR 24#5) s
  row : r (.GPR 12#5) t = BitVec.ofNat 64 left.wordCount
  rowPointer : r (.GPR 11#5) t = r (.GPR 20#5) s + BitVec.ofNat 64 (8 * left.wordCount)

/-- Actual main multiplication +580..+1012, through its executed branch to
+1060. The current zero-filled buffer comes only from ReserveReady, whose
producer executes the shipped memset. Both inductions are unrestricted Nat/List
inductions. Machine nonwrapping inequalities follow from owned physical spans. -/
theorem reservation_loop_runs (before s : ArmState) (base arena : BitVec 64)
    (left right : NatOperand) (reservation : SszNative.Arena.Reservation)
    (code : CodeAt s base) (aligned : CheckSPAlignment s)
    (ready : ReserveReady before s base reservation (left.wordCount + right.wordCount))
    (owned : LoopEntryOwned s left right arena)
    (leftLarge : 1 < left.wordCount) (rightLarge : 1 < right.wordCount) :
    ∃ fuel t, run fuel s = t ∧ LoopReady s t base arena left right reservation := by
  let sp := r (.GPR 31#5) s
  let dst := r (.GPR 20#5) s
  let rightWords := right.words.take right.wordCount
  let leftWords := left.words.take left.wordCount
  have leftFits := SszNative.Limbs.sigWords_le_length left.words
  have rightFits := SszNative.Limbs.sigWords_le_length right.words
  have leftLength : leftWords.length = left.wordCount := by
    simp only [leftWords, List.length_take, Nat.min_eq_left leftFits]
  have rightLength : rightWords.length = right.wordCount := by
    simp only [rightWords, List.length_take, Nat.min_eq_left rightFits]
  have leftOperand := loop_owned_operand s dst (left.wordCount + right.wordCount) left
    owned.space.stack owned.leftAt owned.leftOwned
  have rightOperand := loop_owned_operand s dst (left.wordCount + right.wordCount) right
    owned.space.stack owned.rightAt owned.rightOwned
  have rightNonzero : right.pointer ≠ 0#64 := by
    intro null
    have single := rightOperand.small null
    have length : right.words.length = 1 := by simp [single]
    have small : right.wordCount ≤ 1 := by
      change SszNative.Limbs.sigWords right.words ≤ 1
      omega
    omega
  obtain ⟨rightPayload, source, sourceRaw⟩ := rightOperand.large rightNonzero
  have sourcePhysical : right.pointer.toNat + 8 * rightWords.length ≤ 2^64 := by
    have physical := source.2.1
    rw [rightLength]
    omega
  have rawRightOwned := loop_owned_protected _ right owned.rightOwned rightNonzero
  have sourceOwned : Protected (loopWrites sp dst (left.wordCount + rightWords.length))
      right.pointer.toNat (8 * rightWords.length) := by
    rw [rightLength]
    rcases rawRightOwned with empty | separate
    · omega
    · right
      intro span member
      have apart := separate span member
      omega
  have leftProtected : left.pointer ≠ 0#64 →
      Protected (loopWrites sp dst (left.wordCount + rightWords.length)) left.pointer.toNat (8 * left.words.length) := by
    rw [rightLength]
    exact loop_owned_protected _ left owned.leftOwned
  let u := loopInit base s
  have runU : run 5 s = u := loop_init_run s base code ready.error aligned ready.pc
  have uf := loop_init_stable s base
  have um := loop_init_memory s base
  have uv := loop_init_values s base ready.pc
  have uLeft : NatCompare.Operand u left.pointer left.payload left.words := by
    apply loop_operand_preserve (writes := []) (s := s)
    · intro a outside; exact congrFun um a
    · exact uf.sp
    · intro nonnull; right; simp
    · exact leftOperand
  have uRight : Words u right.pointer rightWords := by
    intro i
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp um]
    exact words_take sourceRaw right.wordCount i
  have uZero : Words u dst (currentWords [] (List.replicate (left.wordCount + rightWords.length) 0#64)) := by
    rw [rightLength]
    intro i
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp um]
    exact ready.zero i
  have factors : ∀ k (hk : k < leftWords.length), leftWords[k] = left.words[0 + k]?.getD 0#64 := by
    intro k hk
    have bound : k < left.words.length := by rw [leftLength] at hk; omega
    simp only [leftWords, List.getElem_take, Nat.zero_add, List.getElem?_eq_getElem bound,
      Option.getD_some]
  have countWord : r (.GPR 19#5) s = BitVec.ofNat 64 (left.wordCount + right.wordCount) := by
    rw [← ready.total, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨rowsFuel, v, runV, vf, vm, vp, vRow, vPointer, vWords⟩ :=
    loop_rows_runs base sp left.pointer left.payload right.pointer dst left.wordCount left.words rightWords
      (by simpa only [rightLength] using owned.space) (by rw [rightLength]; omega)
      sourcePhysical sourceOwned leftProtected leftWords (by rw [leftLength]; omega)
      0 [] (List.replicate (left.wordCount + rightWords.length) 0#64) u
      (by simp [leftLength]) factors (by simp) (by simp)
      (uf.code code) (uf.error.trans ready.error) (uf.aligned aligned) uv.1 uf.sp
      (uv.2.1.trans owned.rightPointer)
      (uv.2.2.1.trans owned.leftPointer)
      (uv.2.2.2.1.trans owned.leftPayload)
      (by simpa only [Nat.mul_zero, BitVec.add_zero] using uv.2.2.2.2.1)
      uv.2.2.2.2.2
      (by rw [uf.registers _ (by decide), rightLength]; exact countWord)
      (uf.registers _ (by decide))
      ((uf.registers _ (by decide)).trans owned.leftCount)
      (by rw [uf.registers _ (by decide), rightLength]; exact owned.rightCount)
      (by rw [uf.registers _ (by decide), rightLength]; exact owned.width)
      uLeft uRight uZero
  let t := w .PC (base + 1060#64) v
  have allV : LoopStable loopChanged s v :=
    (uf.weaken (by intro reg member; simp_all)).trans
      (vf.weaken (by intro reg member; simp_all))
  have runT : run 1 v = t := loop_exit_run v base (allV.code code)
    (allV.error.trans ready.error) (allV.aligned aligned) vp
  have tf : LoopStable loopChanged v t := by constructor <;> simp [t, state_simp_rules]
  have allT := allV.trans tf
  have writtenWords : Words t dst (SszNative.NatMul.writtenWords left right) := by
    rw [SszNative.NatMul.writtenWords_native_loop]
    simpa only [t, read_mem_bytes_of_w, List.nil_append, leftWords, rightWords, rightLength] using vWords
  have finalFrame : MemoryFrame (loopWrites sp dst (left.wordCount + right.wordCount)) s t := by
    intro a outside
    change v.mem a = s.mem a
    exact (vm a (by simpa only [rightLength] using outside)).trans (congrFun um a)
  have arenaRead (offset : Nat) (bound : offset + 8 ≤ 24) :
      read_mem_bytes 8 (arena + BitVec.ofNat 64 offset) t =
        read_mem_bytes 8 (arena + BitVec.ofNat 64 offset) s := by
    apply finalFrame.read
    · have physical := owned.arenaPhysical
      bv_omega
    · have address : (arena + BitVec.ofNat 64 offset).toNat = arena.toNat + offset := by
        have physical := owned.arenaPhysical
        bv_omega
      rw [address]
      exact owned.arenaOwned.subspan offset 8 bound
  refine ⟨5 + rowsFuel + 1, t, by rw [run_plus, run_plus, runU, runV, runT], ?_⟩
  refine ⟨by simp [t, state_simp_rules], allT.error.trans ready.error, allT, writtenWords,
    ?_, finalFrame, NatAdd.operand_preserved finalFrame left owned.leftAt owned.leftOwned,
    NatAdd.operand_preserved finalFrame right owned.rightAt owned.rightOwned,
    ?_, arenaRead 8 (by decide), arenaRead 16 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro allocation allocated
    have same : reservation = allocation := Option.some.inj allocated
    subst allocation
    simpa only [NatArithmetic.committed, ready.pointer] using
      NatAdd.LargeCorrect.words_at t dst (SszNative.NatMul.writtenWords left right) writtenWords
  · simpa using arenaRead 0 (by decide)
  · rw [allT.registers _ (by decide)]; exact ready.pointer
  · rw [allT.registers _ (by decide)]; exact ready.total
  · rw [allT.registers _ (by decide)]; exact owned.normalization
  · exact allT.registers _ (by decide)
  · simpa [t, state_simp_rules] using vRow
  · simpa [t, state_simp_rules] using vPointer

end SszArm.NatMul
