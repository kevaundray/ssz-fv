import SszArm.UintPrepare

namespace SszArm.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def preparedWordCount (s : ArmState) : BitVec 64 := (r (.GPR 8#5) s >>> 3) + 1#64
def preparedByteCount (s : ArmState) : BitVec 64 := preparedWordCount s <<< 3

def prepareTrace (s : ArmState) : List Nat :=
  if preparedByteCount s &&& 9223372036854775808#64 = 0#64
  then [0,1,2,3,4,5,6,10,11,12] else [0,1,2,3,4,5,6,7,8,9]

def prepareSpill (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s

private theorem prepare_spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n*8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem :=
  mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

private theorem prepare_read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m*8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (prepare_spill_mem_w s f v m dst value)) n addr

macro "prepare_normalize" : tactic => `(tactic|
  simp_all (config := {decide := true, instances := true})
    [PrepareFollows, prepareBlock, prepareInstruction, preparedByteCount, preparedWordCount,
     prepareSpill, BoolCodec.StoreOp.effect, Udivti3.put, Udivti3.next, Udivti3.branch,
     state_simp_rules, BitVec.add_assoc, BitVec.sub_add_cancel, prepare_read_spill_w,
     prepare_spill_mem_w, apply_ite])

theorem prepare_trace_length (s : ArmState) : (prepareTrace s).length = 10 := by
  unfold prepareTrace
  split <;> rfl

theorem prepare_trace_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 4764#64) : PrepareFollows base (prepareTrace s) s := by
  unfold prepareTrace
  split <;> prepare_normalize

theorem prepare_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (hp : read_pc s = base + 4764#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 10 s = prepareBlock (prepareTrace s) s := by
  rw [← prepare_trace_length s]
  exact prepare_block_run _ s base hc (prepare_trace_follows s base hp) he ha

theorem prepare_trace_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 4764#64) (hsp : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := prepareBlock (prepareTrace s) s
    read_pc t = (if (preparedByteCount s).toNat < 2^63 then base + 6776#64 else base + 4816#64) ∧
    r (.GPR 11#5) t = r (.GPR 8#5) s >>> 3 ∧
    r (.GPR 10#5) t = preparedWordCount s ∧
    r (.GPR 13#5) t = preparedByteCount s ∧ t.mem = (prepareSpill s).mem := by
  have hz := SszNative.Arena.high_bit_clear (preparedByteCount s)
  unfold prepareTrace
  split <;> prepare_normalize

def PreparePreserved : StateField → Prop
  | .PC => False
  | .GPR reg => reg ≠ 10#5 ∧ reg ≠ 11#5 ∧ reg ≠ 13#5
  | _ => True

instance (f : StateField) : Decidable (PreparePreserved f) := by
  cases f <;> unfold PreparePreserved <;> infer_instance

theorem prepare_trace_field (s : ArmState) (f : StateField) (hf : PreparePreserved f)
    (hsp : 16 ≤ (r (.GPR 31#5) s).toNat) :
    r f (prepareBlock (prepareTrace s) s) = r f s := by
  have hr : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (prepareSpill s) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [prepareSpill] at hr
  unfold prepareTrace
  split
  all_goals
    cases f with
    | PC => exact False.elim hf
    | GPR reg =>
      simp only [PreparePreserved] at hf
      by_cases h31 : reg = 31#5 <;> by_cases h9 : reg = 9#5 <;>
        (try subst reg) <;> prepare_normalize
    | SFP reg => prepare_normalize
    | FLAG flag => prepare_normalize
    | ERR => prepare_normalize

theorem prepared_word_count (s : ArmState) (count : Nat) (hpos : 0 < count)
    (hcount : count < 2^63) (h8 : (r (.GPR 8#5) s).toNat = count - 1) :
    (preparedWordCount s).toNat = SszNative.Arena.wordsForBytes count := by
  simp only [preparedWordCount, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, h8, BitVec.toNat_ofNat]
  simp only [SszNative.Arena.wordsForBytes, show count ≠ 0 by omega, ↓reduceIte]
  omega

theorem prepared_byte_count (s : ArmState) (count : Nat) (hpos : 0 < count)
    (hcount : count < 2^63) (h8 : (r (.GPR 8#5) s).toNat = count - 1) :
    (preparedByteCount s).toNat = 8 * SszNative.Arena.wordsForBytes count := by
  have hw := prepared_word_count s count hpos hcount h8
  have hb := SszNative.Arena.wordsForBytes_bytes_lt count hcount
  simp only [preparedByteCount, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hw]
  omega

end SszArm.UintCodec
