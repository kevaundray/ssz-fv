import SszX86.IndicesElementTypeProofs

namespace SszX86.IndicesElementType
open SszNative UintCodec

/-- Only active fields of freshly constructed primitive results are observed.
The third alternative is the exact full five-word source-to-target copy. -/
def SuccessAt (original final : DataMem) (readonly : Codec.Footprint)
    (out : BitVec 64) (desc : SszNative.Codec.Desc) : Prop :=
  Mem.loadInt final (out + 64#64) 4 = some 0 ∧
    ((desc = .primitive .bool ∧ Mem.loadInt final out 8 = some 0) ∨
     (desc = .primitive (.uint (.small 1)) ∧ Mem.loadInt final out 8 = some 1 ∧
       Mem.loadInt final (out + 8#64) 8 = some 0 ∧
       Mem.loadInt final (out + 16#64) 8 = some 1) ∨
     ∃ pointer words, Codec.DescAt original readonly pointer desc ∧
       DescWords.At words original pointer ∧ DescWords.At words final out)

/-- All Error's active payload words and its native Result reason are retained. -/
def ErrorWordsAt (final : DataMem) (out pointer payload : BitVec 64) (reason : Nat) : Prop :=
  Mem.loadInt final out 8 = some 1 ∧
  Mem.loadInt final (out + 8#64) 8 = some 0 ∧
  Mem.loadInt final (out + 16#64) 8 = some (pointer.toNat : Int) ∧
  Mem.loadInt final (out + 24#64) 8 = some (payload.toNat : Int) ∧
  Mem.loadInt final (out + 32#64) 8 = some 0 ∧
  Mem.loadInt final (out + 40#64) 8 = some 0 ∧
  Mem.loadInt final (out + 48#64) 8 = some 0 ∧
  Mem.loadInt final (out + 56#64) 8 = some 0 ∧
  Mem.loadInt final (out + 64#64) 4 = some (reason : Int)

def ResultAt (original final : DataMem) (readonly : Codec.Footprint)
    (out : BitVec 64) : Except SszNative.Indices.Error SszNative.Codec.Desc → Prop
  | .ok desc => SuccessAt original final readonly out desc
  | .error .notSteppable => ErrorWordsAt final out 0 0 56
  | .error (.noSuchField ordinal) => ErrorWordsAt final out ordinal.pointer ordinal.payload 57
  | .error _ => False

theorem ResultMemory.observed {original final : DataMem} {readonly : Codec.Footprint}
    {out : BitVec 64} {result : Except SszNative.Indices.Error SszNative.Codec.Desc}
    (completed : ResultMemory original readonly out result final) :
    ResultAt original final readonly out result := by
  cases completed with
  | bool =>
    have active := bool_active original out
    exact ⟨active.2, Or.inl ⟨rfl, active.1⟩⟩
  | uint =>
    have active := uint_active original out
    exact ⟨active.2.2.2, Or.inr (Or.inl ⟨rfl, active.1, active.2.1, active.2.2.1⟩)⟩
  | notSteppable => exact error_active original out 0 0 56 (by decide)
  | noSuchField ordinal =>
    exact error_active original out ordinal.pointer ordinal.payload 57 (by decide)
  | copied words desc source =>
    have active := copy_active original out words
    exact ⟨active.2, Or.inr (Or.inr ⟨_, words, desc, source, active.1⟩)⟩

theorem ResultMemory.frame {original final : DataMem} {readonly : Codec.Footprint}
    {out : BitVec 64} {result : Except SszNative.Indices.Error SszNative.Codec.Desc}
    (completed : ResultMemory original readonly out result final) :
    ∃ bytes, bytes ≤ 64 ∧ Codec.MemoryFrame original final (SuccessWrites out bytes) := by
  cases completed with
  | bool => exact ⟨8, by decide, bool_frame original out⟩
  | uint => exact ⟨24, by decide, uint_frame original out⟩
  | notSteppable => exact ⟨64, Nat.le_refl _, error_frame original out 0 0 56⟩
  | noSuchField ordinal =>
    exact ⟨64, Nat.le_refl _, error_frame original out ordinal.pointer ordinal.payload 57⟩
  | copied words _ _ => exact ⟨40, by decide, copy_frame original out words⟩

/-- No byte outside the actual output footprint changes, including all original
readonly aliases and the four opaque trailing bytes of the72-byte Result. -/
theorem Returned.readonly {s : MachineData} {base : Int64} {readonly : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {path : SszNative.Indices.PathStep} {ra : BitVec 64}
    (owned : Owned s base readonly desc path ra)
    {result : Except SszNative.Indices.Error SszNative.Codec.Desc} {t : MachineState}
    (returned : Returned s readonly ra result t) :
    ∀ address, readonly address → t.1.dmem.get? address = s.dmem.get? address := by
  obtain ⟨bytes, bound, frame⟩ := returned.result.frame
  intro address readable
  apply frame address
  intro written
  apply owned.readonly_separate address readable
  rcases written with ⟨i, hi, equal⟩ | shifted
  · exact ⟨i, by omega, equal⟩
  · exact Emit.span_shift s.regs.rdi.toBitVec 64 4 72 (by decide) shifted

/-- Observable public root: original resources imply actual machine return,
active semantic fields, full copied child provenance and readonly preservation. -/
theorem program_observed (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (readonly : Codec.Footprint) (desc : SszNative.Codec.Desc)
    (path : SszNative.Indices.PathStep) (ra : BitVec 64)
    (owned : Owned s base readonly desc path ra) :
    Eventually (step e) (fun t =>
      Returned s readonly ra (SszNative.Indices.elementType desc path) t ∧
      ResultAt s.dmem t.1.dmem readonly s.regs.rdi.toBitVec
        (SszNative.Indices.elementType desc path) ∧
      ∀ address, readonly address → t.1.dmem.get? address = s.dmem.get? address) (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (program_correct e base hc s readonly desc path ra owned)
  intro t returned
  exact ⟨returned, returned.result.observed, returned.readonly owned⟩

end SszX86.IndicesElementType
