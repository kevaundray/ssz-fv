import SszX86.CodecStorage

set_option autoImplicit false

namespace SszX86.Codec
open SszNative UintCodec

theorem FieldsAt.cons {m : DataMem} {r : Footprint} {p : BitVec 64}
    {name : String} {desc : SszNative.Codec.Desc} {rest : List (String × SszNative.Codec.Desc)}
    (h : FieldsAt m r p ((name, desc) :: rest)) :
    ∃ child : BitVec 64, LoadAt m r (p + 16) 8 (child.toNat : Int) ∧
      DescAt m r child desc ∧ FieldsAt m r (p + 24) rest := by
  cases h with
  | fieldsCons span nameSlice nameBytes pointer child rest => exact ⟨_, pointer, child, rest⟩

theorem VariantsAt.cons {m : DataMem} {r : Footprint} {p : BitVec 64}
    {selector : NatOperand} {desc : SszNative.Codec.Desc}
    {rest : List (NatOperand × SszNative.Codec.Desc)}
    (h : VariantsAt m r p ((selector, desc) :: rest)) :
    ∃ child : BitVec 64, LoadAt m r p 8 (child.toNat : Int) ∧ NatAt m r (p + 8) selector ∧
      DescAt m r child desc ∧ VariantsAt m r (p + 24) rest := by
  cases h with
  | variantsCons span pointer selector child rest => exact ⟨_, pointer, selector, child, rest⟩

theorem DescAt.vector {m : DataMem} {r : Footprint} {p : BitVec 64}
    {desc : SszNative.Codec.Desc} {length : NatOperand}
    (h : DescAt m r p (.vector desc length)) :
    ∃ child : BitVec 64, LoadAt m r (p + 24) 8 (child.toNat : Int) ∧ DescAt m r child desc := by
  cases h with
  | descVector header length pointer child => exact ⟨_, pointer, child⟩

theorem DescAt.vector_length {m : DataMem} {r : Footprint} {p : BitVec 64}
    {desc : SszNative.Codec.Desc} {length : NatOperand}
    (h : DescAt m r p (.vector desc length)) : NatAt m r (p + 8) length := by
  cases h with
  | descVector header length pointer child => exact length

theorem DescAt.list {m : DataMem} {r : Footprint} {p : BitVec 64}
    {desc : SszNative.Codec.Desc} {limit : NatOperand}
    (h : DescAt m r p (.list desc limit)) :
    ∃ child : BitVec 64, LoadAt m r (p + 24) 8 (child.toNat : Int) ∧ NatAt m r (p + 8) limit ∧
      DescAt m r child desc := by
  cases h with
  | descList header limit pointer child => exact ⟨_, pointer, limit, child⟩

theorem DescAt.progressiveList {m : DataMem} {r : Footprint} {p : BitVec 64}
    {desc : SszNative.Codec.Desc} {limit : Option NatOperand}
    (h : DescAt m r p (.progressiveList desc limit)) :
    ∃ child : BitVec 64, LoadAt m r (p + 8) 8 (child.toNat : Int) ∧ OptionNatAt m r (p + 16) limit ∧
      DescAt m r child desc := by
  cases h with
  | descProgressiveList header pointer limit child => exact ⟨_, pointer, limit, child⟩

theorem DescAt.container {m : DataMem} {r : Footprint} {p : BitVec 64}
    {fields : List (String × SszNative.Codec.Desc)} (h : DescAt m r p (.container fields)) :
    ∃ buffer, SliceAt m r (p + 8) buffer fields.length 24 8 ∧ FieldsAt m r buffer fields := by
  cases h with
  | descContainer header slice fields => exact ⟨_, slice, fields⟩

theorem DescAt.progressiveContainer {m : DataMem} {r : Footprint} {p : BitVec 64}
    {active : List Bool} {fields : List (String × SszNative.Codec.Desc)}
    (h : DescAt m r p (.progressiveContainer active fields)) :
    ∃ buffer, SliceAt m r (p + 24) buffer fields.length 24 8 ∧ FieldsAt m r buffer fields := by
  cases h with
  | descProgressiveContainer header activeSlice active slice fields => exact ⟨_, slice, fields⟩

theorem DescAt.compatibleUnion {m : DataMem} {r : Footprint} {p : BitVec 64}
    {variants : List (NatOperand × SszNative.Codec.Desc)}
    (h : DescAt m r p (.compatibleUnion variants)) :
    ∃ buffer, SliceAt m r (p + 8) buffer variants.length 24 8 ∧ VariantsAt m r buffer variants := by
  cases h with
  | descCompatibleUnion header slice variants => exact ⟨_, slice, variants⟩

theorem ValueAt.seq {m : DataMem} {r : Footprint} {p : BitVec 64}
    {values : List SszNative.Codec.Value} (h : ValueAt m r p (.seq values)) :
    ∃ buffer, SliceAt m r (p + 8) buffer values.length 48 16 ∧ ValuesAt m r buffer values := by
  cases h with
  | valueSeq header slice values => exact ⟨_, slice, values⟩

theorem ValueAt.union {m : DataMem} {r : Footprint} {p : BitVec 64}
    {selector : NatOperand} {value : SszNative.Codec.Value}
    (h : ValueAt m r p (.union selector value)) :
    ∃ child : BitVec 64, NatAt m r (p + 8) selector ∧ LoadAt m r (p + 24) 8 (child.toNat : Int) ∧
      ValueAt m r child value := by
  cases h with
  | valueUnion header selector pointer child => exact ⟨_, selector, pointer, child⟩

end SszX86.Codec
