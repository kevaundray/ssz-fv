import SszX86.IndicesElementTypeOutput
import SszX86.BitVectorLoad

namespace SszX86.IndicesElementType
open UintCodec

/-- Every word copied by the native descriptor-copy block comes from the
original mapped bytes. This includes arbitrary padding, without interpreting it
as descriptor metadata or selecting a padding value in a public precondition. -/
theorem DescWords.of_mapped (m : DataMem) (pointer : BitVec 64)
    (mapped : Large.Mapped m pointer 40) : ∃ words : DescWords, words.At m pointer := by
  obtain ⟨tag, tagLoad⟩ := BitVector.mapped_word m pointer 8
    (Delimited.mapped_load_zero m pointer 40 8 mapped (by decide))
  obtain ⟨word8, word8Load⟩ := BitVector.mapped_word m (pointer + 8#64) 8
    (Large.mapped_load m pointer 40 8 8 mapped (by decide))
  obtain ⟨word16, word16Load⟩ := BitVector.mapped_word m (pointer + 16#64) 8
    (Large.mapped_load m pointer 40 16 8 mapped (by decide))
  obtain ⟨word24, word24Load⟩ := BitVector.mapped_word m (pointer + 24#64) 8
    (Large.mapped_load m pointer 40 24 8 mapped (by decide))
  obtain ⟨word32, word32Load⟩ := BitVector.mapped_word m (pointer + 32#64) 8
    (Large.mapped_load m pointer 40 32 8 mapped (by decide))
  exact ⟨⟨tag, word8, word16, word24, word32⟩,
    tagLoad, word8Load, word16Load, word24Load, word32Load⟩

end SszX86.IndicesElementType
