import SszX86.HashCompression
import SszX86.HashMemoryFacts

namespace SszX86.Hash

/-- The four literal MOVABS values in the real combine initializer. -/
def initialQwords : List (BitVec 64) :=
  [0xbb67ae856a09e667#64, 0xa54ff53a3c6ef372#64,
   0x9b05688c510e527f#64, 0x5be0cd191f83d9ab#64]

def initialQwordBytes : List UInt8 :=
  initialQwords.flatMap fun value => Int.toBytes 8 value.toInt

/-- Closed byte identities, checked by kernel reduction; no compression unfolds. -/
theorem initial_qwords_bytes :
    initialQwordBytes = chainingBytes SszNative.HashStream.new.chaining := by decide

theorem initial_table_bytes :
    initialBytes = chainingBytes SszNative.HashStream.new.chaining := by decide

theorem initial_first_pair :
    Int.toBytes 8 (0xbb67ae856a09e667#64).toInt = (initialBytes.take 8) := by decide

theorem initial_second_pair :
    Int.toBytes 8 (0xa54ff53a3c6ef372#64).toInt = (initialBytes.drop 8).take 8 := by decide

theorem initial_third_pair :
    Int.toBytes 8 (0x9b05688c510e527f#64).toInt = (initialBytes.drop 16).take 8 := by decide

theorem initial_fourth_pair :
    Int.toBytes 8 (0x5be0cd191f83d9ab#64).toInt = initialBytes.drop 24 := by decide

end SszX86.Hash
