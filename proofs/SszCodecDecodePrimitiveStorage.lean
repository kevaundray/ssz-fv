import SszCodecDecodePrimitiveProofs

set_option autoImplicit false

namespace SszNative.CodecDecode

/-- Primitive views retain the original base offset. Byte leaves borrow the whole
input; bit leaves borrow either the whole input or exactly the delimiter-retained
prefix. No composite node can be produced by a primitive decoder. -/
def PrimitiveBorrowed (input : Input) : Node → Prop
  | .bool _ | .uint _ => True
  | .bytes offset data => offset = input.offset ∧ data = input.bytes
  | .bits offset data => offset = input.offset ∧
      (data.bytes = input.bytes ∨ data.bytes = input.bytes.extract 0
        (Delimited.retainedBytes input.bytes.size
          (Ssz.highestBit input.bytes[input.bytes.size - 1]!)))
  | .seq _ _ | .union _ _ _ => False

private theorem bind_preserves {α : Type} (first : Outcome α)
    (next : α → Nat → Outcome Node) (property : Node → Prop)
    (preserved : ∀ value used node, (next value used).result = .ok node → property node)
    (node : Node) (success : (bind first next).result = .ok node) : property node := by
  cases result : first.result with
  | error reason => simp [bind, result] at success
  | ok value =>
    apply preserved value first.used node
    simpa only [bind, result] using success

private theorem unchanged_preserves (used : Nat) (value node : Node)
    (success : (unchanged used (.ok value)).result = .ok node) : node = value := by
  exact (Except.ok.inj success).symm

private theorem packed_storage (input : Input) (data : Ssz.Bytes) (count : BitVec 128)
    (used : Nat) (physical : data.size < 2 ^ 64)
    (borrowed : data = input.bytes ∨ data = input.bytes.extract 0
      (Delimited.retainedBytes input.bytes.size
        (Ssz.highestBit input.bytes[input.bytes.size - 1]!)))
    (node : Node) (success : (packed input.offset data count used).result = .ok node) :
    node.value.Physical ∧ PrimitiveBorrowed input node := by
  by_cases sized : data.size = (count.toNat + 7) / 8
  · simp only [packed, sized, ↓reduceDIte, unchanged, Except.ok.injEq] at success
    subst node
    exact ⟨physical, rfl, borrowed⟩
  · simp [packed, sized, unchanged] at success

/-- Trimming bounds both the Small pack and every Large limb pack. -/
theorem unsigned_read_bound (input : Input) (start count index : Nat)
    (window : start + count ≤ WordDecode.significantBytes input.bytes input.bytes.size)
    (within : index < count) : start + index < input.bytes.size := by
  have trimmed := WordDecode.significantBytes_le input.bytes input.bytes.size
  omega

/-- The countdown scan accesses count-1 only in its nonzero branch. -/
theorem unsigned_scan_read_bound (input : Input) (count : Nat)
    (within : count ≤ input.bytes.size) (nonzero : count ≠ 0) :
    count - 1 < input.bytes.size := by omega

/-- The bool byte is read only after exact scope has established one byte. -/
theorem bool_read_bound (input : Input) (used : Nat)
    (checked : (exact (.small 1) input.bytes.size used).result = .ok ()) :
    0 < input.bytes.size := by
  by_cases sized : input.bytes.size = 1
  · omega
  · simp [exact, NatOperand.value, NatOperand.words, Limbs.value, sized,
      eq_comm, unchanged] at checked

/-- Large unsigned outputs expose the actual reservation, its complete initialized
limbs, exact byte interval, and nontruncating native pointer representation. -/
theorem unsigned_large_geometry (input : Input) (arena : Delimited.ArenaState)
    (valid : Arena.Valid arena.base arena.capacity arena.used)
    (pointer : BitVec 64) (words : List (BitVec 64))
    (success : (unsigned input arena).result = .ok (.uint (.large pointer words))) :
    ∃ allocation : Arena.Reservation,
      Arena.reserve arena.base arena.capacity arena.used
        ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) = some allocation ∧
      pointer = BitVec.ofNat 64 allocation.pointer ∧
      words = WordDecode.decodeWords input.bytes 0
        (WordDecode.significantBytes input.bytes input.bytes.size) ∧
      words.length = (WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8 ∧
      2 ≤ words.length ∧ pointer.toNat = allocation.pointer ∧
      pointer.toNat % 8 = 0 ∧ 0 < pointer.toNat ∧
      arena.base + arena.used ≤ pointer.toNat ∧
      pointer.toNat + 8 * words.length = arena.base + allocation.used ∧
      allocation.used ≤ arena.capacity ∧
      pointer.toNat + 8 * words.length ≤ 2 ^ 64 := by
  by_cases small : WordDecode.significantBytes input.bytes input.bytes.size ≤ 8
  · simp [unsigned, small] at success
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used
        ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) with
    | none => simp [unsigned, small, reserved] at success
    | some allocation =>
      simp only [unsigned, small, ↓reduceIte, reserved, Except.ok.injEq,
        Node.uint.injEq, NatOperand.large.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      have count : 2 ≤ (WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8 := by omega
      have geometry := Arena.success_properties arena.base arena.capacity arena.used _
        valid (by omega) allocation reserved
      have represented : (BitVec.ofNat 64 allocation.pointer).toNat = allocation.pointer :=
        Nat.mod_eq_of_lt geometry.2.2.1
      refine ⟨allocation, rfl, rfl, rfl, WordDecode.decodeWords_length _ _ _, ?_⟩
      rw [WordDecode.decodeWords_length, represented]
      exact ⟨count, rfl, geometry.1, geometry.2.1, geometry.2.2.2.2.2.1,
        geometry.2.2.2.2.2.2.1, geometry.2.2.2.2.1, geometry.2.2.2.2.2.2.2.2⟩

theorem unsigned_storage (input : Input) (arena : Delimited.ArenaState)
    (physical : input.bytes.size < 2 ^ 64) (node : Node)
    (success : (unsigned input arena).result = .ok node) :
    node.value.Physical ∧ PrimitiveBorrowed input node := by
  by_cases small : WordDecode.significantBytes input.bytes input.bytes.size ≤ 8
  · simp only [unsigned, small, ↓reduceIte, Except.ok.injEq] at success
    subst node
    exact ⟨True.intro, True.intro⟩
  · cases reserved : Arena.reserve arena.base arena.capacity arena.used
        ((WordDecode.significantBytes input.bytes input.bytes.size + 7) / 8) with
    | none => simp [unsigned, small, reserved] at success
    | some allocation =>
      simp only [unsigned, small, ↓reduceIte, reserved, Except.ok.injEq] at success
      subst node
      constructor
      · change (WordDecode.decodeWords input.bytes 0
          (WordDecode.significantBytes input.bytes input.bytes.size)).length < 2 ^ 64
        rw [WordDecode.decodeWords_length]
        have trimmed := WordDecode.significantBytes_le input.bytes input.bytes.size
        omega
      · trivial

theorem bitVector_storage (length : NatOperand) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (node : Node) (success : (bitVector length input arena).result = .ok node) :
    node.value.Physical ∧ PrimitiveBorrowed input node := by
  apply bind_preserves _ _ _ ?_ node success
  intro count used node success
  exact packed_storage input input.bytes count used physical (Or.inl rfl) node success

theorem delimited_storage (limit : Option NatOperand) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (node : Node) (success : (delimited limit input arena).result = .ok node) :
    node.value.Physical ∧ PrimitiveBorrowed input node := by
  by_cases empty : input.bytes.size = 0
  · simp [delimited, empty, unchanged] at success
  · by_cases zero : input.bytes[input.bytes.size - 1]! = 0
    · cases scanned : Delimited.scanZeros input.bytes <;>
        simp [delimited, empty, zero, scanned, unchanged] at success
    · cases prepared : Delimited.prepare arena (Delimited.countWords input.bytes.size
          (Ssz.highestBit input.bytes[input.bytes.size - 1]!)) with
      | none => simp [delimited, empty, zero, prepared, unchanged] at success
      | some ready =>
        simp only [delimited, empty, zero, ↓reduceIte, prepared] at success
        apply bind_preserves _ _ _ ?_ node success
        intro value used node success
        apply packed_storage input _ _ used ?_ (Or.inr rfl) node success
        have extracted : (input.bytes.extract 0 (Delimited.retainedBytes input.bytes.size
            (Ssz.highestBit input.bytes[input.bytes.size - 1]!))).size ≤ input.bytes.size := by
          simp only [Array.size_extract, Nat.sub_zero]
          exact Nat.min_le_right _ _
        omega

/-- The primitive boundary constructs physically sized native storage without
assuming physical descriptor metadata or the success of any later operation. -/
theorem primitive_storage (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (node : Node) (success : (primitive shape input arena).result = .ok node) :
    node.value.Physical ∧ PrimitiveBorrowed input node := by
  cases shape with
  | bool =>
    apply bind_preserves _ _ _ ?_ node success
    intro value used node success
    dsimp only at success
    split at success
    · have same := unchanged_preserves _ _ _ success
      subst node
      exact ⟨True.intro, True.intro⟩
    · split at success
      · have same := unchanged_preserves _ _ _ success
        subst node
        exact ⟨True.intro, True.intro⟩
      · cases success
  | uint width =>
    apply bind_preserves _ _ _ ?_ node success
    intro value used node success
    exact unsigned_storage input { arena with used := used } physical node success
  | byteVector length =>
    apply bind_preserves _ _ _ ?_ node success
    intro value used node success
    have same := unchanged_preserves _ _ _ success
    subst node
    exact ⟨physical, rfl, rfl⟩
  | byteList limit =>
    apply bind_preserves _ _ _ ?_ node success
    intro value used node success
    have same := unchanged_preserves _ _ _ success
    subst node
    exact ⟨physical, rfl, rfl⟩
  | bitVector length => exact bitVector_storage length input arena physical node success
  | bitList limit => exact delimited_storage (some limit) input arena physical node success
  | progressiveBitList limit => exact delimited_storage limit input arena physical node success

theorem primitive_physical (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (node : Node) (success : (primitive shape input arena).result = .ok node) :
    node.value.Physical := (primitive_storage shape input arena physical node success).1

theorem primitive_borrowed (shape : Serialize.Desc) (input : Input)
    (arena : Delimited.ArenaState) (physical : input.bytes.size < 2 ^ 64)
    (node : Node) (success : (primitive shape input arena).result = .ok node) :
    PrimitiveBorrowed input node := (primitive_storage shape input arena physical node success).2

end SszNative.CodecDecode
