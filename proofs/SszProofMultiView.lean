import SszProofMultiResources
import SszIndicesArithmeticSemanticPrefix
import SszProofMultiPureTree

set_option autoImplicit false

namespace SszNative.Proof

/-- A live slot invariant. Every condition concerns current input data, not a
future execution. Borrowed values can only remain at their original nonroot. -/
structure MultiNode.Valid {l p : Nat} (node : MultiNode l p) : Prop where
  physical : node.index.words.length < 2^64
  positive : 0 < node.position
  depth_eq : node.depth = Ssz.levelOf node.position
  shift_eq : node.shift + node.depth = Indices.depth node.index
  borrowed : match node.value with
    | .hashed _ => True
    | _ => node.shift = 0 ∧ 2 ≤ node.index.value

theorem MultiNode.isRight_eq {l p : Nat} (node : MultiNode l p) (valid : node.Valid) :
    node.isRight = (node.position % 2 == 1) := by
  rw [MultiNode.isRight, Indices.bit_refines node.index node.shift valid.physical]
  have shifted : (node.index.value >>> node.shift).testBit 0 = node.index.value.testBit node.shift := by
    simp
  rw [Ssz.gindexBit, ← shifted, Nat.testBit_zero]
  rfl

theorem MultiNode.flipDomain {l p : Nat} (node : MultiNode l p) (valid : node.Valid)
    (deep : 0 < node.depth) : Indices.PrefixFlipDomain node.index node.shift true := by
  intro _
  have nonzero : node.index.value ≠ 0 := by
    intro zero
    have positive := valid.positive
    simp [MultiNode.position, zero] at positive
  have width : Indices.bitLength node.index = Indices.depth node.index + 1 := by
    rw [Indices.bitLength_value, Indices.depth_value]
    simp [Serialize.bitLength, nonzero]
  have shift := valid.shift_eq
  omega

theorem MultiNode.isSiblingOf_eq {l p : Nat} (node other : MultiNode l p)
    (valid : node.Valid) (otherValid : other.Valid) (deep : 0 < node.depth) :
    node.isSiblingOf other = (Ssz.gindexSibling node.position == other.position) := by
  rw [MultiNode.isSiblingOf, Indices.prefixEqual_refines node.index node.shift true
    other.index other.shift valid.physical otherValid.physical (node.flipDomain valid deep)]
  apply Bool.eq_iff_iff.mpr
  simp [MultiNode.position, Ssz.gindexSibling]

/-- An even writer can only read an untouched odd sibling. -/
theorem MultiNode.sibling_odd {l p : Nat} (node other : MultiNode l p)
    (valid : node.Valid) (otherValid : other.Valid) (deep : 0 < node.depth)
    (even : node.isRight = false) (paired : node.isSiblingOf other = true) :
    other.isRight = true := by
  rw [node.isSiblingOf_eq other valid otherValid deep, beq_iff_eq] at paired
  rw [node.isRight_eq valid] at even
  have parity := Ssz.gindexSibling_parity node.position
  have evenParity : node.position % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one node.position with zero | one
    · exact zero
    · simp [one] at even
  rw [other.isRight_eq otherValid, ← paired, parity, evenParity]
  decide

theorem MultiNode.rootHashed {l p : Nat} (node : MultiNode l p) (valid : node.Valid)
    (root : node.position = 1) : ∃ digest, node.value = .hashed digest := by
  cases value : node.value with
  | hashed digest => exact ⟨digest, rfl⟩
  | leaf position =>
      have borrowed := valid.borrowed
      simp only [value] at borrowed
      have same : node.index.value = 1 := by simpa [MultiNode.position, borrowed.1] using root
      omega
  | proof position =>
      have borrowed := valid.borrowed
      simp only [value] at borrowed
      have same : node.index.value = 1 := by simpa [MultiNode.position, borrowed.1] using root
      omega

/-- Hash replacement preserves every view invariant and removes the borrow case. -/
theorem MultiNode.Valid.hashed {l p : Nat} {node : MultiNode l p}
    (valid : node.Valid) (digest : Ssz.Bytes) :
    ({ node with value := .hashed digest } : MultiNode l p).Valid :=
  ⟨valid.physical, valid.positive, valid.depth_eq, valid.shift_eq, True.intro⟩

/-- A checked root predicate has no nonroot xor-domain restriction. -/
theorem MultiNode.isRoot_eq {l p : Nat} (node : MultiNode l p) (valid : node.Valid) :
    Indices.prefixEqual node.index node.shift false (.small 1) 0 = (node.position == 1) := by
  rw [Indices.prefixEqual_refines node.index node.shift false (.small 1) 0
    valid.physical (by decide) (by intro impossible; cases impossible)]
  apply Bool.eq_iff_iff.mpr
  simp [MultiNode.position, NatOperand.value, NatOperand.words, Limbs.value]

/-- Final hashed-root search equals pinned lookup because borrowed root claims
are excluded by the current-slot invariant, not by assuming successful output. -/
theorem multiFindRoot_erase {l p : Nat} (leaves proof : List Ssz.Bytes)
    (hl : leaves.length = l) (hp : proof.length = p) (nodes : List (MultiNode l p))
    (valid : ∀ node ∈ nodes, node.Valid) :
    eraseResult (multiFindRoot nodes) =
      .ok (match Ssz.nodeAt (nodes.map (MultiNode.erase leaves proof hl hp)) 1 with
        | some root => .ok root
        | none => .error .proofIncomplete) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      have head := valid node (by simp)
      have tail : ∀ next ∈ rest, next.Valid := fun next member => valid next (by simp [member])
      rw [multiFindRoot, node.isRoot_eq head]
      by_cases root : node.position = 1
      · obtain ⟨digest, hashed⟩ := node.rootHashed head root
        simp [root, hashed, Ssz.nodeAt, MultiNode.erase, MultiValue.bytes, eraseResult]
      · simpa [root, Ssz.nodeAt, MultiNode.erase]
          using ih tail

end SszNative.Proof
