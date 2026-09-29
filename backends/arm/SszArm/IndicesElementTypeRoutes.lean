import SszArm.IndicesElementTypeDispatch

set_option autoImplicit false

namespace SszArm.Indices.ElementType.Dispatch

/-- Only the physical tag is classified here; no declaration validity is imposed. -/
inductive Kind where
  | boolean | uint | byteVector | byteList | bitVector | bitList | progressiveBitList
  | vector | list | progressiveList | container | progressiveContainer | union
  deriving DecidableEq

def Kind.tag : Kind → BitVec 64
  | .boolean => 0 | .uint => 1 | .byteVector => 2 | .byteList => 3
  | .bitVector => 4 | .bitList => 5 | .progressiveBitList => 6
  | .vector => 7 | .list => 8 | .progressiveList => 9
  | .container => 10 | .progressiveContainer => 11 | .union => 12

def Kind.ofDesc : SszNative.Codec.Desc → Kind
  | .primitive .bool => .boolean
  | .primitive (.uint _) => .uint
  | .primitive (.byteVector _) => .byteVector
  | .primitive (.byteList _) => .byteList
  | .primitive (.bitVector _) => .bitVector
  | .primitive (.bitList _) => .bitList
  | .primitive (.progressiveBitList _) => .progressiveBitList
  | .vector _ _ => .vector
  | .list _ _ => .list
  | .progressiveList _ _ => .progressiveList
  | .container _ => .container
  | .progressiveContainer _ _ => .progressiveContainer
  | .compatibleUnion _ => .union

def Kind.ops (kind : Kind) (position : Bool) : List Op :=
  [.p12, .p16, if position then .p44 else .p20] ++
  match kind with
  | .boolean | .uint => [.p48, .p52, .p56, .p144, .p148, .p152]
  | .byteVector | .byteList => [.p48, .p52, .p56, .p144, .p148, .p152, .p156]
  | .bitVector | .bitList | .progressiveBitList => [.p48, .p52, .p56]
  | .vector | .list =>
      (if position then [.p252, .p256, .p260, .p264, .p268]
       else [.p24, .p28, .p32]) ++ [.p36, .p40]
  | .progressiveList =>
      (if position then [.p252, .p256, .p260, .p264, .p268]
       else [.p24, .p28, .p32]) ++ [.p272, .p276, .p280]
  | .container =>
      if position then [.p252, .p256, .p372, .p376, .p612]
      else [.p24, .p28, .p32, .p272, .p276]
  | .progressiveContainer =>
      if position then [.p252, .p256, .p372, .p376, .p380, .p384, .p388]
      else [.p24, .p28, .p32, .p272, .p276]
  | .union =>
      if position then [.p252, .p256, .p372, .p376, .p380, .p384]
      else [.p24, .p28, .p32, .p272, .p276]

def Kind.destination (kind : Kind) (position : Bool) : Nat :=
  match kind with
  | .bitVector | .bitList | .progressiveBitList => 60
  | .byteVector | .byteList => 160
  | .vector | .list | .progressiveList => 284
  | .container => if position then 616 else 408
  | .progressiveContainer => if position then 392 else 408
  | _ => 408

/-- Arbitrary non-position discriminants stay arbitrary: the branch observes only
whether the PathStep tag is zero. Position payloads are not read by this segment. -/
theorem route_follows (kind : Kind) (position : Bool) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 12#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (zero : r (.GPR 9#5) s = 0#64 ↔ position = true) :
    Follows base (kind.ops position) s := by
  change r .PC s = _ at pc
  cases position <;> cases kind <;>
    simp_all (config := {decide := true, instances := true})
      [Kind.ops, Kind.tag, Follows, Op.row, Op.effect,
       put, next, branch, compare64, greater,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc]

theorem route_destination (kind : Kind) (position : Bool) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 12#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (zero : r (.GPR 9#5) s = 0#64 ↔ position = true) :
    read_pc (block (kind.ops position) s) =
      base + BitVec.ofNat 64 (kind.destination position) := by
  change r .PC s = _ at pc
  cases position <;> cases kind <;>
    simp_all (config := {decide := true, instances := true})
      [Kind.ops, Kind.tag, Kind.destination, block, Op.effect,
       put, next, branch, compare64, greater,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.add_assoc]

theorem route_run (kind : Kind) (position : Bool) (s : ArmState) (base : BitVec 64)
    (code : Linked.ElementType.CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + 12#64)
    (tag : r (.GPR 8#5) s = kind.tag)
    (zero : r (.GPR 9#5) s = 0#64 ↔ position = true) :
    run (kind.ops position).length s = block (kind.ops position) s ∧
    read_pc (block (kind.ops position) s) =
      base + BitVec.ofNat 64 (kind.destination position) :=
  ⟨block_run _ s base code error (route_follows kind position s base pc tag zero),
   route_destination kind position s base pc tag zero⟩

end SszArm.Indices.ElementType.Dispatch
