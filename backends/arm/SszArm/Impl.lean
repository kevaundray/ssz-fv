import Arm.State

/-!
# The emitted AArch64 uint64 kernels

These raw words bind to the two functions in `asm/arm/uint64.s` through
`scripts/check-asm.py`, which assembles temporary objects and checks their words.
`stepi` fetches and decodes them inside each proof.

AAPCS64 passes the caller-owned buffer in x0, the store value in x1, the load
result in x0, and the return address in x30. Both kernels allow unaligned data
addresses and access exactly eight bytes. They are not length-checking public
SSZ deserializers.

LNSym has total byte-addressed memory and a separate instruction map. Thus the
model does not express allocation, mapping, access permissions, or executable
memory aliasing. Callers must supply a real readable/writable eight-byte region;
the natural-address frame theorem additionally states its no-wrap condition.
-/

namespace SszArm

def loadProgram : List (BitVec 32) :=
  [ 0xf9400000#32    -- ldr x0, [x0]
  , 0xd65f03c0#32 ]  -- ret

def storeProgram : List (BitVec 32) :=
  [ 0xf9000001#32    -- str x1, [x0]
  , 0xd65f03c0#32 ]  -- ret

/-- The function's raw words are present at a symbolic linked address. -/
def CodeAt (s : ArmState) (base : BitVec 64) (code : List (BitVec 32)) : Prop :=
  ∀ k (hk : k < code.length),
    s.program.find? (base + BitVec.ofNat 64 (4 * k)) = some code[k]

/-- A concrete instruction map witnessing the code-placement precondition. -/
def loadAt (base : BitVec 64) (code : List (BitVec 32)) : Program :=
  code.mapIdx fun k word => (base + BitVec.ofNat 64 (4 * k), word)

end SszArm
