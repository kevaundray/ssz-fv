import SszArm.DispatchBool
import SszArm.DispatchByteView
import SszArm.DispatchUintProofs
import SszArm.DispatchBitVectorProofs
import SszArm.DispatchBitListProofs

/-!
Actual private ARM codec::deserialize entry coverage for descriptor tags 0--6.
Each public theorem starts at the original function entry, executes the linked
prologue and descriptor branch tree, derives body ownership from original
physical resources, and composes the accepted primitive body through real RET.
This does not claim the external C/schema-construction wrapper or composite tags.

Public refinements are Dispatch.Boolean.program_correct,
Dispatch.Bytes.program_refines, Dispatch.Unsigned.program_refines,
Dispatch.BitVector.program_refines, and DispatchBitList.{bitList_ssz_correct,
progressiveBitList_ssz_correct}. All retain their native memory/resource frame.
-/
