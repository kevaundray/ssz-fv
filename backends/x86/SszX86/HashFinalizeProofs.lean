import SszX86.HashFinalizePadding

namespace SszX86.Hash

/-- The actual native finalizer consumes the exact112 state and returns through
its caller's original RET slot. Only the actual linked compression helper is a
trusted semantic boundary. The byte and bit counters are unrestricted UInt64s. -/
theorem finalize_correct (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (compress : CompressionCorrect e root) (s : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root s state ra) :
    Eventually (step e) (FinalizePost s state ra) (s, root - 256) := by
  apply Finalize.prefix_runs e root hc s state ra pre
  intro current entered
  exact Finalize.padding_runs e root hc compress s state ra pre current entered

end SszX86.Hash
