import SszArm.CodecLinkedBase

namespace SszArm.Codec.Linked

/-- Extract the actual decoded instruction using a checked complete-image
certificate, with no default instruction for a failed decode. -/
def decoded (program : List (Nat × BitVec 32))
    (all_decode : program.all (fun row => (decode_raw_inst row.2).isSome) = true)
    (row : Nat × BitVec 32) (member : row ∈ program) : ArmInst :=
  (decode_raw_inst row.2).get (List.all_eq_true.mp all_decode row member)

/-- Uniform executable binding for every word of any of the seventeen complete
function images. Use the corresponding module's `all_decode` certificate. -/
theorem step_at (program : List (Nat × BitVec 32))
    (all_decode : program.all (fun row => (decode_raw_inst row.2).isSome) = true)
    (s : ArmState) (base : BitVec 64) (code : WordsAt program s base)
    (row : Nat × BitVec 32) (member : row ∈ program)
    (entry : read_pc s = base + BitVec.ofNat 64 row.1)
    (error : read_err s = .None) :
    stepi s = exec_inst (decoded program all_decode row member) s := by
  apply stepi_eq_of_fetch_inst_of_decode_raw_inst s _ row.2 _ error entry
  · exact fetch_inst_from_program.trans (code row member)
  · exact (Option.some_get (List.all_eq_true.mp all_decode row member)).symm

end SszArm.Codec.Linked
