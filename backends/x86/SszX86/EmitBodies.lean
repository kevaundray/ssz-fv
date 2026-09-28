import SszX86.EmitLeafOwned
import SszX86.EmitNatOwned
import SszX86.EmitCopyOwned
import SszX86.EmitUintBody
import SszX86.EmitBits
import SszX86.EmitBytes

namespace SszX86.Emit
open SszNative.Serialize

/-- Body ownership is derived only after actual entry execution. The theorem
covers every successful primitive descriptor, including all native Nat layouts. -/
theorem bodies_run (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s body : MachineData) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat)
    (owned : Owned s base desc value buffer ra written)
    (entry : AtBody s body) (tag : BodyTag desc value body) :
    Eventually (step e) (fun final => final.2 = base + 1593 ∧
      BodyPost body (emit desc value) final.1) (body, base + Int64.ofNat (bodyEntry desc)) := by
  have compatible := success_compatible desc value written owned.valid.success
  cases desc <;> cases value <;> simp only [Compatible] at compatible
  · exact bool_body e base hc body _ (entry.bool_owned owned tag)
  · apply eventually_weaken (step e) _ _ _ _
      (Uint.body_runs e base hc body _ _ written (entry.uint_owned owned tag))
    intro final post
    exact ⟨post.1, post.2.1⟩
  · simpa only [bodyEntry, emit, show Int64.ofNat 256 = (256 : Int64) by decide] using
      Bytes.body_runs e base hc helper body _ buffer (entry.bytes_owned owned tag)
  · simpa only [bodyEntry, emit, show Int64.ofNat 256 = (256 : Int64) by decide] using
      Bytes.body_runs e base hc helper body _ buffer (entry.bytes_owned owned tag)
  · exact Bits.body_correct e base hc helper body _ _ buffer written (entry.bits_owned owned tag)
  · exact Bits.body_correct e base hc helper body _ _ buffer written (entry.bits_owned owned tag)
  · exact Bits.body_correct e base hc helper body _ _ buffer written (entry.bits_owned owned tag)

end SszX86.Emit
