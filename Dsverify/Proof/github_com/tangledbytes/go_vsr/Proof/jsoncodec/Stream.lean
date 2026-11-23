/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Stream.lean (lab master 915f964;
notes/dsv-vr.md): unchanged.
-/
/-
Scanner facts for the decoder's framing (the events package's `jsonstream`), beyond the frozen
ones of `VsrProof/Spec/json.lean`: a strict prefix of an event's encoding at the end of the
stream (`eof` true) still asks for more (an event is an object), and whitespace only asks for
more.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json

@[expose] public section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open VsrModel

/-- `scanF_partial` for either `eof`. -/
theorem vsrnet.scanF_partial_eof (ws pre : List w8) (m : Msg) (eof : Bool)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m)
    (hpre : pre <+: VsrWire.encEvent m) (hne : pre ≠ VsrWire.encEvent m) :
    (vsrnet.scanF (ws ++ pre) eof).1 = W64 1 := by
  have hsp : ∀ c ∈ ws, VsrJson.spB c = true := fun c hc => by
    rw [← vsrnet.isSpaceB_spB]; exact hws c hc
  simp only [vsrnet.scanF, VsrJson.scanF, VsrJson.scanL_partial eof ws pre m hsp hm hpre hne]
  rfl

/-- The scanner on whitespace only: more, its end the whitespace's. -/
theorem vsrnet.scanF_space (ws : List w8) (eof : Bool)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) :
    vsrnet.scanF ws eof = (W64 1, W64 ws.length) := by
  have hsp : ∀ c ∈ ws, VsrJson.spB c = true := fun c hc => by
    rw [← vsrnet.isSpaceB_spB]; exact hws c hc
  simp only [vsrnet.scanF, VsrJson.scanF, VsrJson.scanL_space ws eof hsp]
  rfl

end Perennial.github_com.tangledbytes.go_vsr.examples
