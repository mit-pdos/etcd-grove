/-
The proof of `time.Duration.String`: Perennial's (translated: `format` into a 32-byte buffer, every
index in bounds; some string). Lean-first.
-/
module

public import Spec.time.Duration__String
public import Perennial.Spec.time.Duration__String
import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.time.Assumptions]

theorem time.Duration.String.wp_proof : time.Duration.String.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.time.Duration.wp_String

end proof

end EtcdGrove
end Perennial
