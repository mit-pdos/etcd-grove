/-
The proof of `(*time.Duration).String()`: goose's pointer-method wrapper (`ptr_unfold'String`: load
`*l`, call the value method), over Perennial's proof of `Duration.String`. Lean-first.
-/
module

public import Spec.time.Duration__String_ptr
public import Perennial.Spec.time.Duration__String
import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.time.Assumptions]

theorem time.Duration.String_ptr.wp_proof :
    time.Duration.String_ptr.spec (GF := GF) (hG := hG) := by
  intro l d
  haveI : go.NotInterface go.int64 := ⟨by simp [go.int64]⟩
  wp_start as Hl
  wp_auto
  wp_apply _root_.Perennial.time.Duration.wp_String as %s -
  iapply HΦ $$ Hl

end proof

end EtcdGrove
end Perennial
