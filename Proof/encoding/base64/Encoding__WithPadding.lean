/-
The proof of `Spec/encoding/base64/Encoding__WithPadding.lean`. Lean-first.
-/
module

public import Spec.encoding.base64.Encoding__WithPadding
public import Proof.encoding.base64.Lemmas

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
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

theorem base64.Encoding.WithPadding.wp_proof :
    base64.Encoding.WithPadding.spec (GF := GF) (hG := hG) := by
  intro e enc dqe
  wp_start as He
  try wp_auto
  simp only [_root_.Perennial.encoding.base64.NoPadding]
  wp_method_call
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
