/-
Proof of `assemble64` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.assemble64

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

theorem base64.assemble64.wp_proof : base64.assemble64.spec (GF := GF) (hG := hG) := by
  intro n1 n2 n3 n4 n5 n6 n7 n8
  wp_start
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; ipureintro; simp_all
  · try wp_auto
    iapply HΦ; ipureintro; simp_all

end proof

end EtcdGrove
end Perennial
