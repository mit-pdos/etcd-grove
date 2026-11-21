/-
Proof of `assemble32` over its translated body (`encoding/base64`, go1.27.3). Lean-first
(prove-authcrypto, 2026-11-21).
-/
module

public import Spec.encoding.base64.assemble32

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

theorem base64.assemble32.wp_proof : base64.assemble32.spec (GF := GF) (hG := hG) := by
  intro n1 n2 n3 n4
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
