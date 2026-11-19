/-
Proof of `fields.Everything`'s spec, over its translated body and `andTerm.Empty`'s (with their
bodies since 2026-11-19, `fields.toml`; until then a trust-boundary axiom). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.fields.Everything

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [package_sem : k8s_io.apimachinery.pkg.fields.Assumptions]

theorem fields.Everything.wp_proof : fields.Everything.spec (GF := GF) (hG := hG) := by
  wp_start
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨-, -⟩
  try wp_auto
  iapply HΦ
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ' - HΦ'
  wp_method_call; wp_call
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ'
    itrivial
  · try wp_auto
    iapply HΦ'
    itrivial

end proof

end EtcdGrove
end Perennial
