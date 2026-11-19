/-
Proof of `Spec/k8s_io/apimachinery/pkg/runtime/schema/GroupResource__String_ptr.lean`, over
the translation of `GroupResource.String` (with its body since 2026-11-19, `schema.toml`; until
then a trust-boundary axiom). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions]

theorem schema.GroupResource.String_ptr.wp_proof :
  schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG) := by
  intro l dq gr
  wp_start as Hl
  wp_load
  wp_pures
  wp_method_call; wp_call
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    iexact Hl
  · try wp_auto
    iapply HΦ
    iexact Hl

end proof

end EtcdGrove
end Perennial
