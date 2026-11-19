/-
Proof of `Spec/k8s_io/apimachinery/pkg/runtime/schema/GroupVersionResource__Empty_ptr.lean` (2026-11-19: the trust
boundary until then, when `runtime/schema` was translated names only). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource__Empty_ptr
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

theorem schema.GroupVersionResource.Empty_ptr.wp_proof :
    schema.GroupVersionResource.Empty_ptr.spec (GF := GF) (hG := hG) := by
  intro l dq v
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iStructNamedPrefix gvr "g"
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_if_destruct
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      iapply HΦ
      iexact Hl
    · iapply HΦ
      iexact Hl
  · iapply HΦ
    iexact Hl

end proof

end EtcdGrove
end Perennial
