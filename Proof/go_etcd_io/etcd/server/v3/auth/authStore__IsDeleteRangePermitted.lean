/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__IsDeleteRangePermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsDeleteRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.IsDeleteRangePermitted.wp_proof
    (h_isOpPermitted : auth.authStore.isOpPermitted.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG) := by
  intro st R M a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M info.Username' info.Revision' key re k e dk de
      (W32 1)) $$ [$Hinv $Hrd $Hk $He] as %err ⟨Hrd, Hk, He, Herr⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen⟩
  iapply HΦ
  iframe
  iapply typedPointsto_combine a info dq Hann
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
