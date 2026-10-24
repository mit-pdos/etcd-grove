/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__IsRangePermitted.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__isOpPermitted
public import Proof.go_etcd_io.etcd.server.v3.auth.VerdictLemmas

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

theorem auth.authStore.IsRangePermitted.wp_proof
    (h_isOpPermitted : auth.authStore.isOpPermitted.spec (GF := GF) (hG := hG)) :
    auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG) := by
  intro st R M a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M info key re k e dk de
      (W32 0)) $$ [$Hinv $Hrd $Hk $He] as %err ⟨Hrd, Hk, He, Herr, #Hv⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  iapply permVerdict_permOp_read M info k e err $$ Hv

end proof

end EtcdGrove
end Perennial
