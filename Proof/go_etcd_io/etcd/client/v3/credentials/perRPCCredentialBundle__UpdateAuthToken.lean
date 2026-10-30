/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/perRPCCredentialBundle__UpdateAuthToken.lean`
(the auth plan's C1, 2026-10-28). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle__UpdateAuthToken
public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__UpdateAuthToken

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
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- Phase 1 of C1 (`notes/c1-plan.md`): the method is not yet translated
(`Code/go_etcd_io/etcd/client/v3/credentials.toml`). -/
theorem credentials.perRPCCredentialBundle.UpdateAuthToken.wp_proof
    (wp_UpdateAuthToken : credentials.perRPCCredential.UpdateAuthToken.spec (GF := GF) (hG := hG)) :
    credentials.perRPCCredentialBundle.UpdateAuthToken.spec (GF := GF) (hG := hG) := by
  intro b P t
  wp_start as ⟨Hb, #Ht⟩
  unfold tokenBundleInv
  icases Hb with ⟨%b', %rc, %h, #Hrc, #Hinv⟩
  have hb : b = b' := by
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
    exact GoGlobalContext.intoVal_inj_loc h
  subst hb
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; trivial
  wp_apply wp_UpdateAuthToken rc P t $$ [Hinv Ht]
  · iframe Hinv Ht
  iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
