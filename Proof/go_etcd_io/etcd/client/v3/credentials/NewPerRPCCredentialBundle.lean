/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/NewPerRPCCredentialBundle.lean` (the auth
plan's E2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle

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

theorem credentials.NewPerRPCCredentialBundle.wp_proof :
    credentials.NewPerRPCCredentialBundle.spec (GF := GF) (hG := hG) := by
  intro P
  wp_start as %Htb
  wp_auto
  wp_alloc b as Hb
  iStructNamed Hb
  ipersist rc
  iStructNamed «$v0»
  imod inv_alloc credTokN ⊤ iprop(∃ t : GoString,
      structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredential go!"authToken"
        «$v0_ptr» ↦ t ∗ (⌜t = go!""⌝ ∨ □ P t)) $$ [authToken] with #Hinv
  · iexists _
    iframe authToken
    ileft; ipureintro; rfl
  wp_auto
  iapply HΦ
  unfold tokenBundleInv credTokInv
  iexists b, «$v0_ptr»
  iframe rc Hinv
  isplitr
  · ipureintro; rfl
  ipureintro; exact Htb

end proof

end EtcdGrove
end Perennial
