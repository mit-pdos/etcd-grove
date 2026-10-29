/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/perRPCCredentialBundle__PerRPCCredentials.lean`
(the auth plan's E2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle__PerRPCCredentials
public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__GetRequestMetadata
public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredential__RequireTransportSecurity

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

theorem credentials.perRPCCredentialBundle.PerRPCCredentials.wp_proof
    (wp_GetRequestMetadata :
      credentials.perRPCCredential.GetRequestMetadata.spec (GF := GF) (hG := hG))
    (wp_RequireTransportSecurity :
      credentials.perRPCCredential.RequireTransportSecurity.spec (GF := GF) (hG := hG)) :
    credentials.perRPCCredentialBundle.PerRPCCredentials.spec (GF := GF) (hG := hG) := by
  intro b rc P
  wp_start as ⟨#Hrc, #Hinv⟩
  wp_auto
  iapply HΦ
  unfold perRPCCredsOk
  isplit
  · iintro !> %ctx %sl %Ψ !> - HΨ
    wp_auto
    wp_apply wp_GetRequestMetadata rc P ctx sl $$ [$Hinv] as %mp %err ⟨%Herr, %cm, Hm, #Hq⟩
    iapply HΨ
    iintro -
    iexists cm
    iframe Hm
    imodintro
    iexact Hq
  · iintro !> !> %Ψ - HΨ
    wp_auto
    wp_apply wp_RequireTransportSecurity rc as %bt -
    iapply HΨ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
