/-
Proof of `Spec/go_etcd_io/etcd/client/v3/credentials/perRPCCredentialBundle__PerRPCCredentials.lean`
(the auth plan's E2d). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle__PerRPCCredentials

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

theorem credentials.perRPCCredentialBundle.PerRPCCredentials.wp_proof :
    credentials.perRPCCredentialBundle.PerRPCCredentials.spec (GF := GF) (hG := hG) := by
  intro b rc
  wp_start as #Hrc
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
