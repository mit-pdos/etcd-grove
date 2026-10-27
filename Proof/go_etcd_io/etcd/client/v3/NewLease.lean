/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewLease.lean` (item 5, client construction; proved since
item 1, the client lease: until then a trust-boundary axiom). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewLease
public import Spec.go_etcd_io.etcd.client.v3.RetryLeaseClient
public import Spec.go_etcd_io.etcd.client.v3.NewLeaseFromLeaseClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewLease.wp_proof
    (wp_RetryLeaseClient : RetryLeaseClient.spec (GF := GF) (hG := hG))
    (wp_NewLeaseFromLeaseClient : NewLeaseFromLeaseClient.spec (GF := GF) (hG := hG)) :
    NewLease.spec (GF := GF) (hG := hG) := by
  intro c addr
  wp_start as ⟨#Hcore, #Hkv⟩
  iunfold clientCoreAt at Hcore
  icases Hcore with ⟨%Hcnn, #Hlg, -, -, %cfg, #Hcfg⟩
  iunfold clientKVAt at Hkv
  icases Hkv with ⟨-, %conn, %sl, #Hconn, #Hecon, #Hco, #Hcopts⟩
  wp_auto
  wp_apply wp_RetryLeaseClient c conn $$ [] as %v ⟨%rlc, %Hv, #Hrlc⟩
  · iframe #
  subst Hv
  ihave #Hcfg2 := Hcfg
  iStructNamed Hcfg2
  (try wp_auto)
  wp_apply wp_NewLeaseFromLeaseClient rlc conn c addr _ $$ [] as %vl Hres
  · iframe #
    ipureintro; exact Hcnn
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
