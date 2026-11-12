/-
Proof of `Spec/go_etcd_io/etcd/client/v3/RetryLeaseClient.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.RetryLeaseClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewLeaseClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem RetryLeaseClient.wp_proof (wp_NewLeaseClient : NewLeaseClient.spec (GF := GF) (hG := hG)) :
    RetryLeaseClient.spec (GF := GF) (hG := hG) := by
  intro cl conn
  wp_start as #Hconn
  wp_auto
  wp_apply wp_NewLeaseClient as %v ⟨%lc, %Hv, #Hcc⟩
  subst Hv
  wp_alloc rlc as Hrlc
  iStructNamed Hrlc
  ipersist lc
  wp_auto
  iapply HΦ
  iexists rlc
  isplitl []
  · ipureintro; rfl
  unfold retryLeaseAt leaseStubAt
  iexists lc
  iframe #

end proof

end EtcdGrove
end Perennial
