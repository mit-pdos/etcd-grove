/-
Proof of `Spec/go_etcd_io/etcd/client/v3/New.lean` (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.New
public import Spec.go_etcd_io.etcd.client.v3.newClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem clientv3.New.wp_proof (wp_newClient : newClient.spec (GF := GF) (hG := hG)) :
    clientv3.New.spec (GF := GF) (hG := hG) := by
  intro cfg ep V
  wp_start as ⟨#Hvars, #Hcfg, #Hw, %HV⟩
  ihave #Hcfg' := Hcfg
  iunfold clientCfgOk at Hcfg'
  icases Hcfg' with ⟨#Heps, -, -⟩
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_auto
  rw [decide_eq_false (show ¬ (cfg.Endpoints'.len = W64 0) by
    intro h; rw [h] at Hel; have h0 := Hel.1; simp only [List.length_singleton] at h0; revert h0; decide)]
  wp_auto
  ipersist cfg
  wp_apply wp_newClient cfg_ptr cfg ep V $$ [$Hvars $cfg $Hcfg $Hw] as %cl %err Hres
  · ipureintro; exact HV
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
