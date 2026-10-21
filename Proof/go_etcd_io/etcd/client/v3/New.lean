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
  intro cfg eps V
  wp_start as ⟨#Hcfg, %HV⟩
  ihave #Hcfg' := Hcfg
  iunfold clientCfgOk at Hcfg'
  icases Hcfg' with ⟨#Heps, -, %Hpure⟩
  ihave %Hel := ownSlice_len _ _ _ $$ Heps
  wp_auto
  rw [decide_eq_false (show ¬ (cfg.Endpoints'.len = W64 0) by
    intro h; rw [h] at Hel; have h0 := Hel.1
    exact Hpure.1.1 (List.eq_nil_of_length_eq_zero (by rw [h0]; rfl)))]
  wp_auto
  ipersist cfg
  wp_apply wp_newClient cfg_ptr cfg eps V $$ [$cfg $Hcfg] as %cl %err Hres
  · ipureintro; exact HV
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
