/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__backoffIfUnavailable.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__backoffIfUnavailable
public import Spec.go_etcd_io.etcd.client.v3.isUnavailableErr
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.backoffIfUnavailable.wp_proof
    (wp_isUnavailableErr : isUnavailableErr.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.backoffIfUnavailable.spec (GF := GF) (hG := hG) := by
  intro wgs ci cd backoff err
  wp_start as ⟨#Hctx, #HC, #Hse, #Hv⟩
  iunfold clientWatchVars at Hv
  icases Hv with ⟨%ch, %t, %d, #Hch, #Ht, #Hd⟩
  wp_auto
  wp_apply wp_isUnavailableErr ci cd err $$ [$HC $Hse] as %b -
  wp_if_destruct
  · iapply HΦ; itrivial
  · wp_if_destruct
    · wp_if_destruct
      all_goals
        wp_apply time.wp_Sleep
        iapply HΦ; itrivial
    · wp_apply time.wp_Sleep
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
