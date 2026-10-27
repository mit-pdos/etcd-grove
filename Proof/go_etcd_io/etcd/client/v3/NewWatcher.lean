/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewWatcher.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewWatcher
public import Spec.go_etcd_io.etcd.client.v3.NewWatchFromWatchClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewWatchClient

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

theorem NewWatcher.wp_proof
    (wp_NewWatchClient : NewWatchClient.spec (GF := GF) (hG := hG))
    (wp_NewWatchFromWatchClient : NewWatchFromWatchClient.spec (GF := GF) (hG := hG)) :
    NewWatcher.spec (GF := GF) (hG := hG) := by
  intro V c callSl vs
  wp_start as ⟨%Hc, #Hconn, #Hco, #Hvs, #Hok, #Hlg⟩
  wp_auto
  wp_apply wp_NewWatchClient as %v ⟨%wc, %Hv, #Hcc⟩
  subst Hv
  wp_apply wp_NewWatchFromWatchClient { V with wc := wc } c callSl vs $$ [] as %wi ⟨%w, %lg, %Hwi, #Hw⟩
  · iframe #
    isplitr
    · unfold v3rpc.watchStubAt
      iexact Hcc
    ipureintro; exact Hc
  iapply HΦ
  iexists w, wc, lg
  iframe #
  ipureintro; exact Hwi

end proof

end EtcdGrove
end Perennial
