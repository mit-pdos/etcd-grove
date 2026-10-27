/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcherStream__resetBufWait.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcherStream__resetBufWait

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

theorem watcherStream.resetBufWait.wp_proof : watcherStream.resetBufWait.spec (GF := GF) (hG := hG) := by
  intro ws t
  wp_start as Ht
  wp_auto
  iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
