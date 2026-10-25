/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/snapshotSender__stop.lean` (rafthttp
stage 7d; an axiom from stage 6b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__stop
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.snapshotSender.stop.wp_proof :
    rafthttp.snapshotSender.stop.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as Hst
  iunfold snapSenderStop at Hst
  icases Hst with ⟨%sc, %γs, #Hsc, Hbc⟩
  wp_auto
  wp_apply (wp_broadcast_chan_close sc γs iprop(True)) $$ [$Hbc] as -
  · imodintro; itrivial
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
