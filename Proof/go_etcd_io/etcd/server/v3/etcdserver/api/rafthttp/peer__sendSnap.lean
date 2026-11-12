/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__sendSnap.lean` (rafthttp stage
7d). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__sendSnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender__send

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peer.sendSnap.wp_proof
    (hSend : rafthttp.snapshotSender.send.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.sendSnap.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p m ml rc
  wp_start as ⟨#Hp, #Hmsg, Hb⟩
  iunfold peerOk at Hp
  icases Hp with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rcc, %pc, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, #Hss, #Hssok, -⟩
  wp_auto
  wp_apply wp_fork $$ [Hb]
  · wp_apply hSend Rh pid ss m ml rc $$ [$Hb]
    · iframe #
    itrivial
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
