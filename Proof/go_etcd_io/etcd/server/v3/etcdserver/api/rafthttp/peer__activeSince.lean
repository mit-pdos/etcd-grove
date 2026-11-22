/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__activeSince.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__activeSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activeSince

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peer.activeSince.wp_proof
    (hPS : rafthttp.peerStatus.activeSince.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.activeSince.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p
  wp_start as #Hp
  iunfold peerOk at Hp
  icases Hp with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, -, -, -, -, -, -,
    #Hst, #Hps, -⟩
  wp_auto
  wp_apply hPS ps $$ [] as %t -
  · iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
