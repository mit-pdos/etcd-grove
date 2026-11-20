/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Message__GetTo.lean` over the real body
(prove-grpcsmall, 2026-11-20; a trust-boundary axiom until then, D22 S-h): `snap.Message` embeds a
`*raftpb.Message`, and the promoted `GetTo` loads the embedded pointer (`msgRO`'s `Message` field) and
calls raftpb's proved getter on it, over the raft message's read-only content `msgRO` keeps
(`NewMessage`'s read-only argument).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode snap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.Message.GetTo.wp_proof
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    snap.Message.GetTo.spec (GF := GF) (hG := hG) := by
  intro m ml rc
  wp_start as Hm
  unfold msgIs msgRO
  icases Hm with #⟨Hml, -, -, -, ⟨%st, Hown⟩⟩
  wp_auto
  wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [Hown]
  · iexact Hown
  iintro -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
