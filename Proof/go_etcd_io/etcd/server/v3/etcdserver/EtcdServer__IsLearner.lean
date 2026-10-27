/-
Proof of `EtcdServer.IsLearner` (`server.go`; until D43 M4, 2026-10-26, the trust boundary of
unit P3b): a call of the server's cluster's `IsLocalMemberLearner`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsLearner
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsLocalMemberLearner

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.IsLearner.wp_proof
    (wp_IsLocalMemberLearner : membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG)) :
    EtcdServer.IsLearner.spec (GF := GF) (hG := hG) := by
  intro s c RM
  wp_start as ⟨#Hcl, #Hrc⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_IsLocalMemberLearner c RM as %b -
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
