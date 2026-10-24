/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__IsLearner.lean`
(`return s.cluster.IsLocalMemberLearner()`). Lean-first (no Rocq counterpart); PR #22188
verification: replaces the `EtcdServer.IsLearner.wp_proof` axiom with a mechanized proof over
`membership.RaftCluster.IsLocalMemberLearner`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsLearner
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsLocalMemberLearner

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.IsLearner.wp_proof
    (wp_IsLocalMemberLearner : membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG)) :
    EtcdServer.IsLearner.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start as ⟨#Hcl, #Hrc, #Hkept⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_IsLocalMemberLearner c as %b -
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
