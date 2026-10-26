/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__IsLearner.lean`. Lean-first (no
Rocq counterpart); the trust boundary of unit P3b (names-only) until 2026-10-26: a call of the
server's `*RaftCluster`'s `IsLocalMemberLearner`.
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
    (hL : membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG)) :
    EtcdServer.IsLearner.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start as ⟨#Hcf, #Hrc, #Hlk⟩
  (try wp_auto)
  wp_apply hL c $$ [] as %b -
  · iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
