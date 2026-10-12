/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__ReadState.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__ReadState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.ReadState.wp_proof : raftNode.ReadState.spec (GF := GF) (hG := hG) := by
  intro E γ r
  wp_start as #Hr
  iunfold isRaftNode at Hr
  iNamed Hr
  wp_auto
  iapply HΦ
  iexact Hrsci

end proof

end EtcdGrove
end Perennial
