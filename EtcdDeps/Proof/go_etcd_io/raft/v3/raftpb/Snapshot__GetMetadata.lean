/-
Proof of `Spec/Snapshot__GetMetadata.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

theorem raftpb.Snapshot.GetMetadata.wp_proof : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
