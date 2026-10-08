/-
Proof of `Spec/raftpb_sovRaft.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.sovRaft

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.sovRaft.wp_proof : raftpb.sovRaft.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as _
  wp_auto
  wp_apply _root_.Perennial.math.bits.wp_Len64 with %l _
  wp_end

end proof

end EtcdGrove
end Perennial
