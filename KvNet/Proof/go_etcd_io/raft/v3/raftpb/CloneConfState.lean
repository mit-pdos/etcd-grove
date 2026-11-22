-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/CloneConfState.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneConfState.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"): `wp_CloneConfState_al`
(`CloneCS.lean`) at `al = false`.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.raftpb.CloneCS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.CloneConfState.wp_proof : raftpb.CloneConfState.spec (GF := GF) (hG := hG) :=
  ⟨fun p dq c => wp_CloneConfState_al p dq c false, wp_CloneConfState_nil⟩

end proof

end EtcdGrove
end Perennial
