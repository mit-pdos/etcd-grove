-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/appendEnum.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/appendEnum.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendEnum
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendVarint

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

theorem raftpb.appendEnum.wp_proof
    (wp_appendVarint : raftpb.appendVarint.spec (GF := GF) (hG := hG)) :
    raftpb.appendEnum.spec (GF := GF) (hG := hG) := by
  intro b B v
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_appendVarint $$ [$Hb $Hcap] as %s ⟨Hs, Hcap⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
