/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/Snapshot__GetMetadata.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata

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

theorem raftpb.Snapshot.GetMetadata.wp_proof :
    raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq s
    wp_start as Hs
    iNamed Hs
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ
      iframe Hm
      iintro Hm
      iunfold ownSnapM
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
