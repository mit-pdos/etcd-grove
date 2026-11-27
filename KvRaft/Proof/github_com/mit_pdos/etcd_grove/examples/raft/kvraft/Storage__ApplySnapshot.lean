/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/Storage__ApplySnapshot.lean`.
Lean-first (no Rocq counterpart): the `MemoryStorage`'s `ApplySnapshot` (its triple, the premise,
which gives the snapshot back owned), then the image's.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Storage__ApplySnapshot
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.image__applySnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

theorem Storage.ApplySnapshot.wp_proof
    (wp_applySnapshot : image.applySnapshot.spec (GF := GF) (hG := hG)) :
    Storage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs ip I sp dq sv eood P Q Hms
  wp_start as ⟨#Hrec, #Himg, HI, #Herr, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hmsf, -⟩
  wp_auto
  wp_apply Hms $$ [$HP] as ⟨Hsv, HQ⟩
  wp_apply wp_applySnapshot ip I sp dq sv eood $$ [$HI $Hsv $Herr] as %err ⟨Hsv, HI⟩
  iapply HΦ
  iframe Hsv HQ HI

end proof

end kvraft
end EtcdGrove
end Perennial
