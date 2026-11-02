/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__CreateSnapshot.lean`.
Lean-first (no Rocq counterpart): the image's snapshot (which copies the data), then the
`MemoryStorage`'s (its triple, the premise, which may keep the data).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__CreateSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__createSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

theorem Storage.CreateSnapshot.wp_proof
    (wp_createSnapshot : image.createSnapshot.spec (GF := GF) (hG := hG)) :
    Storage.CreateSnapshot.spec (GF := GF) (hG := hG) := by
  intro s ms γs ip I i cs co data dq bs eood P Q Hok Hms
  wp_start as ⟨#Hrec, #Himg, HI, Hcs, Hdata, #Herr, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hmsf, -⟩
  wp_auto
  wp_apply wp_createSnapshot ip I i cs co data dq bs eood Hok $$ [$HI $Hcs $Hdata $Herr]
    as %err ⟨Hdata, HI⟩
  wp_apply Hms $$ [$HP $Hdata] as %snap %e HQ
  iapply HΦ
  isplitl [HQ]
  · iexists snap, e; iexact HQ
  iexact HI

end proof

end kvdurable
end EtcdGrove
end Perennial
