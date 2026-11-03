/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Storage__Compact.lean`. Lean-first
(no Rocq counterpart): the image's compaction, then the `MemoryStorage`'s (its triple, the premise).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Compact
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__compact

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

theorem Storage.Compact.wp_proof (wp_compact : image.compact.spec (GF := GF) (hG := hG)) :
    Storage.Compact.spec (GF := GF) (hG := hG) := by
  intro s ms γs ip I i eco P Q Hle Hms
  wp_start as ⟨#Hrec, #Himg, HI, #Herr, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hmsf, -⟩
  wp_auto
  wp_apply wp_compact ip I i eco Hle $$ [$HI $Herr] as %err HI
  wp_apply Hms $$ [$HP] as %e HQ
  iapply HΦ
  isplitl [HQ]
  · iexists e; iexact HQ
  iexact HI

end proof

end kvdurable
end EtcdGrove
end Perennial
