/-
kvreconf's proof (the same Go text), ported. Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__Put.lean`. Lean-first (no
Rocq counterpart): `do` of a `Put` (`kvNext opPutB` sets the key).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Put
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvNext kvUpd)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.Put.wp_proof (wp_do : Cluster.do.spec (GF := GF) (hG := hG)) :
    Cluster.Put.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c key val Ψ Hkey Hval
  wp_start as ⟨#Hcc, Hau⟩
  try wp_auto
  have h : ∀ x, kvNext (W8 1) key val x = kvUpd x key val := fun x => ite_eq_left rfl
  wp_apply wp_do γ vs dir c (W8 1) key val (fun _ => Ψ) Hkey Hval $$ [$Hcc Hau] as %res HΨ
  · simp only [h]
    iexact Hau
  try wp_auto
  iapply HΦ $$ HΨ

end proof

end kvdurable
end EtcdGrove
end Perennial
