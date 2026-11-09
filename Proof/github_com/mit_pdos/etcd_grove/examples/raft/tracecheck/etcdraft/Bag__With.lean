/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__With`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__With
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.With.wp_proof (wp_add : Bag.add.spec (GF := GF) (hG := hG)) :
    Bag.With.spec (GF := GF) (hG := hG) := by
  intro g b p m
  wp_start as ⟨#Hg, #Hm, %Hnd, %Hb⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_add_unfold.method_unfold]
  try wp_auto
  wp_apply wp_add g b p m (W64 1) 1 $$ [Hg Hm] as %g' #Hg'
  · iframe Hg Hm
    ipureintro; exact ⟨Hnd, rfl, Hb⟩
  try wp_auto
  iapply HΦ
  unfold Bag.with
  iexact Hg'

end proof

end Etcdraft
end EtcdGrove
end Perennial
