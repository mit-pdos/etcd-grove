/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Without`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Without
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__sub

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

theorem Bag.Without.wp_proof (wp_sub : Bag.sub.spec (GF := GF) (hG := hG)) :
    Bag.Without.spec (GF := GF) (hG := hG) := by
  intro g b p m
  wp_start as ⟨#Hg, #Hm, %Hnd⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_sub_unfold.method_unfold]
  try wp_auto
  wp_apply wp_sub g b p m (W64 1) 1 $$ [Hg Hm] as %g' #Hg'
  · iframe Hg Hm
    ipureintro; exact ⟨Hnd, rfl⟩
  try wp_auto
  iapply HΦ
  unfold Bag.without
  iexact Hg'

end proof

end Etcdraft
end EtcdGrove
end Perennial
