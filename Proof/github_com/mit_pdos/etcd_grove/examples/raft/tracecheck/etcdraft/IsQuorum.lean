/-
Lean-first (no Rocq counterpart). Layer C (2026-11-08): the proof of `IsQuorum`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsQuorum
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Subset

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

theorem IsQuorum.wp_proof (wp_Subset : Set.Subset.spec (GF := GF) (hG := hG)) :
    IsQuorum.spec (GF := GF) (hG := hG) := by
  intro ql q cl c
  wp_start as ⟨#Hq, #Hc, %Hql⟩
  ihave #Hq0 := Hq
  ihave #Hc0 := Hc
  iunfold setRO at Hq0 Hc0
  icases Hq0 with ⟨%xs, #Hxs, %Hxm⟩
  icases Hc0 with ⟨%ys, #Hys, %Hym⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  ihave %Hyl := ownSlice_len $$ Hys
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Subset_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Subset ql q cl c $$ [Hq Hc]
  · iframe Hq Hc
  by_cases hs : q.subset c = true
  · rw [hs]
    try wp_auto
    have hq : q.length = xs.length := by rw [← Hxm, List.length_map]
    have hc : c.length = ys.length := by rw [← Hym, List.length_map]
    have hlen : sint.Z (ql.len * W64 2) = sint.Z ql.len * 2 := by
      have : (xs.length : Int) < 2 ^ 62 := by rw [← hq]; exact_mod_cast Hql
      rw [Hxl.1] at this; word
    have : isQuorum q c = decide (sint.Z cl.len < sint.Z (ql.len * W64 2)) := by
      unfold isQuorum; rw [hs, Bool.true_and, hlen]
      congr 1; apply propext; rw [hq, hc, Hxl.1, Hyl.1]; word
    rw [this]
    iapply HΦ; ipureintro; trivial
  · rw [Bool.not_eq_true] at hs
    rw [hs]
    try wp_auto
    have : isQuorum q c = false := by unfold isQuorum; rw [hs, Bool.false_and]
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
