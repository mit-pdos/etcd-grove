/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `TState__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TState__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Equal

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

theorem TState.Equal.wp_proof (wp_StateEqual : State.Equal.spec (GF := GF) (hG := hG)) :
    TState.Equal.spec (GF := GF) (hG := hG) := by
  intro g ts h us
  wp_start as ⟨#Hg, #Hh⟩
  iunfold tstateRO at Hg Hh
  icases Hg with ⟨#Hgs, %Hgf⟩
  icases Hh with ⟨#Hhs, %Hhf⟩
  wp_auto
  rw [sint_decide_nat Hgf.1 Hhf.1]
  by_cases hl : ts.l = us.l
  · rw [decide_eq_true hl]
    wp_auto
    wp_apply wp_StateEqual g.S' ts.s h.S' us.s $$ [Hgs Hhs]
    · iframe Hgs Hhs
    try wp_auto
    have : ts.eq us = ts.s.eq us.s := by simp [TState.eq, hl]
    rw [this]; iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false hl]
    wp_auto
    have : ts.eq us = false := by simp [TState.eq, hl]
    rw [this]; iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
