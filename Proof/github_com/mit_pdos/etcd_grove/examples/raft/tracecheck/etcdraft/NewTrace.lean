/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `NewTrace`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTrace
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTraceWith

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

theorem NewTrace.wp_proof (wp_NewTraceWith : NewTraceWith.spec (GF := GF) (hG := hG)) :
    NewTrace.spec (GF := GF) (hG := hG) := by
  intro sl evs
  wp_start as ⟨#Hevs, %Hb⟩
  wp_auto
  wp_apply wp_NewTraceWith sl evs false false $$ [Hevs] as %t %err Hr
  · iframe Hevs; ipureintro; exact Hb
  try wp_auto
  iapply HΦ
  unfold newTrace
  cases h : newTraceWith evs false false with
  | error e => simp only [h]; iexact Hr
  | ok tr =>
    simp only [h]
    icases Hr with ⟨%He, #Ht⟩
    isplitr
    · ipureintro; exact He
    iapply traceRO_of_heap t tr ⟨evs, Hb.1, Hb.2, h⟩
    iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
