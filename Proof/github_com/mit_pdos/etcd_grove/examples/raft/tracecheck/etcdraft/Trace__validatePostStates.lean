/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__validatePostStates`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__stateMatches

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

theorem Trace.validatePostStates.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_stateMatches : line.stateMatches.spec (GF := GF) (hG := hG)) :
    Trace.validatePostStates.spec (GF := GF) (hG := hG) := by
  intro t tr g ts p st i
  wp_start as ⟨#Ht, #Hts, #Hst, %Hl1, %Hl2⟩
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  wp_apply wp_stateMatches q (tr.line ts.l) p st i $$ [Hlp Hst]
  · iframe Hlp Hst
  try wp_auto
  unfold Trace.validatePostStates
  iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
