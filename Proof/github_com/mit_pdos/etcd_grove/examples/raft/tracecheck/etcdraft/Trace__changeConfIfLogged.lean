/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__changeConfIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__changeConfIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent

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

theorem Trace.changeConfIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG)) :
    Trace.changeConfIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i j action a
  wp_start as ⟨#Ht, #Hts, %Hl1, %Ha, %Hcc⟩
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"ChangeConf" "ChangeConf" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  have hne : tr.isNodeEvent ts "ChangeConf" (uint.nat i) = false := by
    unfold Trace.isNodeEvent Trace.isEvent; simp [Hcc]
  rw [hne]
  wp_auto
  have : tr.changeConfIfLogged ts (uint.nat i) (uint.nat j) a = [] := by
    unfold Trace.changeConfIfLogged; simp [hne]
  rw [this]
  iapply HΦ
  iapply statesOut_nil

end proof

end Etcdraft
end EtcdGrove
end Perennial
