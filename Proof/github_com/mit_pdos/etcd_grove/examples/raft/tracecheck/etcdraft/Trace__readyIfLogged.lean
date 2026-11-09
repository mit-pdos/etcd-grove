/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__readyIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__readyIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Ready

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

theorem Trace.readyIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_Ready : State.Ready.spec (GF := GF) (hG := hG)) :
    Trace.readyIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hnd, %Hsum⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.readyIfLogged ts (uint.nat i)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"Ready" "Ready" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "Ready" (uint.nat i)
  · ret_nil [Trace.readyIfLogged, hne]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_Ready g.S' ts.s i $$ [Hst] as %q #Hsq
  · iframe Hst; ipureintro; exact ⟨Hi, Hnd, Hsum⟩
  ret_single q, (ts.s.ready (uint.nat i)), Hsq [Trace.readyIfLogged, hne]

end proof

end Etcdraft
end EtcdGrove
end Perennial
