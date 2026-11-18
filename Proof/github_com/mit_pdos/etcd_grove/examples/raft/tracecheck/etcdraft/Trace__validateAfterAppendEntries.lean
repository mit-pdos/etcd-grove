/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__validateAfterAppendEntries`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validateAfterAppendEntries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.newPending

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

theorem Trace.validateAfterAppendEntries.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_isAppendEntriesRequest : line.isAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_newPending : newPending.spec (GF := GF) (hG := hG)) :
    Trace.validateAfterAppendEntries.spec (GF := GF) (hG := hG) := by
  intro t tr g ts p st i
  wp_start as ⟨#Ht, #Hts, #Hs, %Hl1, %Hl2⟩
  open_ts
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %q #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  try wp_auto
  wp_apply wp_validatePostStates t tr g ts p st i $$ [Ht Hts Hs]
  · iframe Ht Hts Hs; ipureintro; exact ⟨Hl1, Hl2⟩
  cases hv : tr.validatePostStates ts st (uint.nat i)
  · wp_auto
    have : tr.validateAfterAppendEntries ts st (uint.nat i) = false := by
      simp [Trace.validateAfterAppendEntries, hv]
    rw [this]; iapply HΦ; ipureintro; trivial
  wp_auto
  wp_apply wp_newPending g.S' ts.s p st _ (tr.line ts.l).isAppendEntriesRequest $$ [Hst Hs Hlp]
  · iframe Hst Hs
    imodintro
    iintro %q' %m' %Φ'
    imodintro
    iintro Hm' HΦ'
    iapply wp_isAppendEntriesRequest q (tr.line ts.l) q' m' $$ [Hm' Hlp] HΦ'
    iframe Hm' Hlp Hpkg
  try wp_auto
  have : tr.validateAfterAppendEntries ts st (uint.nat i) =
      newPending ts.s st (tr.line ts.l).isAppendEntriesRequest := by
    simp [Trace.validateAfterAppendEntries, hv]
  rw [this]; iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
