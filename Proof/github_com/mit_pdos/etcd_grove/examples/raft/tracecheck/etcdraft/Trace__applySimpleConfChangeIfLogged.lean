/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__applySimpleConfChangeIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__applySimpleConfChangeIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ApplySimpleConfChange
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil

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

theorem Trace.applySimpleConfChangeIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_ApplySimpleConfChange : State.ApplySimpleConfChange.spec (GF := GF) (hG := hG))
    (wp_nonNil : nonNil.spec (GF := GF) (hG := hG)) :
    Trace.applySimpleConfChangeIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i sts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hlog, %Hrc, %Hev⟩
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"ApplyConfChange" "ApplyConfChange" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "ApplyConfChange" (uint.nat i)
  · have : sts = [] := by
      simp [Trace.applySimpleConfChangeIfLogged, hne, Pure.pure, Except.pure] at Hev; exact Hev
    subst this
    wp_auto
    iapply HΦ
    iapply statesOut_nil
  wp_auto
  cases ha : ts.s.applySimpleConfChange (uint.nat i) with
  | error e =>
    exfalso
    simp [Trace.applySimpleConfChangeIfLogged, hne, ha, Bind.bind, Except.bind] at Hev
  | ok o =>
  have hsts : sts = somes [o] := by
    simp [Trace.applySimpleConfChangeIfLogged, hne, ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hev
    first | exact Hev | exact Hev.symm
  subst hsts
  wp_apply wp_ApplySimpleConfChange g.S' ts.s i o $$ [Hst] as %q Hq
  · iframe Hst; ipureintro; exact ⟨Hi, Hlog, Hrc, ha⟩
  try wp_auto
  wp_apply wp_slice_literal [q]
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  try wp_auto
  wp_apply wp_nonNil _ (DFrac.own 1) [q] [o] (fun p s => stateRO (GF := GF) p s) $$ [Hsl0 Hq]
      as %rs ⟨%qs, Hqs, Hqcap, Hqrl⟩
  · iframe Hsl0
    isplitl [Hq]
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hq]
      · iexact Hq
      iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    imodintro
    iintro %p0 %s0 Hs0
    iapply stateRO_not_null $$ Hs0
  try wp_auto
  iapply HΦ
  iunfold statesOut
  iexists qs
  iframe

end proof

end Etcdraft
end EtcdGrove
end Perennial
