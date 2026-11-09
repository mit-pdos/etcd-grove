/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__clientRequestIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__clientRequestIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsNodeEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ClientRequest
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

theorem Trace.clientRequestIfLogged.wp_proof
    (wp_loglineIsNodeEvent : Trace.loglineIsNodeEvent.spec (GF := GF) (hG := hG))
    (wp_ClientRequest : State.ClientRequest.spec (GF := GF) (hG := hG))
    (wp_nonNil : nonNil.spec (GF := GF) (hG := hG)) :
    Trace.clientRequestIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i v
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.clientRequestIfLogged ts (uint.nat i) (sint.Z v)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsNodeEvent t tr g ts go!"Replicate" "Replicate" i $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isNodeEvent ts "Replicate" (uint.nat i)
  · ret_nil [Trace.clientRequestIfLogged, hne]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_ClientRequest g.S' ts.s i v $$ [Hst] as %q Hsq
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  try wp_auto
  wp_apply wp_nonNil _ _ [q] [ts.s.clientRequest (uint.nat i) (sint.Z v)] (fun p s => stateRO (GF := GF) p s)
    $$ [Hsl0 Hsq] as %out ⟨%qs, Hout, Hcap, Hl⟩
  · iframe Hsl0
    isplitl [Hsq]
    · iapply BigSepL2.bigSepL2_singleton.2
      cases ts.s.clientRequest (uint.nat i) (sint.Z v) <;> iexact Hsq
    imodintro
    iintro %p %s Hp
    iapply stateRO_not_null $$ Hp
  try wp_auto
  iapply HΦ' $$ %out %(somes [ts.s.clientRequest (uint.nat i) (sint.Z v)]) [] [Hout Hcap Hl]
  · ipureintro; simp [Trace.clientRequestIfLogged, hne]
  iunfold statesOut
  iexists qs
  iframe

end proof

end Etcdraft
end EtcdGrove
end Perennial
