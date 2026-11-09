/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__ignoreInLeaseIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__ignoreInLeaseIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePreStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__IgnoreInLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Domain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isRequestVoteRequest

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

/-- With `CheckQuorum` off, no message is ignored in a lease. -/
theorem Trace.ignoreInLeaseIfLogged_nil (tr : Trace) (ts : TState) (h : ts.s.checkQuorum = false) :
    tr.ignoreInLeaseIfLogged ts = [] := by
  unfold Trace.ignoreInLeaseIfLogged
  split
  · rfl
  · rw [List.flatMap_eq_nil_iff]
    intro m _
    split
    · have : ts.s.ignoreInLease m = none := by unfold State.ignoreInLease; simp [h]
      rw [this]; rfl
    · rfl

theorem Trace.ignoreInLeaseIfLogged.wp_proof
    (wp_loglineIsEvent : Trace.loglineIsEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePreStates : Trace.validatePreStates.spec (GF := GF) (hG := hG))
    (wp_IgnoreInLease : State.IgnoreInLease.spec (GF := GF) (hG := hG))
    (wp_Domain : Bag.Domain.spec (GF := GF) (hG := hG))
    (wp_nonNil : nonNil.spec (GF := GF) (hG := hG))
    (wp_isRVReq : line.isRequestVoteRequest.spec (GF := GF) (hG := hG)) :
    Trace.ignoreInLeaseIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hcq⟩
  rw [Trace.ignoreInLeaseIfLogged_nil tr ts Hcq]
  open_ts
  wp_auto
  wp_apply wp_loglineIsEvent t tr g ts go!"IgnoreRequestVoteRequest" "IgnoreRequestVoteRequest" $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hne : tr.isEvent ts "IgnoreRequestVoteRequest"
  · wp_auto
    iapply HΦ
    iapply statesOut_nil
  have hle : ts.l ≤ tr.len := Trace.isEvent_le hne
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%gs, %sm, #Hp, -, -, -, -, -, #Hmsgs, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨-, -, #PMs, -⟩
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Domain_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Domain gs.Messages' ts.s.messages $$ [Hmsgs] as %sl #Hsl
  · iexact Hmsgs
  iunfold msgsRO at Hsl
  icases Hsl with ⟨%ps, #Hps, #Hpl⟩
  ihave %Hlen := ownSlice_len $$ Hps
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hpl
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (x : Loc) (osl : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* ([] : List Loc) ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i m out Hnil Hcap0]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, ps[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, ts.s.messages.domain[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Hll ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => msgRO (GF := GF) a b) Hy Hx $$ Hpl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) ps DFrac.discard y hn0 $$ [Hps] as -
    · isplitr
      · iexact Hps
      ipureintro; exact Hy
    try wp_auto
    wp_apply wp_isRVReq ql (tr.line ts.l) y x $$ [Hlp Hyx]
    · iframe Hlp Hyx
    cases hr : (tr.line ts.l).isRequestVoteRequest x
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; constructor <;> word
    try wp_auto
    ihave #Hyx0 := Hyx
    iunfold msgRO at Hyx0
    icases Hyx0 with ⟨%gmx, #Hgmx, %Hvx, -⟩
    icases typedPointsto_split _ _ _ $$ Hgmx with Hgmxf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgmxf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #MD, -⟩
    try wp_auto
    wp_apply wp_validatePreStates t tr g ts gmx.Dest' $$ [Ht Hts]
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
    cases hvp : tr.validatePreStates ts (uint.nat gmx.Dest')
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; constructor <;> word
    try wp_auto
    wp_apply wp_IgnoreInLease g.S' ts.s y x $$ [Hst Hyx] as %r Hr
    · iframe Hst Hyx; ipureintro; exact Hcq
    have hil : ts.s.ignoreInLease x = none := by unfold State.ignoreInLease; simp [Hcq]
    rw [hil]
    icases Hr with %Hr
    subst Hr
    try wp_auto
    wp_apply wp_slice_literal [null]
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, -⟩
    try wp_auto
    wp_apply wp_nonNil _ (DFrac.own 1) [null] [none] (fun p s => stateRO (GF := GF) p s) $$ [Hsl0]
        as %rs ⟨%qs, Hqs, Hqcap, Hqrl⟩
    · iframe Hsl0
      isplitr
      · iapply BigSepL2.bigSepL2_cons.2
        isplitr
        · ipureintro; rfl
        iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      imodintro
      iintro %p0 %s0 Hs0
      iapply stateRO_not_null $$ Hs0
    ihave %Hqll := BigSepL2.bigSepL2_length $$ Hqrl
    have hqs : qs = [] := by simpa [somes] using Hqll
    subst hqs
    try wp_auto
    wp_apply wp_slice_append $$ [Hout Hcap Hqs] as %s3 ⟨Hs3, Hcap3, -⟩
    · iframe
    try wp_auto
    simp only [List.append_nil]
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    iunfold statesOut
    iexists []
    iframe
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
