/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AcceptAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AcceptAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesAlreadyDone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ConflictAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__NoConflictAppendEntriesRequest

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

-- Not enabled: no successor, nil (hygiene off).
set_option hygiene false in
local macro "acc_none" lo:term "," pf:term : tactic => `(tactic| (
    try wp_auto
    iapply HΦ
    have : st.acceptAppendEntriesRequest (uint.nat i) (uint.nat j) $lo m = .ok [] := $pf
    rw [this]
    dsimp only
    iexists []
    ihave Hn := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := Loc) (GF := GF)
    iframe Hn Hc
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial))

theorem State.AcceptAppendEntriesRequest.wp_proof (wp_nonNil : nonNil.spec (GF := GF) (hG := hG))
    (wp_AD : State.AppendEntriesAlreadyDone.spec (GF := GF) (hG := hG))
    (wp_C : State.ConflictAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_NC : State.NoConflictAppendEntriesRequest.spec (GF := GF) (hG := hG)) :
    State.AcceptAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro p st i j logOk q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hpok, %Hmok, %Hsn, %hp1, %hp2, %hll, %hel⟩
  read_server
  read_msg
  wp_auto
  lookup_server
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]
    acc_none logOk, (by unfold State.acceptAppendEntriesRequest; simp [h1]; rfl)
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Follower]
  rw [decide_strRel Hf.2.1 strRel_follower]
  by_cases h2 : (st.s (uint.nat i)).state = follower
  rotate_left
  · rw [decide_eq_false h2]
    acc_none logOk, (by unfold State.acceptAppendEntriesRequest; simp [h1, h2]; rfl)
  rw [decide_eq_true h2]
  wp_auto
  cases hl : logOk
  · acc_none false, (by unfold State.acceptAppendEntriesRequest; simp [h1, h2]; rfl)
  wp_auto
  rw [decide_strRel Hv.2.1 strRel_snapshot, decide_eq_false Hsn]
  wp_auto
  have hidx : sint.Z (gm.PrevLogIndex' + W64 1) = m.prevLogIndex + 1 := by
    have := Hv.2.2.2.2.2.2.1; rw [← this]; word
  have hidx1 : 1 ≤ sint.Z (gm.PrevLogIndex' + W64 1) := by rw [hidx]; omega
  have hidx2 : sint.Z (gm.PrevLogIndex' + W64 1) < 2 ^ 62 := by rw [hidx]; omega
  wp_apply wp_AD p st i j (gm.PrevLogIndex' + W64 1) q m $$ [Hst Hmsg] as %r1 Hr1
  · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok, hidx1, hidx2, hp1, by omega, hll, hel⟩
  try wp_auto
  cases hc : st.conflictAppendEntriesRequest (uint.nat i) (sint.Z (gm.PrevLogIndex' + W64 1)) m with
  | error e =>
    wp_apply wp_C p st i (gm.PrevLogIndex' + W64 1) q m $$ [Hst Hmsg]
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, hidx1, hidx2, hll, hel⟩
    rw [hc]
    iintro %r2 HF
    iexfalso; iexact HF
  | ok oc =>
  wp_apply wp_C p st i (gm.PrevLogIndex' + W64 1) q m $$ [Hst Hmsg]
  · iframe Hst Hmsg; ipureintro; exact ⟨Hi, hidx1, hidx2, hll, hel⟩
  simp only [hc]
  iintro %r2 Hr2
  ihave Hr2 : optOwn (GF := GF) r2 oc $$ [Hr2]
  · cases oc <;> (simp only [optOwn]; iexact Hr2)
  try wp_auto
  cases hn : st.noConflictAppendEntriesRequest (uint.nat i) (sint.Z (gm.PrevLogIndex' + W64 1)) m with
  | error e =>
    wp_apply wp_NC p st i (gm.PrevLogIndex' + W64 1) q m $$ [Hst Hmsg]
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, hidx1, hidx2, by omega, by omega, hll, hel⟩
    rw [hn]
    iintro %r3 HF
    iexfalso; iexact HF
  | ok on =>
  wp_apply wp_NC p st i (gm.PrevLogIndex' + W64 1) q m $$ [Hst Hmsg]
  · iframe Hst Hmsg; ipureintro; exact ⟨Hi, hidx1, hidx2, by omega, by omega, hll, hel⟩
  simp only [hn]
  iintro %r3 Hr3
  ihave Hr3 : optOwn (GF := GF) r3 on $$ [Hr3]
  · cases on <;> (simp only [optOwn]; iexact Hr3)
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  wp_apply wp_nonNil _ (DFrac.own 1) _
      [st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z (gm.PrevLogIndex' + W64 1)) m, oc, on]
      (fun r s => iprop(∃ M, stateOwn (GF := GF) r s M)) $$ [Hsl0 Hr1 Hr2 Hr3] as %out Hout
  · iframe Hsl0
    have hl : ([r1, zero_val Loc, zero_val Loc].set (sint.nat (W64 (0 + 1))) r2).set (sint.nat (W64 (0 + 1 + 1))) r3 = [r1, r2, r3] := rfl
    rw [hl]
    isplitl [Hr1 Hr2 Hr3]
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr1]
      · iexact Hr1
      iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr2]
      · iunfold optOwn at Hr2; iexact Hr2
      iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr3]
      · iunfold optOwn at Hr3; iexact Hr3
      iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    imodintro
    iintro %r %s ⟨%M, Hs⟩
    iapply stateOwn_not_null $$ Hs
  try wp_auto
  iapply HΦ
  have : st.acceptAppendEntriesRequest (uint.nat i) (uint.nat j) true m =
      .ok (somes [st.appendEntriesAlreadyDone (uint.nat i) (uint.nat j) (sint.Z (gm.PrevLogIndex' + W64 1)) m, oc, on]) := by
    rw [hidx] at hc hn ⊢
    unfold State.acceptAppendEntriesRequest
    simp [h1, h2, Hsn, hc, hn]; rfl
  rw [this]
  dsimp only
  iexact Hout

end proof

end Etcdraft
end EtcdGrove
end Perennial
