/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__Receive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__UpdateTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleRequestVoteRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleRequestVoteResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__DropStaleResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleAppendEntriesResponse

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

-- Two optional successors through `nonNil` (hygiene off): `HB` their non-nil ones.
set_option hygiene false in
local macro "nn2" o1:term "," o2:term : tactic => `(tactic| (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %slb ⟨Hslb, -⟩
    wp_apply wp_nonNil _ (DFrac.own 1) _ [$o1, $o2] (fun r s => stateRO (GF := GF) r s) $$ [Hslb Hr1 Hr2] as %outB HB
    · iframe Hslb
      rw [show ∀ (a b : Loc), ([a, zero_val Loc].set (sint.nat (W64 (0 + 1))) b) = [a, b] from fun _ _ => rfl]
      isplitl [Hr1 Hr2]
      · iapply BigSepL2.bigSepL2_cons.2
        isplitl [Hr1]
        · iexact Hr1
        iapply BigSepL2.bigSepL2_cons.2
        isplitl [Hr2]
        · iexact Hr2
        iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      imodintro
      iintro %r %s Hs
      iapply stateRO_not_null $$ Hs))

-- `out = append(out, B...)` and the result (hygiene off).
set_option hygiene false in
local macro "rc_fin" sts:term "," h:term : tactic => `(tactic| (
    try wp_auto
    icases HA with ⟨%qsA, HoutA, HcapA, HA⟩
    icases HB with ⟨%qsB, HoutB, -, HB⟩
    wp_apply wp_slice_append $$ [HoutA HcapA HoutB] as %out ⟨Hout, Hcap, -⟩
    · iframe
    try wp_auto
    ihave %HAl := BigSepL2.bigSepL2_length $$ HA
    imodintro
    iapply HΦ
    rw [($h : st.receive m = .ok (somes [st.updateTerm (uint.nat gm.Dest') (uint.nat gm.Source') m] ++ $sts))]
    dsimp only
    iexists _
    iframe Hout Hcap
    iapply (BigSepL2.bigSepL2_append (Or.inl HAl)).2
    iframe))

theorem State.Receive.wp_proof (wp_nonNil : nonNil.spec (GF := GF) (hG := hG))
    (wp_UpdateTerm : State.UpdateTerm.spec (GF := GF) (hG := hG))
    (wp_HRVReq : State.HandleRequestVoteRequest.spec (GF := GF) (hG := hG))
    (wp_HRVResp : State.HandleRequestVoteResponse.spec (GF := GF) (hG := hG))
    (wp_DropStale : State.DropStaleResponse.spec (GF := GF) (hG := hG))
    (wp_HAEReq : State.HandleAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_HAEResp : State.HandleAppendEntriesResponse.spec (GF := GF) (hG := hG)) :
    State.Receive.spec (GF := GF) (hG := hG) := by
  intro p st q m
  wp_start as ⟨#Hst, #Hmsg, %Hpok, %Hmok, %Hpv1, %Hpv2, %Hsn, %hp1, %hp2, %hel, %hll⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
  read_msg
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_lookup2 $$ [Hm] as -
  · iexact Hm
  have hdest : uint.nat gm.Dest' = m.dest := Hv.2.2.2.2.2.2.2.2.2.2.2.2
  have hsrc : uint.nat gm.Source' = m.source := Hv.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := Hkeys gm.Dest'
  rw [hdest] at hk
  by_cases hd : m.dest ∈ st.server
  rotate_left
  · rw [decide_eq_false (fun e => hd (hk.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.receive m = .ok [] := by
      unfold State.receive; simp [hd]; rfl
    rw [this]
    dsimp only
    iexists []
    ihave Hn := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := Loc) (GF := GF)
    iframe Hn Hc
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  rw [decide_eq_true (hk.2 hd)]
  wp_auto
  have Hi : uint.nat gm.Dest' ∈ st.server := by rw [hdest]; exact hd
  wp_apply wp_UpdateTerm p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r0 Hr0
  · iframe Hst Hmsg; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sla ⟨Hsla, -⟩
  wp_apply wp_nonNil _ (DFrac.own 1) _ [st.updateTerm (uint.nat gm.Dest') (uint.nat gm.Source') m]
      (fun r s => stateRO (GF := GF) r s) $$ [Hsla Hr0] as %outA HA
  · iframe Hsla
    isplitl [Hr0]
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr0]
      · iexact Hr0
      iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    imodintro
    iintro %r %s Hs
    iapply stateRO_not_null $$ Hs
  try wp_auto
  have hmd : uint.nat gm.Dest' = m.dest := hdest
  rw [Hv.1]
  cases ht : m.type
  · -- RequestVoteRequest
    simp only [msgTypeW]
    wp_auto
    wp_apply wp_HRVReq p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r1 Hr1
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %slb ⟨Hslb, -⟩
    wp_apply wp_nonNil _ (DFrac.own 1) _ [st.handleRequestVoteRequest (uint.nat gm.Dest') (uint.nat gm.Source') m]
        (fun r s => stateRO (GF := GF) r s) $$ [Hslb Hr1] as %outB HB
    · iframe Hslb
      isplitl [Hr1]
      · iapply BigSepL2.bigSepL2_cons.2
        isplitl [Hr1]
        · iexact Hr1
        iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      imodintro
      iintro %r %s Hs
      iapply stateRO_not_null $$ Hs
    rc_fin (somes [st.handleRequestVoteRequest (uint.nat gm.Dest') (uint.nat gm.Source') m]),
      (by rw [hmd, hsrc]; unfold State.receive; simp [hd, ht]; rfl)
  · -- RequestVoteResponse
    simp (config := { decide := true }) only [msgTypeW]
    wp_auto
    wp_apply wp_DropStale p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r1 Hr1
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hmok.1⟩
    try wp_auto
    wp_apply wp_HRVResp p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r2 Hr2
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hmok.1⟩
    try wp_auto
    nn2 st.dropStaleResponse (uint.nat gm.Dest') (uint.nat gm.Source') m, st.handleRequestVoteResponse (uint.nat gm.Dest') (uint.nat gm.Source') m
    rc_fin (somes [st.dropStaleResponse (uint.nat gm.Dest') (uint.nat gm.Source') m, st.handleRequestVoteResponse (uint.nat gm.Dest') (uint.nat gm.Source') m]),
      (by rw [hmd, hsrc]; unfold State.receive; simp [hd, ht]; rfl)
  · -- AppendEntriesRequest
    simp (config := { decide := true }) only [msgTypeW]
    wp_auto
    cases hae : st.handleAppendEntriesRequest (uint.nat gm.Dest') (uint.nat gm.Source') m with
    | error e =>
      wp_apply wp_HAEReq p st gm.Dest' gm.Source' q m $$ [Hst Hmsg]
      · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok, Hsn, hp1, hp2, by rw [hmd]; exact hll hd, hel⟩
      simp only [hae]
      iintro %r1 HF
      iexfalso; iexact HF
    | ok sts =>
    wp_apply wp_HAEReq p st gm.Dest' gm.Source' q m $$ [Hst Hmsg]
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok, Hsn, hp1, hp2, by rw [hmd]; exact hll hd, hel⟩
    simp only [hae]
    iintro %outB HB
    rc_fin sts, (by rw [hmd, hsrc] at hae ⊢; unfold State.receive; simp [hd, ht, hae]; rfl)
  · -- AppendEntriesResponse
    simp (config := { decide := true }) only [msgTypeW]
    wp_auto
    wp_apply wp_DropStale p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r1 Hr1
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hmok.1⟩
    try wp_auto
    wp_apply wp_HAEResp p st gm.Dest' gm.Source' q m $$ [Hst Hmsg] as %r2 Hr2
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hmok.1⟩
    try wp_auto
    nn2 st.dropStaleResponse (uint.nat gm.Dest') (uint.nat gm.Source') m, st.handleAppendEntriesResponse (uint.nat gm.Dest') (uint.nat gm.Source') m
    rc_fin (somes [st.dropStaleResponse (uint.nat gm.Dest') (uint.nat gm.Source') m, st.handleAppendEntriesResponse (uint.nat gm.Dest') (uint.nat gm.Source') m]),
      (by rw [hmd, hsrc]; unfold State.receive; simp [hd, ht]; rfl)
  · exact absurd ht Hpv1
  · exact absurd ht Hpv2

end proof

end Etcdraft
end EtcdGrove
end Perennial
