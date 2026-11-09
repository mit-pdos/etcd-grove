/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__HandleAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RejectAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ReturnToFollowerState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AcceptAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

/-! The append-request actions keep the state's servers (`mut`'s premise in the leader loop). -/
theorem State.reject_server {st s : State} {i j : ID} {m : Msg} {lo : Bool}
    (h : st.rejectAppendEntriesRequest i j m lo = some s) : s.server = st.server := by
  unfold State.rejectAppendEntriesRequest at h; dsimp only at h
  split at h
  · cases h
  · cases h; rfl

theorem State.returnToFollower_server {st s : State} {i : ID} {m : Msg}
    (h : st.returnToFollowerState i m = some s) : s.server = st.server := by
  unfold State.returnToFollowerState at h; dsimp only at h
  split at h
  · cases h
  · cases h; rfl

theorem State.alreadyDone_server {st s : State} {i j : ID} {idx : Int} {m : Msg}
    (h : st.appendEntriesAlreadyDone i j idx m = some s) : s.server = st.server := by
  unfold State.appendEntriesAlreadyDone at h; dsimp only at h
  split at h
  · cases h
  · cases h
    split <;> (try split) <;> rfl

theorem State.conflict_server {st s : State} {i : ID} {idx : Int} {m : Msg}
    (h : st.conflictAppendEntriesRequest i idx m = .ok (some s)) : s.server = st.server := by
  unfold State.conflictAppendEntriesRequest subSeqM at h
  dsimp only at h
  split at h
  · cases h
  · split at h <;> cases h; rfl

theorem State.noConflict_server {st s : State} {i : ID} {idx : Int} {m : Msg}
    (h : st.noConflictAppendEntriesRequest i idx m = .ok (some s)) : s.server = st.server := by
  unfold State.noConflictAppendEntriesRequest subSeqM at h
  dsimp only at h
  split at h
  · cases h
  · split at h <;> cases h; rfl

theorem State.accept_server {st : State} {i j : ID} {lo : Bool} {m : Msg} {sts : List State}
    (hsn : m.subtype ≠ "snapshot")
    (h : st.acceptAppendEntriesRequest i j lo m = .ok sts) : ∀ s ∈ sts, s.server = st.server := by
  unfold State.acceptAppendEntriesRequest at h
  dsimp only at h
  intro s hs
  split at h
  · cases h; simp at hs
  · simp only [show (m.subtype == "snapshot") = false by simpa using hsn, Bool.false_eq_true,
      ↓reduceIte] at h
    cases hc : st.conflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
    | error e => rw [hc] at h; cases h
    | ok oc =>
    cases hn : st.noConflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
    | error e => rw [hc, hn] at h; cases h
    | ok on =>
    rw [hc, hn] at h
    cases h
    simp only [somes, List.mem_filterMap, id] at hs
    obtain ⟨o, ho, rfl⟩ := hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ho | ho | ho
    · exact State.alreadyDone_server ho.symm
    · subst ho; exact State.conflict_server hc
    · subst ho; exact State.noConflict_server hn

theorem State.HandleAppendEntriesRequest.wp_proof (wp_nonNil : nonNil.spec (GF := GF) (hG := hG))
    (wp_reject : State.RejectAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_rtf : State.ReturnToFollowerState.spec (GF := GF) (hG := hG))
    (wp_accept : State.AcceptAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.HandleAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hpok, %Hmok, %Hsn, %hp1, %hp2, %hll, %hel⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hpl := Hv.2.2.2.2.2.2.1
  ipersist s
  ipersist m
  ipersist i
  ipersist j
  ipersist v
  wp_join (Q := fun v => iprop(⌜v = #(Bool.or (m.prevLogIndex == 0) (Bool.and (Bool.and (decide (m.prevLogIndex > 0)) (decide (m.prevLogIndex ≤ ((st.s (uint.nat i)).log.length : Int)))) (some m.prevLogTerm == (((st.s (uint.nat i)).log[(m.prevLogIndex - 1).toNat]?).map Entry.term))))⌝)) at (if: _ then _ else _)
  · by_cases h0 : m.prevLogIndex = 0
    · rw [decide_eq_true (show gm.PrevLogIndex' = W64 0 by have := hpl; rw [h0] at this; word)]
      wp_auto
      ipureintro; congr 1; simp [h0]
    rw [decide_eq_false (show ¬ gm.PrevLogIndex' = W64 0 by intro e; rw [e] at hpl; exact h0 (by rw [← hpl]; rfl))]
    wp_auto
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z gm.PrevLogIndex' by rw [hpl]; show (0 : Int) < _; omega)]
    wp_auto
    by_cases h1 : m.prevLogIndex ≤ ((st.s (uint.nat i)).log.length : Int)
    rotate_left
    · rw [decide_eq_false (show ¬ sint.Z gm.PrevLogIndex' ≤ sint.Z gs.Log'.len by rw [hpl, hlen]; exact h1)]
      wp_auto
      ipureintro; congr 1; simp [h0, h1]
    rw [decide_eq_true (show sint.Z gm.PrevLogIndex' ≤ sint.Z gs.Log'.len by rw [hpl, hlen]; exact h1)]
    wp_auto
    have hk2 : sint.Z (gm.PrevLogIndex' - W64 1) = m.prevLogIndex - 1 := by rw [← hpl]; word
    have hk0 : 0 ≤ sint.Z (gm.PrevLogIndex' - W64 1) ∧ sint.Z (gm.PrevLogIndex' - W64 1) < sint.Z gs.Log'.len := by
      rw [hk2, hlen]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk0)]
    have hkn : (sint.Z (gm.PrevLogIndex' - W64 1)).toNat < es.length := by rw [Hell, hk2]; omega
    obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z (gm.PrevLogIndex' - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hkn⟩
    obtain ⟨y, Hy⟩ : ∃ y, (st.s (uint.nat i)).log[(sint.Z (gm.PrevLogIndex' - W64 1)).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (Hell ▸ hkn)⟩
    ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx Hy $$ Hel
    iunfold entryRO at Hxy
    icases Hxy with ⟨%Hxy1, -⟩
    icases ownSlice_elem_acc _ x _ _ es hk0.1 Hx $$ Hes with ⟨#Hxe, -⟩
    icases typedPointsto_split _ _ _ $$ Hxe with Hxef
    simp only [TypedPointsto.typedPointstoDef]
    icases Hxef with ⟨#E1, #E2, #E3, -⟩
    wp_auto
    have he := sint_eq_iff gm.PrevLogTerm' x.Term' _ _ Hv.2.2.2.2.2.2.2.1 Hxy1.1
    have hidx : (m.prevLogIndex - 1).toNat = (sint.Z (gm.PrevLogIndex' - W64 1)).toNat := by rw [hk2]
    by_cases h2 : m.prevLogTerm = y.term
    · rw [decide_eq_true (he.2 h2)]
      have hpos : 0 < m.prevLogIndex := by omega
      ipureintro; congr 1; rw [hidx, Hy]; simp [h0, h1, h2, hpos]
    · rw [decide_eq_false (fun e => h2 (he.1 e))]
      have hpos : 0 < m.prevLogIndex := by omega
      ipureintro; congr 1; rw [hidx, Hy]; simp [h0, h1, h2, hpos]
  rename_i vv
  iintro %Hv0
  subst Hv0
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = (Bool.or (m.prevLogIndex == 0) (Bool.and (Bool.and (decide (m.prevLogIndex > 0)) (decide (m.prevLogIndex ≤ ((st.s (uint.nat i)).log.length : Int)))) (some m.prevLogTerm == (((st.s (uint.nat i)).log[(m.prevLogIndex - 1).toNat]?).map Entry.term)))) := ⟨_, rfl⟩
  rw [← hlo]
  wp_auto
  ipersist logOk
  have hle : sint.Z gm.Term' ≤ sint.Z gs.CurrentTerm' ↔ m.term ≤ (st.s (uint.nat i)).currentTerm := by
    rw [Hf.1, Hv.2.2.1]
  by_cases h0 : m.term ≤ (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h0 (hle.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.handleAppendEntriesRequest (uint.nat i) (uint.nat j) m = .ok [] := by
      unfold State.handleAppendEntriesRequest; simp [h0]; rfl
    rw [this]
    dsimp only
    iexists []
    ihave Hn := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hc := ownSliceCap_nil (V := Loc) (GF := GF)
    iframe Hn Hc
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  rw [decide_eq_true (hle.2 h0)]
  wp_auto
  wp_apply wp_reject p st i j q m lo $$ [Hst Hmsg] as %r1 Hr1
  · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok⟩
  try wp_auto
  wp_apply wp_rtf p st i q m $$ [Hst Hmsg] as %r2 Hr2
  · iframe Hst Hmsg; ipureintro; exact Hi
  try wp_auto
  ihave Hr1 : optOwnS (GF := GF) st.server r1 (st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo) $$ [Hr1]
  · cases ho : st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo with
    | none => simp only [optOwnS]; iexact Hr1
    | some s1 => simp only [optOwnS]; iframe Hr1; ipureintro; exact State.reject_server ho
  ihave Hr2 : optOwnS (GF := GF) st.server r2 (st.returnToFollowerState (uint.nat i) m) $$ [Hr2]
  · cases ho : st.returnToFollowerState (uint.nat i) m with
    | none => simp only [optOwnS]; iexact Hr2
    | some s1 => simp only [optOwnS]; iframe Hr2; ipureintro; exact State.returnToFollower_server ho
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  wp_apply wp_nonNil _ (DFrac.own 1) _
      [st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo, st.returnToFollowerState (uint.nat i) m]
      (fun r s => iprop(∃ M, stateOwn (GF := GF) r s M)) $$ [Hsl0 Hr1 Hr2] as %outA HA
  · iframe Hsl0
    have hl : ([r1, zero_val Loc].set (sint.nat (W64 (0 + 1))) r2) = [r1, r2] := rfl
    rw [hl]
    isplitl [Hr1 Hr2]
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr1]
      · iunfold optOwnS at Hr1
        cases st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo
        · iexact Hr1
        · icases Hr1 with ⟨H, -⟩; iexact H
      iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hr2]
      · iunfold optOwnS at Hr2
        cases st.returnToFollowerState (uint.nat i) m
        · iexact Hr2
        · icases Hr2 with ⟨H, -⟩; iexact H
      iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    imodintro
    iintro %r %s ⟨%M, Hs⟩
    iapply stateOwn_not_null $$ Hs
  try wp_auto
  cases ha : st.acceptAppendEntriesRequest (uint.nat i) (uint.nat j) lo m with
  | error e =>
    wp_apply wp_accept p st i j lo q m $$ [Hst Hmsg]
    · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok, Hsn, hp1, hp2, hll, hel⟩
    simp only [ha]
    iintro %r3 HF
    iexfalso; iexact HF
  | ok sts =>
  wp_apply wp_accept p st i j lo q m $$ [Hst Hmsg]
  · iframe Hst Hmsg; ipureintro; exact ⟨Hi, Hpok, Hmok, Hsn, hp1, hp2, hll, hel⟩
  simp only [ha]
  iintro %outB ⟨%qsB, HoutB, -, HB⟩
  icases HA with ⟨%qsA, HoutA, HcapA, HA⟩
  wp_apply wp_slice_append $$ [HoutA HcapA HoutB] as %out ⟨Hout, Hcap, -⟩
  · iframe
  try wp_auto
  have hsrvB := State.accept_server Hsn ha
  have hsrvA : ∀ s ∈ somes [st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo, st.returnToFollowerState (uint.nat i) m], s.server = st.server := by
    intro s hs
    simp only [somes, List.mem_filterMap, id, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain ⟨o, ho, hos⟩ := hs
    rcases ho with rfl | rfl
    · exact State.reject_server hos
    · exact State.returnToFollower_server hos
  ihave %HAl := BigSepL2.bigSepL2_length $$ HA
  ihave Hall := (BigSepL2.bigSepL2_append (Φ := fun _ r s => iprop(∃ M, stateOwn (GF := GF) r s M)) (Or.inl HAl)).2 $$ [HA HB]
  · iframe
  obtain ⟨ALL, hALL⟩ : ∃ L, L = somes [st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m lo, st.returnToFollowerState (uint.nat i) m] ++ sts := ⟨_, rfl⟩
  have hsrv : ∀ s ∈ ALL, s.server = st.server := by
    intro s hs; rw [hALL, List.mem_append] at hs
    rcases hs with hs | hs
    · exact hsrvA s hs
    · exact hsrvB s hs
  rw [← hALL]
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  irename i => Hip
  irename j => Hjp
  irename m => Hmp
  irename v => Hvp
  irename s => Hsp
  irename logOk => Hlop
  have hres : st.handleAppendEntriesRequest (uint.nat i) (uint.nat j) m =
      .ok (if m.term == (st.s (uint.nat i)).currentTerm then ALL.map (fun t => t.upd (uint.nat i) (fun w => { w with lead := uint.nat j })) else ALL) := by
    unfold State.handleAppendEntriesRequest
    simp only [← hlo] at ha ⊢
    simp [h0, ha, hALL]; rfl
  rw [hres]
  dsimp only
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]
    wp_auto
    imod statesOwn_persist _ _ $$ Hall with Hall
    imodintro
    iapply HΦ
    rw [show (m.term == (st.s (uint.nat i)).currentTerm) = false by simpa using h1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists _
    iframe
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  ihave %Hol := ownSlice_len $$ Hout
  ihave %HLl := BigSepL2.bigSepL2_length $$ Hall
  ihave IH : iprop(∃ (n : w64) (tv : Loc) (L : List State),
      "i" ∷ i_ptr ↦ n ∗ "t" ∷ t_ptr ↦ tv ∗
      "Hall" ∷ ([∗list] r;s ∈ qsA ++ qsB;L, ∃ M, stateOwn (GF := GF) r s M) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z out.len ∧ L.length = ALL.length ∧
        ∀ k, L[k]? = if k < sint.nat n then (ALL[k]?).map (fun (t : State) => t.upd (uint.nat i) (fun w => { w with lead := uint.nat j })) else ALL[k]?⌝) $$ [i t Hall]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, rfl, fun k => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hn0, hn1, hLl, hLk⟩ := Hn
  wp_if_destruct
  · have Hif : sint.Z n < sint.Z out.len := by simpa using Hif
    have Hlt : sint.nat n < (qsA ++ qsB).length := by rw [Hol.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, (qsA ++ qsB)[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have HlL : sint.nat n < L.length := by rw [hLl, ← HLl]; exact Hlt
    obtain ⟨s0, Hs0⟩ : ∃ s0, L[sint.nat n]? = some s0 := ⟨_, List.getElem?_eq_getElem HlL⟩
    have hs0 : ALL[sint.nat n]? = some s0 := by rw [← Hs0, hLk]; simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z out.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index out (sint.Z n) _ (DFrac.own 1) x hn0 $$ [Hout] as Hout
    · iframe Hout; ipureintro; exact Hx
    try wp_auto
    icases BigSepL2.bigSepL2_insert_acc (Φ := fun _ r s => iprop(∃ M, stateOwn (GF := GF) r s M)) Hx Hs0 $$ Hall with ⟨⟨%M0, Hst⟩, Hset⟩
    have Hi : uint.nat i ∈ s0.server := by rw [hsrv s0 (List.mem_of_getElem? hs0)]; exact Hi
    mut_open x, s0, M0, i, Hst
    try wp_auto
    ihave Hcp : cp ↦ ({ gc with Lead' := j } : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex
        VotesResponded VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp ({ gc with Lead' := j } : G.Server) mc ((fun (w : Server) => { w with lead := uint.nat j }) (s0.s (uint.nat i)))
      ⟨Hcf.1, Hcf.2.1, Hcf.2.2.1, rfl, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩ Hcmi $$ [Hcp Hcm]
    · iframe Hcp Hcm Hcl Hcr Hcg Hcc Hcd
    ihave Hs := stateOwnHole_close_upd _ _ _ _ _ (fun (w : Server) => { w with lead := uint.nat j }) Hi $$ [Hh Hc]
    · iframe
    ihave Hall := Hset $$ [Hs]
    · iexists _; iexact Hs
    have hset : (qsA ++ qsB).set (sint.nat n) x = qsA ++ qsB := by
      have : (qsA ++ qsB)[sint.nat n] = x := (List.getElem?_eq_some_iff.1 Hx).2
      rw [← this, List.set_getElem_self]
    rw [hset]
    wp_for_post
    iframe
    iexists _, _, (L.set (sint.nat n) (s0.upd (uint.nat i) (fun (w : Server) => { w with lead := uint.nat j })))
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [hLl], fun k => ?_⟩
    rw [List.getElem?_set, hLk k]
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    by_cases hk : k = sint.nat n
    · subst hk; simp [HlL, hs0]
    · have : (sint.nat n = k) = False := by simp; omega
      simp only [this, ite_false]
      by_cases hk2 : k < sint.nat n
      · simp [hk2, show k < sint.nat n + 1 by omega]
      · simp [hk2, show ¬ k < sint.nat n + 1 by omega]
  · have hnx : sint.nat n = ALL.length := by rw [← HLl, Hol.1]; word
    have hL : L = ALL.map (fun (t : State) => t.upd (uint.nat i) (fun w => { w with lead := uint.nat j })) := by
      apply List.ext_getElem?
      intro k
      rw [hLk k, List.getElem?_map, hnx]
      by_cases hk : k < ALL.length
      · simp [hk]
      · simp [hk, List.getElem?_eq_none (by omega : ALL.length ≤ k)]
    subst hL
    try wp_auto
    imod statesOwn_persist _ _ $$ Hall with Hall
    imodintro
    iapply HΦ
    rw [show (m.term == (st.s (uint.nat i)).currentTerm) = true by simpa using h1]
    simp only [↓reduceIte]
    iexists _
    iframe

end proof

end Etcdraft
end EtcdGrove
end Perennial
