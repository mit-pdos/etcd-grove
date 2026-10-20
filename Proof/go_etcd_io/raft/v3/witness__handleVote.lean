/-
Proof of `Spec/go_etcd_io/raft/v3/witness__handleVote.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.witness__handleVote
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Proof.go_etcd_io.raft.v3.LemmasWitness
public import Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- One more voter of the replication set counted iff it responded. -/
theorem votesInSet_take_succ (rs : List w64) (votes : GMap w64 Bool) (j : Nat) (x : w64)
    (Hx : rs[j]? = some x) :
    votesInSet (rs.take (j + 1)) votes =
      votesInSet (rs.take j) votes + (if (votes !! x).isSome then 1 else 0) := by
  unfold votesInSet
  rw [List.take_add_one, Hx]
  simp only [Option.toList_some, List.filter_append, List.length_append]
  cases h : (votes !! x).isSome <;> simp [List.filter, h]

theorem votesInSet_le (rs : List w64) (votes : GMap w64 Bool) :
    votesInSet rs votes ≤ rs.length := by
  unfold votesInSet; exact List.length_filter_le _ _

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `_, ok := votes[k]` in a nil-or-read-only tally. -/
theorem wp_votes_lookup2 (mref : Loc) (votes : GMap w64 Bool) (k : w64) :
    {{ (⌜mref = map.nil ∧ votes = ∅⌝ ∨ mref ↦$□ votes : IProp GF) }}
      (App (App (Val (map.lookup2 go.uint64 go.bool)) (Val #mref)) (Val #k))
    {{ RET (PairV #((votes !! k).getD false) #(decide ((votes !! k).isSome))); True }} := by
  iintro %Φ #H HΦ
  icases H with (⟨%Hn, %He⟩ | #Hm)
  · subst Hn He
    wp_auto
    simp only [GMap.lookup_empty, Option.getD_none, Option.isSome_none, Bool.false_eq_true,
      decide_false]
    iapply HΦ; itrivial
  · wp_apply wp_map_lookup2 $$ Hm as -
    iapply HΦ; itrivial

/-- `len(votes)` of a nil-or-read-only tally. -/
theorem wp_votes_len (mref : Loc) (votes : GMap w64 Bool) :
    {{ (⌜mref = map.nil ∧ votes = ∅⌝ ∨ mref ↦$□ votes : IProp GF) }}
      (App (Val #(functions go.len [go.uint64.MapType go.bool])) (Val #mref))
    {{ RET #(W64 (GMap.size votes)); ⌜GMap.size votes < 2 ^ 63⌝ }} := by
  iintro %Φ #H HΦ
  icases H with (⟨%Hn, %He⟩ | #Hm)
  · subst Hn He
    wp_auto
    simp only [GMap.map_size_empty]
    try simp only [Int.natCast_zero, Int.ofNat_eq_coe]
    iapply HΦ
    ipureintro; simp
  · wp_apply wp_map_len_lt $$ Hm as ⟨-, %Hs⟩
    iapply HΦ
    ipureintro; exact Hs

/-- The answer's head built first; `canVote`, then `reject` (the responders of the tally counted
over the stored replication set), the vote recorded on a grant (not a pre-vote's); the answer
sealed with its `Reject`, then its `Term`. -/
theorem witness.handleVote.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetLead : raftpb.WitnessHardState.GetLead.spec (GF := GF) (hG := hG))
    (wp_GetLastLogTerm : raftpb.WitnessHardState.GetLastLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetLastLogSubterm : raftpb.WitnessHardState.GetLastLogSubterm.spec (GF := GF) (hG := hG)) :
    witness.handleVote.spec (GF := GF) (hG := hG) := by
  intro w id mv μ q st
  wp_start as ⟨#Hid, #Hm, Hq⟩
  ihave #Hm' := Hm
  iunfold ownWMsg at Hm'
  icases Hm' with ⟨%s0, %s1, %Hmv, #Hs0, #Hs1, #Hvot, #Hctx⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  iunfold whsOwn at Hq
  iNamed Hq
  iunfold hsF at Hhs
  iNamed Hhs
  iunfold whsRest at Hr
  iNamed Hr
  iapply wp_fupd
  wp_auto
  rw [Hty]
  -- the answer's type
  wp_bind (If (Val #(decide (μ.ty = W32 17))) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      msgType_ptr ↦ ((if μ.ty = MsgPreVote then MsgPreVoteResp else MsgVoteResp :
        raftpb.MessageType))))) $$ [msgType]
  · by_cases hpv : μ.ty = W32 17
    · rw [decide_eq_true hpv,
        show raftpb.MsgPreVoteResp = #((W32 18 : raftpb.MessageType)) from rfl]
      wp_auto
      rw [if_pos (show μ.ty = MsgPreVote from hpv)]
      rw [show MsgPreVoteResp = W32 18 from rfl]
      iframe msgType
      ipureintro; rfl
    · rw [decide_eq_false hpv,
        show raftpb.MsgVoteResp = #((W32 6 : raftpb.MessageType)) from rfl]
      wp_auto
      rw [if_neg (show ¬ μ.ty = MsgPreVote from hpv), show MsgVoteResp = W32 6 from rfl]
      iframe msgType
      ipureintro; rfl
  iintro %v ⟨%Hv, msgType⟩
  subst Hv
  wp_auto
  -- the answer's head: `Type: msgType.Enum()`, `To: m.From`, `From: w.id`
  wp_method_call
  try wp_auto
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum _ as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cTo
  imod cellRO_alloc $$ «$v2» with #cFr
  -- `canVote`
  wp_bind (If (If _ (Val #true) _) (Val #true) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)))⌝ ∗
      q.[raftpb.WitnessHardState, go!"State"] ↦ ps ∗
      ps.[raftpb.HardState, go!"Term"] ↦ pt ∗ ps.[raftpb.HardState, go!"Vote"] ↦ pv ∗
      q.[raftpb.WitnessHardState, go!"Lead"] ↦ pld ∗ m_ptr ↦ mv ∗ st_ptr ↦ q))) $$ [HS HT HV HLd m st]
  · -- the first two disjuncts
    wp_bind (If (App (Val (GoInstruction (GoOp GoEquals go.uint64))) _) (Val #true) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)))⌝ ∗
        q.[raftpb.WitnessHardState, go!"State"] ↦ ps ∗ ps.[raftpb.HardState, go!"Vote"] ↦ pv ∗
        q.[raftpb.WitnessHardState, go!"Lead"] ↦ pld ∗ m_ptr ↦ mv ∗ st_ptr ↦ q))) $$ [HS HV HLd m st]
    · wp_apply wp_GetState.1 q (DFrac.own 1) ps $$ [$HS] as HS
      · ipureintro; exact Hnn
      try wp_auto
      wp_apply wp_GetVote.2.2 ps (DFrac.own 1) pv st.vote $$ [$HV $cV] as HV
      · ipureintro; exact Hsn
      try wp_auto
      rw [Hfr]
      by_cases c1 : st.vote = μ.frm
      · rw [decide_eq_true c1]
        wp_auto
        iframe HS HV HLd m st
        ipureintro; rw [decide_eq_true (Or.inl c1 : (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)))]
      rw [decide_eq_false c1]
      wp_auto
      wp_apply wp_GetState.1 q (DFrac.own 1) ps $$ [$HS] as HS
      · ipureintro; exact Hnn
      try wp_auto
      wp_apply wp_GetVote.2.2 ps (DFrac.own 1) pv st.vote $$ [$HV $cV] as HV
      · ipureintro; exact Hsn
      try wp_auto
      by_cases c2 : st.vote = W64 0
      · rw [decide_eq_true c2]
        wp_auto
        wp_apply wp_GetLead.1 q (DFrac.own 1) pld st.lead $$ [$HLd $cLd] as HLd
        · ipureintro; exact Hnn
        try wp_auto
        iframe HS HV HLd m st
        ipureintro
        by_cases c3 : st.lead = W64 0
        · rw [decide_eq_true c3, decide_eq_true (Or.inr ⟨c2, c3⟩ : (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)))]
        · rw [decide_eq_false c3,
            decide_eq_false (show ¬ (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)) by rintro (h | ⟨-, h⟩) <;> contradiction)]
      · rw [decide_eq_false c2]
        wp_auto
        iframe HS HV HLd m st
        ipureintro
        rw [decide_eq_false (show ¬ (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)) by rintro (h | ⟨h, -⟩) <;> contradiction)]
    iintro %v ⟨%Hv, HS, HV, HLd, m, st⟩
    subst Hv
    by_cases d12 : (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0))
    · rw [decide_eq_true d12]
      wp_auto
      iframe HS HT HV HLd m st
      ipureintro
      rw [decide_eq_true (show (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)) from d12.elim Or.inl (fun h => Or.inr (Or.inl h)))]
    rw [decide_eq_false d12]
    wp_auto
    -- the third, `m.Type == MsgPreVote && m.Term > st.GetState().GetTerm()`
    try rw [Hty]
    try rw [show raftpb.MsgPreVote = #((W32 17 : raftpb.MessageType)) from rfl]
    have hn12 : ∀ h : (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)), ¬ (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0)) → μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term := by
      rintro (h | h | h) hn
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
      · exact h
    by_cases c4 : μ.ty = W32 17
    · rw [decide_eq_true c4]
      wp_auto
      wp_apply wp_GetState.1 q (DFrac.own 1) ps $$ [$HS] as HS
      · ipureintro; exact Hnn
      try wp_auto
      wp_apply wp_GetTerm.2.2 ps (DFrac.own 1) pt st.term $$ [$HT $cT] as HT
      · ipureintro; exact Hsn
      try wp_auto
      rw [Hte]
      iframe HS HT HV HLd m st
      ipureintro
      by_cases c5 : uint.Z st.term < uint.Z μ.term
      · rw [decide_eq_true c5, decide_eq_true (show (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)) from Or.inr (Or.inr ⟨c4, c5⟩))]
      · rw [decide_eq_false c5, decide_eq_false (fun h => c5 (hn12 h d12).2)]
    · rw [decide_eq_false c4]
      wp_auto
      iframe HS HT HV HLd m st
      ipureintro
      rw [decide_eq_false (fun h => c4 (hn12 h d12).1)]
  iintro %v ⟨%Hv, HS, HT, HV, HLd, m, st⟩
  subst Hv
  wp_auto
  -- `reject`
  wp_bind (If (Val #(decide (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)))) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ reject_ptr ↦ (if (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)) then (if ltPair μ.lt μ.ls st.lt st.ls then true else if μ.lt = st.lt ∧ μ.ls = st.ls then decide (votesInSet st.rs μ.votes ≠ GMap.size μ.votes) else false) else true) ∗
      m_ptr ↦ mv ∗ st_ptr ↦ q ∗
      q.[raftpb.WitnessHardState, go!"LastLogTerm"] ↦ plt ∗
      q.[raftpb.WitnessHardState, go!"LastLogSubterm"] ↦ pls ∗
      q.[raftpb.WitnessHardState, go!"ReplicationSet"] ↦ srs))) $$ [reject m st HLt HLs HRs]
  · by_cases hcv : (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term))
    · rw [decide_eq_true hcv, if_pos hcv]
      wp_auto
      -- `m.LastLogTerm < st.GetLastLogTerm() || (== && m.LastLogSubterm < ...)`
      wp_bind (If _ (Val #true) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (ltPair μ.lt μ.ls st.lt st.ls))⌝ ∗
          m_ptr ↦ mv ∗ st_ptr ↦ q ∗ q.[raftpb.WitnessHardState, go!"LastLogTerm"] ↦ plt ∗
          q.[raftpb.WitnessHardState, go!"LastLogSubterm"] ↦ pls))) $$ [m st HLt HLs]
      · try wp_auto
        wp_apply wp_GetLastLogTerm.1 q (DFrac.own 1) plt st.lt $$ [$HLt $cLt] as HLt
        · ipureintro; exact Hnn
        try wp_auto
        rw [Hlt]
        by_cases hlt : uint.Z μ.lt < uint.Z st.lt
        · rw [decide_eq_true hlt]
          wp_auto
          iframe m st HLt HLs
          ipureintro
          rw [show decide (ltPair μ.lt μ.ls st.lt st.ls) = true from decide_eq_true (Or.inl hlt)]
        · rw [decide_eq_false hlt]
          wp_auto
          wp_apply wp_GetLastLogTerm.1 q (DFrac.own 1) plt st.lt $$ [$HLt $cLt] as HLt
          · ipureintro; exact Hnn
          try wp_auto
          rw [Hlt]
          by_cases heq : μ.lt = st.lt
          · rw [decide_eq_true heq]
            wp_auto
            wp_apply wp_GetLastLogSubterm.1 q (DFrac.own 1) pls st.ls $$ [$HLs $cLs] as HLs
            · ipureintro; exact Hnn
            try wp_auto
            rw [Hls]
            iframe m st HLt HLs
            ipureintro
            by_cases hls : uint.Z μ.ls < uint.Z st.ls
            · rw [decide_eq_true hls,
                show decide (ltPair μ.lt μ.ls st.lt st.ls) = true from decide_eq_true (Or.inr ⟨heq, hls⟩)]
            · rw [decide_eq_false hls,
                show decide (ltPair μ.lt μ.ls st.lt st.ls) = false from decide_eq_false (by
                  rintro (h | ⟨-, h⟩) <;> contradiction)]
          · rw [decide_eq_false heq]
            wp_auto
            iframe m st HLt HLs
            ipureintro
            rw [show decide (ltPair μ.lt μ.ls st.lt st.ls) = false from decide_eq_false (by
              rintro (h | ⟨h, -⟩) <;> contradiction)]
      iintro %v ⟨%Hv, m, st, HLt, HLs⟩
      subst Hv
      wp_if_destruct
      · -- below the stored pair: rejected
        have hlp := Hif
        rw [if_pos hlp]
        iframe reject m st HLt HLs HRs
      have hlp := Hif
      rw [if_neg hlp]
      -- `m.LastLogTerm == st.GetLastLogTerm() && m.LastLogSubterm == st.GetLastLogSubterm()`
      wp_bind (If (App (Val (GoInstruction (GoOp GoEquals go.uint64))) _) _ (Val #false))
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (μ.lt = st.lt ∧ μ.ls = st.ls))⌝ ∗
          m_ptr ↦ mv ∗ st_ptr ↦ q ∗ q.[raftpb.WitnessHardState, go!"LastLogTerm"] ↦ plt ∗
          q.[raftpb.WitnessHardState, go!"LastLogSubterm"] ↦ pls))) $$ [m st HLt HLs]
      · wp_apply wp_GetLastLogTerm.1 q (DFrac.own 1) plt st.lt $$ [$HLt $cLt] as HLt
        · ipureintro; exact Hnn
        try wp_auto
        rw [Hlt]
        by_cases heq : μ.lt = st.lt
        · rw [decide_eq_true heq]
          wp_auto
          wp_apply wp_GetLastLogSubterm.1 q (DFrac.own 1) pls st.ls $$ [$HLs $cLs] as HLs
          · ipureintro; exact Hnn
          try wp_auto
          rw [Hls]
          iframe m st HLt HLs
          ipureintro
          by_cases hls : μ.ls = st.ls
          · rw [decide_eq_true hls, decide_eq_true ⟨heq, hls⟩]
          · rw [decide_eq_false hls, decide_eq_false (fun h => hls h.2)]
        · rw [decide_eq_false heq]
          wp_auto
          iframe m st HLt HLs
          ipureintro
          rw [decide_eq_false (fun h => heq h.1)]
      iintro %v ⟨%Hv, m, st, HLt, HLs⟩
      subst Hv
      wp_if_destruct
      · -- the same pair: the responders of the tally counted over the stored replication set
        have heq := Hif
        rw [if_pos heq]
        ihave %Hlen := ownSlice_len _ _ _ $$ Hrs
        ihave HI : (∃ (j cnt xv : w64), "i" ∷ i_ptr ↦ j ∗ "votesInSet" ∷ votesInSet_ptr ↦ cnt ∗
            "x" ∷ x_ptr ↦ xv ∗ "m" ∷ m_ptr ↦ mv ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (st.rs.length : Int) ∧
              sint.Z cnt = (votesInSet (st.rs.take (sint.Z j).toNat) μ.votes : Int)⌝ : IProp GF)
          $$ [i votesInSet x m]
        · iexists W64 0, W64 0, _
          iframe i votesInSet x m
          ipureintro
          refine ⟨by word, by word, ?_⟩
          simp [votesInSet]
        wp_for HI
        wp_if_destruct
        · -- `x = st.ReplicationSet[j]`
          have Hlt : (sint.Z j).toNat < st.rs.length := by word
          obtain ⟨xk, Hxk⟩ : ∃ xk, st.rs[(sint.Z j).toNat]? = some xk :=
            ⟨_, List.getElem?_eq_getElem Hlt⟩
          simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z srs.len from ⟨Hj.1, Hif⟩]
          wp_apply wp_load_slice_index srs (sint.Z j) st.rs DFrac.discard xk Hj.1 $$ [Hrs] as -
          · iframe Hrs; ipureintro; exact Hxk
          try wp_auto
          wp_apply wp_votes_lookup2 mv.Votes' μ.votes xk $$ [Hvot]
          · iexact Hvot
          try wp_auto
          have Hstep := votesInSet_take_succ st.rs μ.votes (sint.Z j).toNat xk Hxk
          have Hle := votesInSet_le (st.rs.take ((sint.Z j).toNat + 1)) μ.votes
          have Hlt2 : (st.rs.length : Int) < 2 ^ 63 := by word
          have Htl : (st.rs.take ((sint.Z j).toNat + 1)).length ≤ st.rs.length := by
            rw [List.length_take]; exact Nat.min_le_right _ _
          cases hv : (μ.votes !! xk).isSome
          · rw [hv] at Hstep
            wp_auto
            wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 by word, Hstep]
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact Hj.2.2
          · rw [hv] at Hstep
            wp_auto
            wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro
            have Hc1 : (votesInSet (st.rs.take (sint.Z j).toNat) μ.votes : Int) + 1 < 2 ^ 63 := by
              have := votesInSet_le (st.rs.take (sint.Z j).toNat) μ.votes
              have := List.length_take_le (sint.Z j).toNat st.rs
              omega
            refine ⟨by word, by word, ?_⟩
            rw [show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 by word, Hstep]
            simp only [↓reduceIte]
            push_cast
            word
        · -- `reject = votesInSet != len(m.Votes)`
          try wp_auto
          wp_apply wp_votes_len mv.Votes' μ.votes $$ [Hvot] as %Hsz
          · iexact Hvot
          try wp_auto
          have hj : (sint.Z j).toNat = st.rs.length := by word
          have hc : sint.Z cnt = (votesInSet st.rs μ.votes : Int) := by
            rw [Hj.2.2, hj, List.take_length]
          have Hle := votesInSet_le st.rs μ.votes
          have hr : (!decide (cnt = W64 (GMap.size μ.votes))) =
              decide (votesInSet st.rs μ.votes ≠ GMap.size μ.votes) := by
            by_cases h : votesInSet st.rs μ.votes = GMap.size μ.votes
            · have : cnt = W64 (GMap.size μ.votes) := by rw [← h]; word
              simp [this, h]
            · have : cnt ≠ W64 (GMap.size μ.votes) := fun e => h (by subst e; word)
              simp [h]; exact this
          rw [hr]
          iframe reject m st HLt HLs HRs
          ipureintro; rfl
      · -- neither: granted
        have heq := Hif
        rw [if_neg heq]
        iframe reject m st HLt HLs HRs
    · rw [decide_eq_false hcv]
      wp_auto
      rw [if_neg hcv]
      iframe reject m st HLt HLs HRs
      ipureintro; rfl
  iintro %v ⟨%Hv, reject, m, st, HLt, HLs, HRs⟩
  subst Hv
  generalize hrej : (if (st.vote = μ.frm ∨ (st.vote = W64 0 ∧ st.lead = W64 0) ∨ (μ.ty = MsgPreVote ∧ uint.Z st.term < uint.Z μ.term)) then (if ltPair μ.lt μ.ls st.lt st.ls then true else if μ.lt = st.lt ∧ μ.ls = st.ls then decide (votesInSet st.rs μ.votes ≠ GMap.size μ.votes) else false) else true) = rej
  wp_auto
  -- `if m.Type == MsgVote && !reject { st.State.Vote = new(m.From) }`
  wp_bind (If (If _ _ (Val #false)) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ pv' : Loc,
      ps.[raftpb.HardState, go!"Vote"] ↦ pv' ∗
      cellRO pv' (if μ.ty = MsgVote ∧ rej = false then μ.frm else st.vote) ∗
      m_ptr ↦ mv ∗ st_ptr ↦ q ∗ q.[raftpb.WitnessHardState, go!"State"] ↦ ps ∗
      reject_ptr ↦ rej))) $$ [HV m st HS reject]
  · iapply wp_fupd
    try wp_auto
    try rw [Hty]
    try rw [show raftpb.MsgVote = #((W32 5 : raftpb.MessageType)) from rfl]
    by_cases hv : μ.ty = W32 5
    · rw [decide_eq_true hv]
      wp_auto
      cases rej
      · wp_auto
        imod cellRO_alloc $$ «$r0» with #cV'
        imodintro
        isplitr
        · ipureintro; rfl
        iexists _
        iframe HV m st HS reject
        rw [if_pos (show μ.ty = MsgVote ∧ false = false from ⟨hv, rfl⟩), ← Hfr]
        iexact cV'
      · wp_auto
        imodintro
        isplitr
        · ipureintro; rfl
        iexists pv
        iframe HV m st HS reject
        rw [if_neg (show ¬ (μ.ty = MsgVote ∧ true = false) by simp)]
        iexact cV
    · rw [decide_eq_false hv]
      wp_auto
      imodintro
      isplitr
      · ipureintro; rfl
      iexists pv
      iframe HV m st HS reject
      rw [if_neg (show ¬ (μ.ty = MsgVote ∧ rej = false) from fun h => hv h.1)]
      iexact cV
  iintro %v ⟨%Hv, %pv', HV, #cV', m, st, HS, reject⟩
  subst Hv
  wp_auto
  -- the answer sealed with its `Reject`
  irename : («$r0_ptr» ↦ rej : IProp GF) => Hrj
  imod cellRO_alloc $$ Hrj with #cRj
  imod msgOwn_lit _ _ (respM (if μ.ty = MsgPreVote then MsgPreVoteResp else MsgVoteResp) μ.frm id (W64 0) (W64 0) rej) [] ⊤ $$ [«$r0»] with Hmsg
  · simp only [respM, ← Hfr]
    ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
    iframe «$r0» Hnilb cTy cTo cFr cRj
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    msg_nulls
  wp_apply wp_GetReject.1 _ (DFrac.own 1) DFrac.discard false _ $$ [$Hmsg] as Hmsg
  simp only [respM]
  icases msgPtsC_store_Term _ _ _ _ $$ Hmsg with ⟨%pte, HTe, HbackT⟩
  cases rej
  · -- granted: the request's term
    wp_auto
    imod cellRO_alloc $$ «$r0» with #cTe
    ihave Hmsg := HbackT $$ %_ %_ HTe cTe
    have hw : wVote id st μ = (WHS.mk st.term
        (if μ.ty = MsgVote ∧ false = false then μ.frm else st.vote) st.commit st.li st.lt st.ls
        st.lead st.rs st.rsOut, (respM (if μ.ty = MsgPreVote then MsgPreVoteResp else MsgVoteResp) μ.frm id μ.term (W64 0) false, [])) := by
      unfold wVote
      simp only [hrej]
      split <;> rfl
    rw [hw, ← Hte]
    imodintro
    iapply HΦ
    isplitl [HS HT HV HC HLi HLt HLs HLd HRs HRo]
    · unfold whsOwn
      iexists ps
      iframe HS
      isplitl [HT HV HC]
      · unfold hsF
        iexists _, _, _, _
        isplitr
        · ipureintro; exact Hsn
        iframe HT cT HV cV' HC cC Hpbs
      unfold whsRest
      iexists _, _, _, _, _, _, _
      isplitr
      · ipureintro; exact Hnn
      iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb
    simp only [respM]
    try dsimp only
    iexact Hmsg
  · -- rejected: the state's term
    wp_auto
    wp_apply wp_GetState.1 q (DFrac.own 1) ps $$ [$HS] as HS
    · ipureintro; exact Hnn
    try wp_auto
    wp_apply wp_GetTerm.2.2 ps (DFrac.own 1) pt st.term $$ [$HT $cT] as HT
    · ipureintro; exact Hsn
    try wp_auto
    imod cellRO_alloc $$ «$r0» with #cTe
    ihave Hmsg := HbackT $$ %_ %_ HTe cTe
    have hw : wVote id st μ = (WHS.mk st.term
        (if μ.ty = MsgVote ∧ true = false then μ.frm else st.vote) st.commit st.li st.lt st.ls
        st.lead st.rs st.rsOut, (respM (if μ.ty = MsgPreVote then MsgPreVoteResp else MsgVoteResp) μ.frm id st.term (W64 0) true, [])) := by
      unfold wVote
      simp only [hrej]
      split <;> rfl
    rw [hw]
    imodintro
    iapply HΦ
    isplitl [HS HT HV HC HLi HLt HLs HLd HRs HRo]
    · unfold whsOwn
      iexists ps
      iframe HS
      isplitl [HT HV HC]
      · unfold hsF
        iexists _, _, _, _
        isplitr
        · ipureintro; exact Hsn
        iframe HT cT HV cV' HC cC Hpbs
      unfold whsRest
      iexists _, _, _, _, _, _, _
      isplitr
      · ipureintro; exact Hnn
      iframe HLi cLi HLt cLt HLs cLs HLd cLd HRs Hrs HRo Hro Hpb
    simp only [respM]
    try dsimp only
    iexact Hmsg

end proof

end EtcdGrove
end Perennial
