/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.Granted`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Granted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsHas
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesHas
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `s.F[k]` of an `intsRO` slice. -/
theorem State.Granted_intsRO_at (sl : GoSlice) (xs : List Int) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) :
    intsRO (GF := GF) sl xs ⊢ ∃ w : w64, sliceAt sl k w ∗ ⌜sint.Z w = xs[sint.nat k]!⌝ := by
  iintro #H
  iunfold intsRO at H
  icases H with ⟨%ws, #Hws, %Hmap⟩
  subst Hmap
  iapply sliceRel_at (fun (w : w64) (x : Int) => sint.Z w = x) sl ws (ws.map sint.Z) k hk
    (by
      clear hk
      induction ws with
      | nil => exact .nil
      | cons w ws ih => exact .cons rfl ih)
  iexact Hws

theorem State.Granted_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

/-- The step of `State.granted`'s fold. -/
def State.Granted_G (s : State) (me : Str) (t : Int) (out : SSet) (j : Str) : SSet :=
  if j != me && s.msgs.contains { type := go!"grant", src := j, dst := me, term := t } then setAdd out j else out

theorem State.Granted_eq (s : State) (i : Nat) :
    s.granted i = (let out := s.cfg.server.foldl (State.Granted_G s s.cfg.server[i]! s.currentTerm[i]!) []
      if s.votes.contains { voter := s.cfg.server[i]!, term := s.currentTerm[i]!, cand := s.cfg.server[i]! }
      then setAdd out s.cfg.server[i]! else out) := rfl

theorem State.Granted_fold_len (s : State) (me : Str) (t : Int) :
    ∀ (l : List Str) (init : SSet), (l.foldl (State.Granted_G s me t) init).length ≤ init.length + l.length
  | [], _ => by simp
  | x :: l, init => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := State.Granted_fold_len s me t l (State.Granted_G s me t init x)
    have h2 : (State.Granted_G s me t init x).length ≤ init.length + 1 := by
      unfold State.Granted_G; split
      · exact State.Granted_setAdd_len init x
      · omega
    omega

theorem State.Granted_take_succ (f : SSet → Str → SSet) (l : List Str) (n : Nat) (y : Str)
    (h : l[n]? = some y) : (l.take (n + 1)).foldl f [] = f ((l.take n).foldl f []) y := by
  rw [List.take_add_one, h]
  simp

theorem State.Granted_arith (n : w64) (L : Nat) (hL : (L : Int) < 2 ^ 61) (hn0 : 0 ≤ sint.Z n) (hn : sint.Z n < L) :
    sint.nat n < L ∧ sint.nat (n + W64 1) = sint.nat n + 1 ∧ 0 ≤ sint.Z (n + W64 1) ∧
      sint.Z (n + W64 1) ≤ L ∧ (sint.nat n : Int) < 2 ^ 61 := by
  refine ⟨by word, by word, by word, by word, by word⟩

theorem State.Granted_natZ (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by word

theorem State.Granted.wp_proof (wp_factsHas : factsHas.spec (GF := GF) (hG := hG))
    (wp_SetAdd : SetAdd.spec (GF := GF) (hG := hG)) (wp_votesHas : votesHas.spec (GF := GF) (hG := hG)) :
    State.Granted.spec (GF := GF) (hG := hG) := by
  intro p s i
  wp_start as ⟨#Hs, %Hi0, %Hi1, %Hsl⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hc, #Hsv, #Hiv, %Hb⟩
  iStructNamed Hc
  iunfold strsRO at Hsv
  ihave %Hsvl := ownSlice_len $$ Hsv
  icases State.Granted_intsRO_at g.CurrentTerm' s.currentTerm i ⟨Hi0, by rw [HWf.len_currentTerm]; exact Hi1⟩ $$ HCurrentTerm with ⟨%w, #Hwa, %Hw⟩
  have hsv : s.cfg.server[sint.nat i]? = some s.cfg.server[sint.nat i]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl
  wp_auto
  wp_apply wp_load_index _ i _ _ Hi0 hsv $$ [Hsv]
  · iexact Hsv
  try wp_auto
  have hgl : sint.Z gc.Server'.len = s.cfg.server.length := by rw [Hsvl.1]; word
  ihave IH : iprop(∃ (n : w64) (jv : GoString) (ov : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "out" ∷ out_ptr ↦ ov ∗
      "Hov" ∷ strsRO ov ((s.cfg.server.take (sint.nat n)).foldl
        (State.Granted_G s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]!) []) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gc.Server'.len⌝)
      $$ [i j out]
  · iexists _, _, _
    iframe
    isplitr
    · iunfold strsRO
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
      iapply ownSlice_nil
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  icases Hov with #Hov
  obtain ⟨hn0, hn1⟩ := Hn
  wp_if_destruct
  · rw [hgl] at Hif
    obtain ⟨hlt, hn1', hp0, hp1, hn61⟩ := State.Granted_arith n _ Hsl hn0 Hif
    obtain ⟨y, hy⟩ : ∃ y, s.cfg.server[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hstep := State.Granted_take_succ (State.Granted_G s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]!)
      s.cfg.server (sint.nat n) y hy
    have hol := State.Granted_fold_len s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]!
      (s.cfg.server.take (sint.nat n)) []
    have htl : (s.cfg.server.take (sint.nat n)).length = sint.nat n := by
      rw [List.length_take]; omega
    rw [htl, List.length_nil] at hol
    wp_apply wp_load_index gc.Server' n s.cfg.server y hn0 hy $$ [Hsv]
    · iexact Hsv
    try wp_auto
    by_cases hym : y = s.cfg.server[sint.nat i]!
    · rw [decide_eq_true hym]
      try wp_auto
      have hG : ∀ o, State.Granted_G s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]! o y = o := by
        intro o; unfold State.Granted_G; rw [← hym, bne_self_eq_false, Bool.false_and]; rfl
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitr
      · rw [hn1', hstep, hG]; iexact Hov
      ipureintro; rw [hgl]; exact ⟨hp0, hp1⟩
    · rw [decide_eq_false hym]
      try wp_auto
      wp_apply wp_load_at _ _ w Hi0 $$ [Hwa]
      · iexact Hwa
      try wp_auto
      wp_apply wp_factsHas g.Msgs' s.msgs _
          { type := go!"grant", src := y, dst := s.cfg.server[sint.nat i]!, term := s.currentTerm[sint.nat i]! }
          $$ [HMsgs]
      · iframe HMsgs; ipureintro
        unfold factRel; simp only
        exact ⟨trivial, trivial, trivial, Hw, rfl, rfl, rfl⟩
      try wp_auto
      cases hc : s.msgs.contains
          { type := go!"grant", src := y, dst := s.cfg.server[sint.nat i]!, term := s.currentTerm[sint.nat i]! }
      · have hG : ∀ o, State.Granted_G s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]! o y = o := by
          intro o; unfold State.Granted_G; rw [hc, Bool.and_false]; rfl
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        isplitr
        · rw [hn1', hstep, hG]; iexact Hov
        ipureintro; rw [hgl]; exact ⟨hp0, hp1⟩
      · have hG : ∀ o, State.Granted_G s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]! o y = setAdd o y := by
          intro o; unfold State.Granted_G; rw [hc, show (y != s.cfg.server[sint.nat i]!) = true from bne_iff_ne.mpr hym, Bool.true_and]; rfl
        try wp_auto
        wp_apply wp_SetAdd ov _ y $$ [Hov] as %u #Hu
        · iframe Hov; ipureintro; omega
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        isplitr
        · rw [hn1', hstep, hG]; iexact Hu
        ipureintro; rw [hgl]; exact ⟨hp0, hp1⟩
  · try wp_auto
    have hnx : sint.nat n = s.cfg.server.length := by
      have := State.Granted_natZ n hn0; rw [hgl] at hn1 Hif; omega
    rw [hnx, List.take_length]
    have hol := State.Granted_fold_len s s.cfg.server[sint.nat i]! s.currentTerm[sint.nat i]! s.cfg.server []
    rw [List.length_nil] at hol
    wp_apply wp_load_at _ _ w Hi0 $$ [Hwa]
    · iexact Hwa
    try wp_auto
    wp_apply wp_votesHas g.Votes' s.votes _
        { voter := s.cfg.server[sint.nat i]!, term := s.currentTerm[sint.nat i]!, cand := s.cfg.server[sint.nat i]! }
        $$ [HVotes]
    · iframe HVotes; ipureintro
      unfold voteRel; simp only
      exact ⟨trivial, Hw, trivial⟩
    rw [State.Granted_eq]
    cases hc : s.votes.contains
        { voter := s.cfg.server[sint.nat i]!, term := s.currentTerm[sint.nat i]!, cand := s.cfg.server[sint.nat i]! }
    · try wp_auto
      simp only [Bool.false_eq_true, ↓reduceIte]
      iapply HΦ
      iexact Hov
    · try wp_auto
      wp_apply wp_SetAdd ov _ _ $$ [Hov] as %u #Hu
      · iframe Hov; ipureintro; omega
      try wp_auto
      simp only [↓reduceIte]
      iapply HΦ
      iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
