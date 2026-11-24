/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.Acked`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Acked
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd
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

theorem State.Acked_setAdd_len (s : SSet) (x : Str) : (setAdd s x).length ≤ s.length + 1 := by
  unfold setAdd
  simp only
  split
  · omega
  · simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
    omega

/-- `Acked`'s test of a message. -/
def State.Acked_P (me : Str) (t c : Int) (j : Str) (a : Fact) : Bool :=
  a.type == go!"ack" && a.src == j && a.dst == me && a.term == t && decide (a.index ≥ c)

/-- The step of `State.acked`'s fold. -/
def State.Acked_G (s : State) (me : Str) (t c : Int) (out : SSet) (j : Str) : SSet :=
  if s.msgs.any (State.Acked_P me t c j) then setAdd out j else out

theorem State.Acked_eq (s : State) (i : Nat) (t c : Int) :
    s.acked i t c = s.cfg.server.foldl (State.Acked_G s s.cfg.server[i]! t c) [] := rfl

theorem State.Acked_fold_len (s : State) (me : Str) (t c : Int) :
    ∀ (l : List Str) (init : SSet), (l.foldl (State.Acked_G s me t c) init).length ≤ init.length + l.length
  | [], _ => by simp
  | x :: l, init => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := State.Acked_fold_len s me t c l (State.Acked_G s me t c init x)
    have h2 : (State.Acked_G s me t c init x).length ≤ init.length + 1 := by
      unfold State.Acked_G; split
      · exact State.Acked_setAdd_len init x
      · omega
    omega

theorem State.Acked_take_succ {α β : Type} (f : β → α → β) (init : β) (l : List α) (n : Nat) (y : α)
    (h : l[n]? = some y) : (l.take (n + 1)).foldl f init = f ((l.take n).foldl f init) y := by
  rw [List.take_add_one, h]
  simp

theorem State.Acked_any_take_succ {α : Type} (f : α → Bool) (l : List α) (n : Nat) (x : α)
    (h : l[n]? = some x) : (l.take (n + 1)).any f = ((l.take n).any f || f x) := by
  rw [List.take_add_one, List.any_append, h]
  simp

theorem State.Acked_arith (n : w64) (L : Nat) (hL : (L : Int) < 2 ^ 61) (hn0 : 0 ≤ sint.Z n) (hn : sint.Z n < L) :
    sint.nat n < L ∧ sint.nat (n + W64 1) = sint.nat n + 1 ∧ 0 ≤ sint.Z (n + W64 1) ∧
      sint.Z (n + W64 1) ≤ L ∧ (sint.nat n : Int) < 2 ^ 61 := by
  refine ⟨by word, by word, by word, by word, by word⟩

theorem State.Acked_arith2 (n : w64) (L : Nat) (hL : (L : Int) < 2 ^ 63) (hn0 : 0 ≤ sint.Z n) (hn : sint.Z n < L) :
    sint.nat n < L ∧ sint.nat (n + W64 1) = sint.nat n + 1 ∧ 0 ≤ sint.Z (n + W64 1) ∧
      sint.Z (n + W64 1) ≤ L := by
  refine ⟨by word, by word, by word, by word⟩

theorem State.Acked_natZ (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by word

theorem State.Acked_P_false (me : Str) (t c : Int) (j : Str) (ga : G.Fact) (la : Fact) (tw cw : w64)
    (hr : factRel ga la) (ht : sint.Z tw = t) (hc : sint.Z cw = c)
    (h : ¬ ga.Type' = go!"ack" ∨ ¬ ga.Src' = j ∨ ¬ ga.Dst' = me ∨ ¬ ga.Term' = tw ∨ ¬ sint.Z cw ≤ sint.Z ga.Index') :
    State.Acked_P me t c j la = false := by
  obtain ⟨h1, h2, h3, h4, _, _, h7⟩ := hr
  unfold State.Acked_P
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not, ge_iff_le]
  rcases h with h | h | h | h | h
  · left; left; left; left; rw [← h1]; exact h
  · left; left; left; right; rw [← h2]; exact h
  · left; left; right; rw [← h3]; exact h
  · left; right; rw [← h4, ← ht]; intro h'; exact h (BitVec.toInt_inj.mp h')
  · right; rw [← h7, ← hc]; exact h

theorem State.Acked_P_true (me : Str) (t c : Int) (j : Str) (ga : G.Fact) (la : Fact) (tw cw : w64)
    (hr : factRel ga la) (ht : sint.Z tw = t) (hc : sint.Z cw = c)
    (h1' : ga.Type' = go!"ack") (h2' : ga.Src' = j) (h3' : ga.Dst' = me) (h4' : ga.Term' = tw)
    (h5' : sint.Z cw ≤ sint.Z ga.Index') :
    State.Acked_P me t c j la = true := by
  obtain ⟨h1, h2, h3, h4, _, _, h7⟩ := hr
  unfold State.Acked_P
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ge_iff_le]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← h1, h1']
  · rw [← h2, h2']
  · rw [← h3, h3']
  · rw [← h4, h4', ht]
  · rw [← h7, ← hc]; exact h5'

theorem State.Acked.wp_proof (wp_SetAdd : SetAdd.spec (GF := GF) (hG := hG)) :
    State.Acked.spec (GF := GF) (hG := hG) := by
  intro p s i t c
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
  iunfold factsRO at HMsgs
  icases HMsgs with ⟨%gms, #Hgms, %Hmrel⟩
  ihave %Hml := ownSlice_len $$ Hgms
  have hmgl := Hmrel.length_eq
  have hsv : s.cfg.server[sint.nat i]? = some s.cfg.server[sint.nat i]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by word)]; rfl
  have hgl : sint.Z gc.Server'.len = s.cfg.server.length := by rw [Hsvl.1]; word
  have hml : sint.Z g.Msgs'.len = s.msgs.length := by rw [← hmgl, Hml.1]; word
  have hml63 : (s.msgs.length : Int) < 2 ^ 63 := by rw [← hml]; word
  rw [State.Acked_eq]
  wp_auto
  wp_apply wp_load_index _ i _ _ Hi0 hsv $$ [Hsv]
  · iexact Hsv
  try wp_auto
  ihave IH : iprop(∃ (n : w64) (jv : GoString) (ov : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "out" ∷ out_ptr ↦ ov ∗
      "Hov" ∷ strsRO ov ((s.cfg.server.take (sint.nat n)).foldl
        (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []) ∗
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
    obtain ⟨hlt, hn1', hp0, hp1, hn61⟩ := State.Acked_arith n _ Hsl hn0 Hif
    obtain ⟨y, hy⟩ : ∃ y, s.cfg.server[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hstep := State.Acked_take_succ (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []
      s.cfg.server (sint.nat n) y hy
    have hol := State.Acked_fold_len s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)
      (s.cfg.server.take (sint.nat n)) []
    have htl : (s.cfg.server.take (sint.nat n)).length = sint.nat n := by
      rw [List.length_take]; omega
    rw [htl, List.length_nil] at hol
    wp_apply wp_load_index gc.Server' n s.cfg.server y hn0 hy $$ [Hsv]
    · iexact Hsv
    try wp_auto
    ihave IJ : iprop(∃ (m : w64) (av : G.Fact),
        "i" ∷ i_ptr ↦ m ∗ "a" ∷ a_ptr ↦ av ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z g.Msgs'.len ∧
          (s.msgs.take (sint.nat m)).any (State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y) = false⌝)
        $$ [i a]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmt⟩ := Hm
    wp_if_destruct
    · rw [hml] at Hif
      obtain ⟨hlt2, hm1', hq0, hq1⟩ := State.Acked_arith2 m _ hml63 hm0 Hif
      rw [← hml] at hq1
      have hlt2' : sint.nat m < gms.length := by rw [hmgl]; exact hlt2
      obtain ⟨ga, Hga⟩ : ∃ ga, gms[sint.nat m]? = some ga := ⟨_, List.getElem?_eq_getElem hlt2'⟩
      obtain ⟨la, Hla⟩ : ∃ la, s.msgs[sint.nat m]? = some la := ⟨_, List.getElem?_eq_getElem hlt2⟩
      have hra : factRel ga la := by
        have := forall₂_getElem Hmrel _ hlt2' hlt2
        rw [List.getElem?_eq_some_iff] at Hga Hla
        obtain ⟨_, Hga⟩ := Hga; obtain ⟨_, Hla⟩ := Hla
        rw [← Hga, ← Hla]; exact this
      wp_apply wp_load_index g.Msgs' m gms ga hm0 Hga $$ [Hgms]
      · iexact Hgms
      try wp_auto
      by_cases h0 : ga.Type' = go!"ack"
      · rw [decide_eq_true h0]
        try wp_auto
        by_cases h1 : ga.Src' = y
        · rw [decide_eq_true h1]
          try wp_auto
          by_cases h2 : ga.Dst' = s.cfg.server[sint.nat i]!
          · rw [decide_eq_true h2]
            try wp_auto
            by_cases h3 : ga.Term' = t
            · rw [decide_eq_true h3]
              try wp_auto
              by_cases h4 : sint.Z c ≤ sint.Z ga.Index'
              · rw [decide_eq_true h4]
                try wp_auto
                have hPt : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = true :=
                  State.Acked_P_true _ _ _ _ ga la t c hra rfl rfl h0 h1 h2 h3 h4
                have hany : s.msgs.any (State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y) = true :=
                  List.any_eq_true.mpr ⟨la, List.mem_of_getElem? Hla, hPt⟩
                try wp_auto
                wp_apply wp_SetAdd ov _ y $$ [Hov] as %u #Hu
                · iframe Hov; ipureintro; omega
                try wp_auto
                wp_for_post
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, _
                iframe
                isplitr
                · have hG : State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)
                      ((s.cfg.server.take (sint.nat n)).foldl (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []) y =
                      setAdd ((s.cfg.server.take (sint.nat n)).foldl (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []) y := by
                    unfold State.Acked_G; rw [hany]; rfl
                  rw [hn1', hstep, hG]; iexact Hu
                ipureintro; rw [hgl]; exact ⟨hp0, hp1⟩
              · rw [decide_eq_false h4]
                have hPf : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = false :=
                  State.Acked_P_false _ _ _ _ ga la t c hra rfl rfl (Or.inr (Or.inr (Or.inr (Or.inr h4))))
                try wp_auto
                wp_for_post
                iframe
                iexists _, _
                iframe
                ipureintro
                refine ⟨hq0, hq1, ?_⟩
                rw [hm1', State.Acked_any_take_succ _ _ _ la Hla, hmt, hPf]
            · rw [decide_eq_false h3]
              have hPf : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = false :=
                State.Acked_P_false _ _ _ _ ga la t c hra rfl rfl (Or.inr (Or.inr (Or.inr (Or.inl h3))))
              try wp_auto
              wp_for_post
              iframe
              iexists _, _
              iframe
              ipureintro
              refine ⟨hq0, hq1, ?_⟩
              rw [hm1', State.Acked_any_take_succ _ _ _ la Hla, hmt, hPf]
          · rw [decide_eq_false h2]
            have hPf : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = false :=
              State.Acked_P_false _ _ _ _ ga la t c hra rfl rfl (Or.inr (Or.inr (Or.inl h2)))
            try wp_auto
            wp_for_post
            iframe
            iexists _, _
            iframe
            ipureintro
            refine ⟨hq0, hq1, ?_⟩
            rw [hm1', State.Acked_any_take_succ _ _ _ la Hla, hmt, hPf]
        · rw [decide_eq_false h1]
          have hPf : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = false :=
            State.Acked_P_false _ _ _ _ ga la t c hra rfl rfl (Or.inr (Or.inl h1))
          try wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro
          refine ⟨hq0, hq1, ?_⟩
          rw [hm1', State.Acked_any_take_succ _ _ _ la Hla, hmt, hPf]
      · rw [decide_eq_false h0]
        have hPf : State.Acked_P s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c) y la = false :=
          State.Acked_P_false _ _ _ _ ga la t c hra rfl rfl (Or.inl h0)
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨hq0, hq1, ?_⟩
        rw [hm1', State.Acked_any_take_succ _ _ _ la Hla, hmt, hPf]
    · try wp_auto
      have hmx : sint.nat m = s.msgs.length := by
        have := State.Acked_natZ m hm0; rw [hml] at hm1 Hif; omega
      rw [hmx, List.take_length] at hmt
      have hG : State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)
          ((s.cfg.server.take (sint.nat n)).foldl (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []) y =
          ((s.cfg.server.take (sint.nat n)).foldl (State.Acked_G s s.cfg.server[sint.nat i]! (sint.Z t) (sint.Z c)) []) := by
        unfold State.Acked_G; rw [hmt]; rfl
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      isplitr
      · rw [hn1', hstep, hG]; iexact Hov
      ipureintro; rw [hgl]; exact ⟨hp0, hp1⟩
  · try wp_auto
    have hnx : sint.nat n = s.cfg.server.length := by
      have := State.Acked_natZ n hn0; rw [hgl] at hn1 Hif; omega
    rw [hnx, List.take_length]
    iapply HΦ
    iexact Hov

end proof

end AntCheck
end EtcdGrove
end Perennial
