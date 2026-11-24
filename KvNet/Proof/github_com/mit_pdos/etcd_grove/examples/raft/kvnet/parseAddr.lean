/-
The proof of `KvNet/Spec/.../kvnet/parseAddr.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.parseAddr
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.AddrOk
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.decimal

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

set_option hygiene false in
/-- `parseAddr`'s loop at a piece's end (`hPn`: the piece is the address's `n`-th part; `hnext`,
`hlast`: what the split gives after it): `decimal` takes it, `v[n]`, `n` and `start` move on. -/
local macro "pa_store" : tactic => `(tactic| (
  rw [if_pos ⟨Hst0, by word, by word⟩]
  try wp_auto
  wp_apply wp_decimal as %x %good %Hdec
  obtain ⟨m, hm, -⟩ := Hdecs _ _ hPn
  rw [show uint.nat (W64 65535) = 65535 from rfl, hm] at Hdec
  cases good
  · simp at Hdec
  simp only [↓reduceIte, Option.some.injEq] at Hdec
  try wp_auto
  rw [decide_eq_false (show ¬ sint.Z (W64 5) ≤ sint.Z n by word)]
  try wp_auto
  obtain ⟨wn, hwn⟩ : ∃ w, vs[sint.nat n]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) _ (sint.Z n) _ _ (array.mk 5 vs : GoArray w64 5) wn Hn0 hwn $$ v
    with ⟨Hel, Hcl⟩
  try wp_auto
  rw [if_pos ⟨Hn0, by word⟩]
  try wp_auto
  ihave v := Hcl $$ Hel
  wp_for_post
  iframe
  iexists i + W64 1, n + W64 1, i + W64 1, _
  iframe
  ipureintro
  have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
  have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
  refine ⟨by simp [Hvl], by word, by word, by word, by word, ?_, ?_, ?_⟩
  · intro q hq
    rw [hn1] at hq
    rcases (show q < sint.nat n ∨ q = sint.nat n by omega) with hq | rfl
    · obtain ⟨x', w', h1, h2, h3⟩ := Hpre q hq
      refine ⟨x', w', h1, ?_, h3⟩
      rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_set_ne (by omega)]
      exact h2
    · refine ⟨_, x, hPn, ?_, by rw [hm, Hdec]⟩
      rw [show (sint.Z n).toNat = sint.nat n from rfl,
        List.getElem?_set_self (by show sint.nat n < vs.length; omega)]
  · intro hle
    rw [hi1] at hle
    obtain ⟨h1, h2⟩ := hnext hle
    rw [hi1, hn1, Nat.sub_self, List.take_zero]
    exact ⟨by omega, h1, h2⟩
  · intro hlt
    rw [hi1] at hlt
    rw [hn1]
    exact hlast hlt))

theorem parseAddr.wp_proof
    (wp_AddrOk : AddrOk.spec (GF := GF) (hG := hG))
    (wp_decimal : decimal.spec (GF := GF) (hG := hG)) :
    parseAddr.spec (GF := GF) (hG := hG) := by
  intro a _ha
  wp_start
  try wp_auto
  wp_apply wp_AddrOk a $$ [$Hpkg]
  try wp_auto
  cases hok : addrOk a
  · -- refused
    try wp_auto
    iapply HΦ
    ipureintro
    exact ⟨rfl, fun h => by cases h⟩
  obtain ⟨h, p, x1, x2, x3, x4, n1, n2, n3, n4, pt, h58, h46, d1, d2, d3, d4, dp,
    b1, b2, b3, b4, b5, hpo⟩ := addrOk_parts hok
  have hpt : pt ≤ 65535 := by
    unfold portOk at hpo; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hpo
    omega
  have hP : splitAny a [] = [x1, x2, x3, x4, p] := addrOk_splitAny h58 h46 d1 d2 d3 d4 dp
  have Hdecs : ∀ (k : Nat) (x : GoString), [x1, x2, x3, x4, p][k]? = some x →
      ∃ m, decimalM x 65535 = some m ∧ (k < 4 → m ≤ 255) := by
    intro k x hk
    have e : ∀ {y : GoString} {m : Nat}, decNat y = some m → m ≤ 65535 → decimalM y 65535 = some m :=
      fun hy hm => (decimalM_iff _ 65535 _ (by decide)).2 ⟨hy, hm⟩
    match k, hk with
    | 0, hk => cases hk; exact ⟨n1, e d1 (by omega), fun _ => by omega⟩
    | 1, hk => cases hk; exact ⟨n2, e d2 (by omega), fun _ => b3⟩
    | 2, hk => cases hk; exact ⟨n3, e d3 (by omega), fun _ => b4⟩
    | 3, hk => cases hk; exact ⟨n4, e d4 (by omega), fun _ => b5⟩
    | 4, hk => cases hk; exact ⟨pt, e dp hpt, fun h => absurd h (by omega)⟩
    | k + 5, hk => simp at hk
  try wp_auto
  ihave HI : (∃ (i n st : w64) (vs : List w64),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ n ∗ "start" ∷ start_ptr ↦ st ∗
      "v" ∷ v_ptr ↦ (array.mk 5 vs : GoArray w64 5) ∗
      "%Hinv" ∷ ⌜vs.length = 5 ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z n ∧ 0 ≤ sint.Z st ∧
        sint.nat i ≤ a.length + 1 ∧
        (∀ q, q < sint.nat n → ∃ x w, [x1, x2, x3, x4, p][q]? = some x ∧ vs[q]? = some w ∧
          decimalM x 65535 = some (uint.nat w)) ∧
        (sint.nat i ≤ a.length → sint.nat st ≤ sint.nat i ∧ sint.nat n ≤ 4 ∧
          splitAny (a.drop (sint.nat i)) ((a.drop (sint.nat st)).take (sint.nat i - sint.nat st)) =
            [x1, x2, x3, x4, p].drop (sint.nat n)) ∧
        (a.length < sint.nat i → sint.nat n = 5)⌝ : IProp GF)
    $$ [i n start v]
  · iexists W64 0, W64 0, W64 0, List.replicate 5 (W64 0)
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨rfl, by decide, by decide, by decide, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
    all_goals rw [h0] at *
    all_goals first | omega | (simp; done) | (simp [hP]; done)
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · obtain ⟨Hvl, Hi0, Hn0, Hst0, Hile, Hpre, Hrun, -⟩ := Hinv
    have Hc : sint.Z i ≤ sint.Z (W64 (a.length : Int)) := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hil : sint.nat i ≤ a.length := by word
    obtain ⟨Hsti, Hn4, Hsplit⟩ := Hrun hil
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    by_cases hend : sint.nat i = a.length
    · rw [decide_eq_true (show i = W64 (a.length : Int) by word)]
      try wp_auto
      have hdl : a.drop (sint.nat i) = [] := by rw [hend, List.drop_length]
      rw [hdl, splitAny.eq_1] at Hsplit
      have hn4 : sint.nat n = 4 := by
        have := congrArg List.length Hsplit
        simp only [List.length_cons, List.length_nil, List.length_drop] at this
        omega
      have hPn : [x1, x2, x3, x4, p][sint.nat n]? =
          some ((a.drop (sint.nat st)).take (sint.nat i - sint.nat st)) := by
        rw [hn4] at Hsplit ⊢
        have e4 : [x1, x2, x3, x4, p].drop 4 = [p] := rfl
        rw [e4, List.cons.injEq] at Hsplit
        rw [Hsplit.1]; rfl
      have hnext : sint.nat i + 1 ≤ a.length → sint.nat n + 1 ≤ 4 ∧
          splitAny (a.drop (sint.nat i + 1)) [] = [x1, x2, x3, x4, p].drop (sint.nat n + 1) :=
        fun h => absurd h (by omega)
      have hlast : a.length < sint.nat i + 1 → sint.nat n + 1 = 5 := fun _ => by omega
      pa_store
    · have hilt : sint.nat i < a.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, a[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hilt⟩
      have hdrop : a.drop (sint.nat i) = c :: a.drop (sint.nat i + 1) := by
        rw [List.drop_eq_getElem_cons hilt]
        rw [List.getElem?_eq_getElem hilt] at hc
        rw [Option.some.inj hc]
      rw [decide_eq_false (show ¬ i = W64 (a.length : Int) by intro h; apply hend; subst h; word)]
      repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
      have hsep : ∀ (sep : w8), (sep = 46 ∨ sep = 58) → c = sep → (
          [x1, x2, x3, x4, p][sint.nat n]? =
            some ((a.drop (sint.nat st)).take (sint.nat i - sint.nat st)) ∧
          (sint.nat i + 1 ≤ a.length → sint.nat n + 1 ≤ 4 ∧
            splitAny (a.drop (sint.nat i + 1)) [] = [x1, x2, x3, x4, p].drop (sint.nat n + 1)) ∧
          (a.length < sint.nat i + 1 → sint.nat n + 1 = 5)) := by
        intro sep hs hcs
        subst hcs
        rw [hdrop, splitAny.eq_2, if_pos hs] at Hsplit
        have hlen : sint.nat n < [x1, x2, x3, x4, p].length := Nat.lt_succ_of_le Hn4
        have hd : [x1, x2, x3, x4, p].drop (sint.nat n) =
            [x1, x2, x3, x4, p][sint.nat n] :: [x1, x2, x3, x4, p].drop (sint.nat n + 1) :=
          List.drop_eq_getElem_cons hlen
        rw [hd, List.cons.injEq] at Hsplit
        refine ⟨?_, ?_, ?_⟩
        · rw [List.getElem?_eq_getElem hlen, Hsplit.1]
        rotate_left
        · intro h; exact absurd h (by omega)
        intro _
        refine ⟨?_, Hsplit.2⟩
        have hne := splitAny_ne_nil (a.drop (sint.nat i + 1)) []
        rw [Hsplit.2] at hne
        refine Classical.byContradiction fun hcon => hne (List.drop_eq_nil_of_le ?_)
        show 5 ≤ sint.nat n + 1
        omega
      by_cases h46 : c = W8 46
      · rw [decide_eq_true h46]
        repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
        obtain ⟨hPn, hnext, hlast⟩ := hsep 46 (Or.inl rfl) h46
        pa_store
      · rw [decide_eq_false h46]
        repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
        by_cases h58 : c = W8 58
        · rw [decide_eq_true h58]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
          obtain ⟨hPn, hnext, hlast⟩ := hsep 58 (Or.inr rfl) h58
          pa_store
        · rw [decide_eq_false h58]
          repeat (first | (simp only [Hi0, ↓reduceIte, hc]) | wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, n, st, vs
          iframe
          ipureintro
          have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
          have hcst : (a.drop (sint.nat st))[sint.nat i - sint.nat st]? = some c := by
            rw [List.getElem?_drop, show sint.nat st + (sint.nat i - sint.nat st) = sint.nat i by omega]
            exact hc
          refine ⟨Hvl, by word, Hn0, Hst0, by omega, Hpre, fun _ => ⟨by omega, Hn4, ?_⟩,
            fun h => absurd h (by omega)⟩
          rw [hi1, show sint.nat i + 1 - sint.nat st = (sint.nat i - sint.nat st) + 1 by omega,
            take_succ_of _ _ _ hcst, ← Hsplit, hdrop, splitAny.eq_2,
            if_neg (show ¬ (c = 46 ∨ c = 58) from fun e => e.elim h46 h58)]
  · obtain ⟨Hvl, Hi0, Hn0, Hst0, Hile, Hpre, -, Hdone⟩ := Hinv
    have Hge : ¬ sint.Z i ≤ sint.Z (W64 (a.length : Int)) := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hn5 : sint.nat n = 5 := Hdone (by word)
    rw [hn5] at Hpre
    obtain ⟨y0, w0, h0x, h0w, h0d⟩ := Hpre 0 (by omega)
    obtain ⟨y1, w1, h1x, h1w, h1d⟩ := Hpre 1 (by omega)
    obtain ⟨y2, w2, h2x, h2w, h2d⟩ := Hpre 2 (by omega)
    obtain ⟨y3, w3, h3x, h3w, h3d⟩ := Hpre 3 (by omega)
    obtain ⟨y4, w4, h4x, h4w, h4d⟩ := Hpre 4 (by omega)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0x h1x h2x h3x h4x
    subst h0x h1x h2x h3x h4x
    have e : ∀ {y : GoString} {m m' : Nat}, decNat y = some m → decimalM y 65535 = some m' → m' = m :=
      fun hy hm => by
        have := ((decimalM_iff _ 65535 _ (by decide)).1 hm).1
        rw [hy] at this; exact (Option.some.inj this).symm
    have v0 := e d1 h0d
    have v1 := e d2 h1d
    have v2 := e d3 h2d
    have v3 := e d4 h3d
    have v4 := e dp h4d
    have hn : n = W64 5 := by word
    subst hn
    ipersist v
    icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ (array.mk 5 vs : GoArray w64 5) w0 (by decide) h0w $$ v
      with ⟨#Hv0, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ (array.mk 5 vs : GoArray w64 5) w1 (by decide) h1w $$ v
      with ⟨#Hv1, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ (array.mk 5 vs : GoArray w64 5) w2 (by decide) h2w $$ v
      with ⟨#Hv2, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 3)) _ _ (array.mk 5 vs : GoArray w64 5) w3 (by decide) h3w $$ v
      with ⟨#Hv3, -⟩
    icases array_acc (GF := GF) _ (sint.Z (W64 4)) _ _ (array.mk 5 vs : GoArray w64 5) w4 (by decide) h4w $$ v
      with ⟨#Hv4, -⟩
    have g0 : ¬ uint.Z (W64 255) < uint.Z w0 := by have := b1; word
    have g1 : ¬ uint.Z (W64 255) < uint.Z w1 := by have := b3; word
    have g2 : ¬ uint.Z (W64 255) < uint.Z w2 := by have := b4; word
    have g3 : ¬ uint.Z (W64 255) < uint.Z w3 := by have := b5; word
    repeat (first | (simp only [decide_eq_false g0, decide_eq_false g1, decide_eq_false g2,
      decide_eq_false g3, ↓reduceIte, Bool.false_eq_true]) | wp_auto)
    iapply HΦ
    ipureintro
    refine ⟨rfl, fun _ => ?_⟩
    rw [parseAddrM_parts hok h58 h46 d1 d2 d3 d4 dp]
    have c0 : W8 (n1 : Int) = W8 (uint.Z w0) := by rw [← v0]; try word
    have c1 : W8 (n2 : Int) = W8 (uint.Z w1) := by rw [← v1]; try word
    have c2 : W8 (n3 : Int) = W8 (uint.Z w2) := by rw [← v2]; try word
    have c3 : W8 (n4 : Int) = W8 (uint.Z w3) := by rw [← v3]; try word
    have c4 : W64 (pt : Int) = w4 := by rw [← v4]; word
    rw [c0, c1, c2, c3, c4]

end proof

end raft_kvnet
end EtcdGrove
end Perennial
