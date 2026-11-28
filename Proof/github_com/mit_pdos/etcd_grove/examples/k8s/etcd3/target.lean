module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.target
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (WEvent Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The builtin `max` of two `uint64`s. -/
theorem wp_max_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ (m : w64), RET #m; ⌜uint.nat m = max (uint.nat a) (uint.nat b)⌝ }} := by
  wp_start
  wp_if_destruct
  all_goals (iapply HΦ; ipureintro; rw [Nat.max_def]; split <;> word)

theorem sint_lt4_iff (t : w64) (h : uint.nat t < 256) :
    sint.Z t < sint.Z (W64 4) ↔ uint.nat t < 4 := by
  word

theorem evMaxL_snoc (l : List WEv) (e : WEv) :
    k8s_dist.evMaxL (l ++ [e]) =
      if e.t < 4 then max (k8s_dist.evMaxL l) (uint.nat e.o.ResourceVersion') else k8s_dist.evMaxL l := by
  unfold k8s_dist.evMaxL
  rw [List.filter_append]
  by_cases h : e.t < 4 <;> simp [h, List.foldl_append]

theorem targetL_nf (x : Input) (y : Output) (rv : Nat) (h5 : x.Kind' ≠ W64 5) (h1 : y.Err' = W64 1) :
    k8s_dist.targetL x y rv = uint.nat y.ErrRV' := by
  unfold k8s_dist.targetL; rw [if_neg h5, if_pos h1]

theorem targetL_errNZ (x : Input) (y : Output) (rv : Nat) (h5 : x.Kind' ≠ W64 5) (h1 : y.Err' ≠ W64 1)
    (h0 : y.Err' ≠ W64 0) : k8s_dist.targetL x y rv = 0 := by
  unfold k8s_dist.targetL; rw [if_neg h5, if_neg h1, if_pos h0]

theorem targetL_write (x : Input) (y : Output) (rv : Nat)
    (hk : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) (h0 : y.Err' = W64 0) :
    k8s_dist.targetL x y rv = if rv < uint.nat y.RV' then uint.nat y.RV' - 1 else 0 := by
  have h5 : x.Kind' ≠ W64 5 := by rcases hk with h | h | h <;> rw [h] <;> decide
  have h4 : x.Kind' ≠ W64 4 := by rcases hk with h | h | h <;> rw [h] <;> decide
  unfold k8s_dist.targetL
  rw [if_neg h5, if_neg (by rw [h0]; decide), if_neg (fun h => h h0), if_neg h4, if_pos hk]

theorem targetL_read (x : Input) (y : Output) (rv : Nat) (h5 : x.Kind' ≠ W64 5)
    (hk : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)) (h0 : y.Err' = W64 0) :
    k8s_dist.targetL x y rv = match parseRVD x.MinRV' with
      | none => 0
      | some req => if x.Kind' = W64 4 then (if pastReadL x req then uint.nat req else uint.nat y.ListRV')
          else uint.nat req := by
  unfold k8s_dist.targetL
  rw [if_neg h5, if_neg (by rw [h0]; decide), if_neg (fun h => h h0)]
  by_cases h4 : x.Kind' = W64 4
  · rw [if_pos h4]; cases parseRVD x.MinRV' <;> simp [h4]
  · rw [if_neg h4, if_neg hk]; cases parseRVD x.MinRV' <;> simp only [if_neg h4]

theorem target.wp_proof
    (wp_decodeWEvents : decodeWEvents.spec (GF := GF) (hG := hG))
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_pastRead : pastRead.spec (GF := GF) (hG := hG)) :
    target.spec (GF := GF) (hG := hG) := by
  intro x y rv
  wp_start as -
  wp_auto
  wp_if_destruct
  · have hk5 : x.Kind' = W64 5 := by first | exact Hif | simpa using Hif
    cases hF : y.WFailed'
    case true =>
      (try wp_auto)
      iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF]
    (try wp_auto)
    cases hS : x.Skip'
    case true =>
      try simp only [hS]
      (try wp_auto)
      iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF, hS]
    try simp only [hS]
    (try wp_auto)
    wp_apply wp_decodeWEvents as %sl %ok Hd
    rcases hd : decWEventsL y.WEvents' with _ | all
    · isimp only [hd] at Hd
      icases Hd with %Hok
      subst Hok
      (try wp_auto)
      iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF, hS, hd]
    isimp only [hd] at Hd
    icases Hd with ⟨%Hok, Hw⟩
    subst Hok
    imod wevsOwnM_persist _ _ $$ Hw with #Hw
    unfold wevsOwn
    icases Hw with ⟨%ws, #Hk, %He⟩
    ihave %Hl := ownSlice_len $$ Hk
    have hty : ∀ e ∈ all, e.t < 256 := fun e he =>
      decWEventsL_t y.WEvents'.length y.WEvents' (Nat.le_refl _) all hd e he
    (try wp_auto)
    ihave HI : (∃ (j : w64) (evv : WEvent) (tv : w64) (sm : Bool),
        "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗ "t" ∷ t_ptr ↦ tv ∗ "some" ∷ some_ptr ↦ sm ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
          uint.nat tv = k8s_dist.evMaxL ((ws.map wevOf).take (sint.nat j)) ∧
          sm = ((ws.map wevOf).take (sint.nat j)).any (fun e => decide (e.t < 4))⌝ : IProp GF)
        $$ [i ev t some]
    · iexists W64 0, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩ <;>
        simp [k8s_dist.evMaxL, show sint.nat (0#64 : w64) = 0 from rfl] <;> rfl
    irename : (in_ptr ↦ x : IProp GF) => Hin
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
        ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
      list_elem ws (sint.nat j) as w
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z j) ws _ w Hj.1 $$ [Hk] as -
      · isplit
        · iexact Hk
        · ipureintro; exact Hw_lookup
      have hl : (ws.map wevOf)[sint.nat j]? = some (wevOf w) := by simp [Hw_lookup]
      have hmem : wevOf w ∈ all := by
        rw [← He]; exact List.mem_of_getElem? hl
      have ht := hty _ hmem
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have htake : (ws.map wevOf).take (sint.nat j + 1) =
          (ws.map wevOf).take (sint.nat j) ++ [wevOf w] := by
        rw [List.take_add_one, hl]; rfl
      have h4iff := sint_lt4_iff w.Type' (by simpa only [wevOf] using ht)
      wp_if_destruct
      · have h4 : uint.nat w.Type' < 4 := h4iff.1 Hif
        (try wp_auto)
        wp_apply wp_max_u64 as %m %Hm
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, w, m, true
        iframe
        ipureintro
        refine ⟨by word, by word, ?_, ?_⟩
        · rw [hj1, htake, evMaxL_snoc, Hm, ← Hj.2.2.1]
          simp [wevOf, h4]
        · rw [hj1, htake]
          simp [wevOf, h4]
      · have h4 : ¬ uint.nat w.Type' < 4 := fun h => Hif (h4iff.2 h)
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, w, tv, sm
        iframe
        ipureintro
        refine ⟨by word, by word, ?_, ?_⟩
        · rw [hj1, htake, evMaxL_snoc, Hj.2.2.1]
          simp [wevOf, h4]
        · rw [hj1, htake, Hj.2.2.2]
          simp [wevOf, h4]
    · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
      (try wp_auto)
      have hfull : (ws.map wevOf).take (sint.nat j) = ws.map wevOf :=
        List.take_of_length_le (by simp; word)
      rw [hfull, He] at Hj
      obtain ⟨-, -, Ht, rfl⟩ := Hj
      wp_if_destruct
      · have h2 : x.SendInit' = W64 2 := by first | exact Hif | simpa using Hif
        (try wp_auto)
        cases hsm : all.any (fun e => decide (e.t < 4))
        · (try wp_auto)
          iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF, hS, hd, h2, hsm, Ht]
        (try wp_auto)
        wp_apply wp_parseRV as %req %err Hp
        rcases hp : parseRVD x.MinRV' with _ | m <;> isimp only [hp] at Hp
        · icases Hp with ⟨%Herr, -⟩
          cases err with
          | nil => exact absurd rfl Herr
          | ok i =>
            (try wp_auto)
            iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF, hS, hd, h2, hsm, hp, Ht]
        · icases Hp with ⟨%he, %hm⟩
          subst he hm
          (try wp_auto)
          wp_apply wp_max_u64 as %m1 %Hm1
          wp_apply wp_max_u64 as %m2 %Hm2
          (try wp_auto)
          iapply HΦ; ipureintro
          simp only [k8s_dist.targetL, hk5, hF, hS, hd, h2, hsm, hp, Ht, ↓reduceIte]
          rw [Hm2, Hm1, Ht]
          simp
      · have h2 : x.SendInit' ≠ W64 2 := by first | exact Hif | simpa using Hif
        (try wp_auto)
        iapply HΦ; ipureintro; simp [k8s_dist.targetL, hk5, hF, hS, hd, Ht]
        intro h; exact absurd h h2
  have hk5 : x.Kind' ≠ W64 5 := by first | exact Hif | simpa using Hif
  wp_if_destruct
  · have h1 : y.Err' = W64 1 := by first | exact Hif | simpa using Hif
    (try wp_auto)
    iapply HΦ; ipureintro; rw [targetL_nf x y _ hk5 h1]; (try rfl)
  have h1 : y.Err' ≠ W64 1 := by first | exact Hif | simpa using Hif
  by_cases h0 : y.Err' = W64 0
  · rw [decide_eq_true h0]
    (try wp_auto)
    wp_if_destruct
    · have hk2 : x.Kind' = W64 2 := by first | exact Hif | simpa using Hif
      have hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by exact Or.inr (Or.inr hk2)
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_pos (by word)]; word
      · (try wp_auto)
        iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_neg (by word)]; rfl
    · have hk2 : x.Kind' ≠ W64 2 := by first | exact Hif | simpa using Hif
      (try wp_auto)
      wp_if_destruct
      · have hk1 : x.Kind' = W64 1 := by first | exact Hif | simpa using Hif
        have hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by exact Or.inr (Or.inl hk1)
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_pos (by word)]; word
        · (try wp_auto)
          iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_neg (by word)]; rfl
      · have hk1 : x.Kind' ≠ W64 1 := by first | exact Hif | simpa using Hif
        (try wp_auto)
        wp_if_destruct
        · have hk0 : x.Kind' = W64 0 := by first | exact Hif | simpa using Hif
          have hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by exact Or.inl hk0
          (try wp_auto)
          wp_if_destruct
          · (try wp_auto)
            iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_pos (by word)]; word
          · (try wp_auto)
            iapply HΦ; ipureintro; rw [targetL_write x y _ hw h0, if_neg (by word)]; rfl
        · have hk0 : x.Kind' ≠ W64 0 := by first | exact Hif | simpa using Hif
          have hw : ¬ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
            rintro (h | h | h) <;> contradiction
          (try wp_auto)
          wp_apply wp_parseRV as %req %err Hp
          rw [targetL_read x y _ hk5 hw h0]
          rcases hp : parseRVD x.MinRV' with _ | m <;> isimp only [hp] at Hp
          · icases Hp with ⟨%Herr, -⟩
            cases err with
            | nil => exact absurd rfl Herr
            | ok i =>
              (try wp_auto)
              iapply HΦ; ipureintro; rfl
          · icases Hp with ⟨%he, %hm⟩
            subst he hm
            (try wp_auto)
            wp_if_destruct
            · have h4 : x.Kind' = W64 4 := by first | exact Hif | simpa using Hif
              wp_apply wp_pastRead
              cases hpr : pastReadL x req
              · (try wp_auto)
                iapply HΦ; ipureintro; simp only [if_pos h4, hpr]; rfl
              · (try wp_auto)
                iapply HΦ; ipureintro; simp only [if_pos h4, hpr]; rfl
            · have h4 : x.Kind' ≠ W64 4 := by first | exact Hif | simpa using Hif
              (try wp_auto)
              iapply HΦ; ipureintro; simp only [if_neg h4]
  · rw [decide_eq_false h0]
    (try wp_auto)
    iapply HΦ; ipureintro; rw [targetL_errNZ x y _ hk5 h1 h0]; (try rfl)

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
