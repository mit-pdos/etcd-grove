module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListReadConsistency
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

theorem ListReadConsistency.wp_proof
    (wp_Parse : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    ListReadConsistency.spec (GF := GF) (hG := hG) := by
  intro x hparse
  have hS : (listOptsV x).SendInitialEvents' = null := rfl
  have hRV : (listOptsV x).ResourceVersion' = x.MinRV' := rfl
  have hM : (listOptsV x).ResourceVersionMatch' = matchOptL x := rfl
  have hC : (listOptsV x).Predicate'.Continue' = [] := rfl
  have hR : (listOptsV x).Recursive' = x.Recursive' := rfl
  have hL : (listOptsV x).Predicate'.Limit' = x.Limit' := rfl
  generalize listOptsV x = opts at hS hRV hM hC hR hL
  wp_start as #Hdrv
  wp_auto
  rw [hS, decide_eq_true rfl]
  wp_auto
  iStructNamed opts
  iStructNamed Predicate
  rw [hM]
  by_cases hmo : matchOptL x = []
  · rw [decide_eq_true hmo]
    wp_auto
    rw [hR]
    cases hr : x.Recursive'
    · try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hl2
      try wp_auto
      have hz : (W64 (opts.ResourceVersion'.length : Int) = W64 0) ↔ x.MinRV' = [] := by
        rw [hRV] at hl2 ⊢
        constructor
        · intro h
          have : x.MinRV'.length = 0 := by word
          exact List.length_eq_zero_iff.mp this
        · intro h; rw [h]; rfl
      have hm12 : ¬ (x.Match' = W64 1 ∨ x.Match' = W64 2) := by
        unfold matchOptL at hmo
        by_cases h1 : x.Match' = W64 1 <;> by_cases h2 : x.Match' = W64 2 <;> simp_all
      by_cases hrv : x.MinRV' = []
      · rw [decide_eq_true (hz.2 hrv)]
        simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyConsistent]
        wp_auto
        iapply HΦ
        ipureintro
        unfold listConsL; rw [if_pos hrv, if_neg hm12]; simp [rconsStr]
      · rw [decide_eq_false (fun h => hrv (hz.1 h))]
        wp_auto
        obtain ⟨prv, hprv⟩ := Option.isSome_iff_exists.1 hparse
        rw [hRV]
        wp_apply wp_Parse as %n %perr Hp
        isimp [hprv] at Hp
        icases Hp with %hp
        obtain ⟨rfl, rfl⟩ := hp
        wp_auto
        rw [hmo, decide_eq_false (by simp)]
        wp_auto
        simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
        wp_auto
        iapply HΦ
        ipureintro
        have h1 : ¬ x.Match' = W64 1 := fun h => hm12 (Or.inl h)
        have h2 : ¬ x.Match' = W64 2 := fun h => hm12 (Or.inr h)
        unfold listConsL
        rw [if_neg hrv, hprv]
        simp only [if_neg h1, if_neg h2, hr, Bool.false_and, Bool.false_eq_true, ↓reduceIte, rconsStr]
        simp
    · wp_auto
      rw [hC]
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hl2
      try wp_auto
      have hz : (W64 (opts.ResourceVersion'.length : Int) = W64 0) ↔ x.MinRV' = [] := by
        rw [hRV] at hl2 ⊢
        constructor
        · intro h
          have : x.MinRV'.length = 0 := by word
          exact List.length_eq_zero_iff.mp this
        · intro h; rw [h]; rfl
      have hm12 : ¬ (x.Match' = W64 1 ∨ x.Match' = W64 2) := by
        unfold matchOptL at hmo
        by_cases h1 : x.Match' = W64 1 <;> by_cases h2 : x.Match' = W64 2 <;> simp_all
      by_cases hrv : x.MinRV' = []
      · rw [decide_eq_true (hz.2 hrv)]
        simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyConsistent]
        wp_auto
        iapply HΦ
        ipureintro
        unfold listConsL; rw [if_pos hrv, if_neg hm12]; simp [rconsStr]
      · rw [decide_eq_false (fun h => hrv (hz.1 h))]
        wp_auto
        obtain ⟨prv, hprv⟩ := Option.isSome_iff_exists.1 hparse
        rw [hRV]
        wp_apply wp_Parse as %n %perr Hp
        isimp [hprv] at Hp
        icases Hp with %hp
        obtain ⟨rfl, rfl⟩ := hp
        wp_auto
        rw [hmo, decide_eq_false (by simp)]
        wp_auto
        have h1 : ¬ x.Match' = W64 1 := fun h => hm12 (Or.inl h)
        have h2 : ¬ x.Match' = W64 2 := fun h => hm12 (Or.inr h)
        rw [hL]
        by_cases hl : sint.Z (W64 0) < sint.Z x.Limit'
        · have hl0 : 0 < sint.Z x.Limit' := hl
          rw [decide_eq_true hl]
          wp_auto
          by_cases hp0 : n = 0
          · subst hp0
            wp_auto
            simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
            wp_auto
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1, if_neg h2]
            simp [hr, hl0, rconsStr]
          · rw [decide_eq_true (show uint.Z (W64 0) < uint.Z n by word)]
            simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyExact]
            wp_auto
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1, if_neg h2]
            simp only [hr, hl0, rconsStr, Bool.true_and, decide_true, ne_eq, hp0, not_false_eq_true,
              decide_not, Bool.not_false]
            simp
        · have hl0 : ¬ 0 < sint.Z x.Limit' := hl
          rw [decide_eq_false hl]
          wp_auto
          simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
          wp_auto
          iapply HΦ
          ipureintro
          unfold listConsL
          rw [if_neg hrv, hprv]
          simp only [if_neg h1, if_neg h2]
          simp [hr, hl0, rconsStr]
  · rw [decide_eq_false hmo]
    wp_auto
    rw [hRV]
    have hm12 : x.Match' = W64 1 ∨ x.Match' = W64 2 := by
      unfold matchOptL at hmo
      by_cases h1 : x.Match' = W64 1 <;> by_cases h2 : x.Match' = W64 2 <;> simp_all
    ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    by_cases hrv : x.MinRV' = []
    · rw [decide_eq_true hrv]
      wp_auto
      wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e -
      · iframe #
        isplitl
        · iapply ownSlice_nil
        fmt_args_intro; itrivial
      iapply HΦ
      ipureintro
      unfold listConsL
      rw [if_pos hrv, if_pos hm12]
      nofun
    · rw [decide_eq_false hrv]
      wp_auto
      rw [hC]
      wp_auto
      rw [hR]
      cases hr : x.Recursive'
      · try wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hl2
        try wp_auto
        try rw [hRV]
        have hne : ¬ (W64 (x.MinRV'.length : Int) = W64 0) := by
          intro h
          try rw [hRV] at hl2
          apply hrv
          have : x.MinRV'.length = 0 := by word
          exact List.length_eq_zero_iff.mp this
        rw [decide_eq_false hne]
        wp_auto
        obtain ⟨prv, hprv⟩ := Option.isSome_iff_exists.1 hparse
        try rw [hRV]
        wp_apply wp_Parse as %n %perr Hp
        isimp [hprv] at Hp
        icases Hp with %hp
        obtain ⟨rfl, rfl⟩ := hp
        wp_auto
        try rw [hM]
        rcases hm12 with h1 | h1
        · have hmv : matchOptL x = go!"NotOlderThan" := by simp [matchOptL, h1]
          rw [hmv, decide_eq_true rfl]
          simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
          wp_auto
          iapply HΦ
          ipureintro
          unfold listConsL
          rw [if_neg hrv, hprv]
          simp [h1, rconsStr]
        · have h1' : ¬ x.Match' = W64 1 := by rw [h1]; decide
          have hmv : matchOptL x = go!"Exact" := by simp [matchOptL, h1, h1']
          rw [hmv]
          wp_auto
          by_cases hn0 : n = W64 0
          · rw [decide_eq_true hn0]
            wp_auto
            wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e -
            · iframe #
              isplitl
              · iapply ownSlice_nil
              fmt_args_intro; itrivial
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1', if_pos h1]
            have h0 : n = 0 := hn0
            rw [if_pos h0]
            simp
          · rw [decide_eq_false hn0]
            simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyExact]
            wp_auto
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1', if_pos h1]
            have h0 : ¬ n = 0 := hn0
            rw [if_neg h0]
            simp [rconsStr]
      · wp_auto
        try rw [hC]
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
        try wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hl2
        try wp_auto
        try rw [hRV]
        have hne : ¬ (W64 (x.MinRV'.length : Int) = W64 0) := by
          intro h
          try rw [hRV] at hl2
          apply hrv
          have : x.MinRV'.length = 0 := by word
          exact List.length_eq_zero_iff.mp this
        rw [decide_eq_false hne]
        wp_auto
        obtain ⟨prv, hprv⟩ := Option.isSome_iff_exists.1 hparse
        try rw [hRV]
        wp_apply wp_Parse as %n %perr Hp
        isimp [hprv] at Hp
        icases Hp with %hp
        obtain ⟨rfl, rfl⟩ := hp
        wp_auto
        try rw [hM]
        rcases hm12 with h1 | h1
        · have hmv : matchOptL x = go!"NotOlderThan" := by simp [matchOptL, h1]
          rw [hmv, decide_eq_true rfl]
          simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyNotOlderThan]
          wp_auto
          iapply HΦ
          ipureintro
          unfold listConsL
          rw [if_neg hrv, hprv]
          simp [h1, rconsStr]
        · have h1' : ¬ x.Match' = W64 1 := by rw [h1]; decide
          have hmv : matchOptL x = go!"Exact" := by simp [matchOptL, h1, h1']
          rw [hmv]
          wp_auto
          by_cases hn0 : n = W64 0
          · rw [decide_eq_true hn0]
            wp_auto
            wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e -
            · iframe #
              isplitl
              · iapply ownSlice_nil
              fmt_args_intro; itrivial
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1', if_pos h1]
            have h0 : n = 0 := hn0
            rw [if_pos h0]
            simp
          · rw [decide_eq_false hn0]
            simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ConsistencyExact]
            wp_auto
            iapply HΦ
            ipureintro
            unfold listConsL
            rw [if_neg hrv, hprv]
            simp only [if_neg h1', if_pos h1]
            have h0 : ¬ n = 0 := hn0
            rw [if_neg h0]
            simp [rconsStr]

end proof

end k8s_correctness
end EtcdGrove
end Perennial
