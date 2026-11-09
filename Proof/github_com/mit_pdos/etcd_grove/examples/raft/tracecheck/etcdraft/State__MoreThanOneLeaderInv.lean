/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__MoreThanOneLeaderInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__MoreThanOneLeaderInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StateRead

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

-- The inner loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "mtol_cont" : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by clear hmt hnt hstep hG; word, by clear hmt hnt hstep hG; word, ?_⟩
    rw [hm1]
    exact hstep.2 hG))

theorem State.MoreThanOneLeaderInv.wp_proof : State.MoreThanOneLeaderInv.spec (GF := GF) (hG := hG) := by
  intro p st
  wp_start as #Hst
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hm, #Hpm, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  iunfold setRO at Hsrv
  icases Hsrv with ⟨%xs, #Hxs, %Hmap⟩
  ihave %Hlen := ownSlice_len $$ Hxs
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  let F : ID → Bool := fun i => st.server.all (fun j =>
    Bool.or (!((st.s i).currentTerm == (st.s j).currentTerm && (st.s i).state == leader &&
      (st.s j).state == leader)) (i == j))
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Server'.len ∧ (st.server.take (sint.nat n)).all F = true⌝)
      $$ [i Hgi]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by clear hnt; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsy := set_getElem Hmap Hy
    have Hyin : uint.nat y ∈ st.server := List.mem_of_getElem? Hsy
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index g.Server' (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    rename_i oi_ptr
    irename : (oi_ptr ↦ n : IProp GF) => Hoi
    ihave IJ : iprop(∃ (m z : w64),
        "i" ∷ i_ptr ↦ m ∗ "j" ∷ j_ptr ↦ z ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z g.Server'.len ∧
          (st.server.take (sint.nat m)).all (fun j =>
            Bool.or (!((st.s (uint.nat y)).currentTerm == (st.s j).currentTerm &&
              (st.s (uint.nat y)).state == leader && (st.s j).state == leader)) (uint.nat y == j)) = true⌝)
        $$ [i j]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmt⟩ := Hm
    wp_if_destruct
    · have Hlt2 : sint.nat m < xs.length := by clear hmt hnt; rw [Hlen.1]; word
      obtain ⟨y2, Hy2⟩ : ∃ y, xs[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      have Hsy2 := set_getElem Hmap Hy2
      have Hyin2 : uint.nat y2 ∈ st.server := List.mem_of_getElem? Hsy2
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z g.Server'.len from ⟨hm0, Hif⟩))]
      wp_apply wp_load_slice_index g.Server' (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hy2
      try wp_auto
      icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
      icases servers_at st sm y2 Hyin2 $$ Hsrvs with ⟨%qj, %Hqj, #Hvj⟩
      iunfold serverRO at Hvi Hvj
      icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, -, -, -, -, -, -, -⟩
      icases Hvj with ⟨%gj, %mj, #Hqj', %Hfj, -, -, -, -, -, -, -⟩
      icases typedPointsto_split _ _ _ $$ Hqi' with Hqif
      icases typedPointsto_split _ _ _ $$ Hqj' with Hqjf
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hqif
      iNamed Hqjf
      wp_apply wp_map_lookup1 $$ [HS] as -
      · iexact HS
      rw [Hqi]
      simp only [Option.getD_some]
      try wp_auto
      wp_apply wp_map_lookup1 $$ [HS] as -
      · iexact HS
      rw [Hqj]
      simp only [Option.getD_some]
      try wp_auto
      simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
      have hT : gi.CurrentTerm' = gj.CurrentTerm' ↔
          (st.s (uint.nat y)).currentTerm = (st.s (uint.nat y2)).currentTerm := by
        rw [int_eq_iff, Hfi.1, Hfj.1]
      have hLi : gi.State' = go!"StateLeader" ↔ (st.s (uint.nat y)).state = leader :=
        strRel_eq_iff Hfi.2.1 strRel_leader
      have hLj : gj.State' = go!"StateLeader" ↔ (st.s (uint.nat y2)).state = leader :=
        strRel_eq_iff Hfj.2.1 strRel_leader
      have hstep := all_take_step (fun j =>
            Bool.or (!((st.s (uint.nat y)).currentTerm == (st.s j).currentTerm &&
              (st.s (uint.nat y)).state == leader && (st.s j).state == leader)) (uint.nat y == j))
          st.server (sint.nat m) (uint.nat y2) Hsy2 hmt
      by_cases hc : (st.s (uint.nat y)).currentTerm = (st.s (uint.nat y2)).currentTerm ∧
          (st.s (uint.nat y)).state = leader ∧ (st.s (uint.nat y2)).state = leader ∧ uint.nat y ≠ uint.nat y2
      · -- two leaders of one term: false
        obtain ⟨h1, h2, h3, h4⟩ := hc
        rw [decide_eq_true (hT.2 h1)]
        try wp_auto
        rw [decide_eq_true (hLi.2 h2)]
        try wp_auto
        rw [decide_eq_true (hLj.2 h3)]
        try wp_auto
        rw [decide_eq_false (fun h => h4 ((id_eq_iff y y2).1 h))]
        try wp_auto
        wp_for_post
        try wp_auto
        wp_for_post
        try wp_auto
        have hG : st.moreThanOneLeaderInv = false := by
          have hF : F (uint.nat y) = false := by
            apply (all_take_step _ st.server (sint.nat m) (uint.nat y2) Hsy2 hmt).1
            simp [h1, h2, h3, h4]
          unfold State.moreThanOneLeaderInv
          exact (all_take_step F st.server (sint.nat n) (uint.nat y) Hsy hnt).1 hF
        rw [hG]
        iapply HΦ; ipureintro; trivial
      · have hG : Bool.or (!((st.s (uint.nat y)).currentTerm == (st.s (uint.nat y2)).currentTerm &&
              (st.s (uint.nat y)).state == leader && (st.s (uint.nat y2)).state == leader))
            (uint.nat y == uint.nat y2) = true := by
          by_cases h1 : (st.s (uint.nat y)).currentTerm = (st.s (uint.nat y2)).currentTerm <;>
          by_cases h2 : (st.s (uint.nat y)).state = leader <;>
          by_cases h3 : (st.s (uint.nat y2)).state = leader <;>
          by_cases h4 : uint.nat y = uint.nat y2 <;> simp_all
        -- the Go's condition fails at its first false conjunct
        have hm1 : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hmt hnt hstep hG; word
        by_cases h1 : (st.s (uint.nat y)).currentTerm = (st.s (uint.nat y2)).currentTerm
        · rw [decide_eq_true (hT.2 h1)]
          try wp_auto
          by_cases h2 : (st.s (uint.nat y)).state = leader
          · rw [decide_eq_true (hLi.2 h2)]
            try wp_auto
            by_cases h3 : (st.s (uint.nat y2)).state = leader
            · rw [decide_eq_true (hLj.2 h3)]
              try wp_auto
              have h4 : uint.nat y = uint.nat y2 := Classical.byContradiction fun h4 => hc ⟨h1, h2, h3, h4⟩
              rw [decide_eq_true ((id_eq_iff y y2).2 h4)]
              mtol_cont
            · rw [decide_eq_false (fun h => h3 (hLj.1 h))]
              mtol_cont
          · rw [decide_eq_false (fun h => h2 (hLi.1 h))]
            mtol_cont
        · rw [decide_eq_false (fun h => h1 (hT.1 h))]
          mtol_cont
    · -- server `y` passed: the outer loop's next round
      have hme : st.server.length ≤ sint.nat m := by
        rw [← Hmap, List.length_map, Hlen.1]; clear hmt hnt; word
      have hF : F (uint.nat y) = true := all_take_end _ st.server (sint.nat m) hme hmt
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by clear hmt hnt; word, by clear hmt hnt; word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by clear hmt hnt; word]
      exact (all_take_step F st.server (sint.nat n) (uint.nat y) Hsy hnt).2 hF
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; clear hnt; word
    have hG : st.moreThanOneLeaderInv = true := all_take_end F st.server (sint.nat n) hne hnt
    rw [hG]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
