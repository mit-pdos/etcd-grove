/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__ElectionSafetyInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ElectionSafetyInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.maxIndexOfTerm
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

-- A loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "es_cont" hs:ident hm:ident hstep:ident hG:ident : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by clear $hs $hstep $hG; word, by clear $hs $hstep $hG; word, ?_⟩
    rw [$hm:ident]
    exact $hstep.2 $hG))

theorem State.ElectionSafetyInv.wp_proof (wp_maxIndexOfTerm : maxIndexOfTerm.spec (GF := GF) (hG := hG)) :
    State.ElectionSafetyInv.spec (GF := GF) (hG := hG) := by
  intro p st
  wp_start as ⟨#Hst, %Hlogs⟩
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
  let G : ID → ID → Bool := fun i j =>
    decide (maxIndexOfTerm (st.s i).log (st.s i).currentTerm ≥ maxIndexOfTerm (st.s j).log (st.s i).currentTerm)
  let F : ID → Bool := fun i => Bool.or ((st.s i).state != leader) (st.server.all (G i))
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
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hnt; word
    have hstep := all_take_step F st.server (sint.nat n) (uint.nat y) Hsy hnt
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index g.Server' (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
    iunfold serverRO at Hvi
    icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, #Hlogi, -, -, -, -, -, -⟩
    icases typedPointsto_split _ _ _ $$ Hqi' with Hqif
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqif
    wp_apply wp_map_lookup1 $$ [HS] as -
    · iexact HS
    rw [Hqi]
    simp only [Option.getD_some]
    try wp_auto
    try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
    have hL : gi.State' = go!"StateLeader" ↔ (st.s (uint.nat y)).state = leader :=
      strRel_eq_iff Hfi.2.1 strRel_leader
    by_cases h1 : (st.s (uint.nat y)).state = leader
    · rw [decide_eq_true (hL.2 h1)]
      try wp_auto
      rename_i oi_ptr
      irename : (oi_ptr ↦ n : IProp GF) => Hoi
      ihave IJ : iprop(∃ (m z : w64),
          "i" ∷ i_ptr ↦ m ∗ "j" ∷ j_ptr ↦ z ∗
          "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z g.Server'.len ∧
            (st.server.take (sint.nat m)).all (G (uint.nat y)) = true⌝)
          $$ [i j]
      · iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for IJ
      obtain ⟨hm0, hm1, hmt⟩ := Hm
      wp_if_destruct
      · have Hlt2 : sint.nat m < xs.length := by clear hmt hnt hstep; rw [Hlen.1]; word
        obtain ⟨y2, Hy2⟩ : ∃ y, xs[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem Hlt2⟩
        have Hsy2 := set_getElem Hmap Hy2
        have Hyin2 : uint.nat y2 ∈ st.server := List.mem_of_getElem? Hsy2
        have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hmt hnt hstep; word
        have hstep2 := all_take_step (G (uint.nat y)) st.server (sint.nat m) (uint.nat y2) Hsy2 hmt
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z g.Server'.len from ⟨hm0, Hif⟩))]
        wp_apply wp_load_slice_index g.Server' (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
        · isplitr
          · iexact Hxs
          ipureintro; exact Hy2
        try wp_auto
        icases servers_at st sm y2 Hyin2 $$ Hsrvs with ⟨%qj, %Hqj, #Hvj⟩
        iunfold serverRO at Hvj
        icases Hvj with ⟨%gj, %mj, #Hqj', %Hfj, #Hlogj, -, -, -, -, -, -⟩
        icases typedPointsto_split _ _ _ $$ Hqj' with Hqjf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hqjf
        wp_apply wp_maxIndexOfTerm gi.Log' (st.s (uint.nat y)).log gi.CurrentTerm' $$ [Hlogi] as %r1 %Hr1
        · iframe Hlogi; ipureintro; exact Hlogs _ Hyin
        try wp_auto
        wp_apply wp_map_lookup1 $$ [HS] as -
        · iexact HS
        rw [Hqj]
        simp only [Option.getD_some]
        try wp_auto
        wp_apply wp_maxIndexOfTerm gj.Log' (st.s (uint.nat y2)).log gi.CurrentTerm' $$ [Hlogj] as %r2 %Hr2
        · iframe Hlogj; ipureintro; exact Hlogs _ Hyin2
        try wp_auto
        rw [Hfi.1] at Hr1 Hr2
        by_cases h2 : sint.Z r1 < sint.Z r2
        · rw [decide_eq_true h2]
          try wp_auto
          wp_for_post
          try wp_auto
          wp_for_post
          try wp_auto
          have hG : st.electionSafetyInv = false := by
            have hgf : G (uint.nat y) (uint.nat y2) = false := by
              simp only [G, decide_eq_false_iff_not, ge_iff_le, Nat.not_le]; omega
            have hF : F (uint.nat y) = false := by simp [F, h1, hstep2.1 hgf]
            unfold State.electionSafetyInv
            exact hstep.1 hF
          rw [hG]
          iapply HΦ; ipureintro; trivial
        · rw [decide_eq_false h2]
          have hG : G (uint.nat y) (uint.nat y2) = true := by
            simp only [G, decide_eq_true_eq, ge_iff_le]; omega
          es_cont hmt hm1' hstep2 hG
      · -- every server checked: the outer loop's next round
        have hme : st.server.length ≤ sint.nat m := by
          rw [← Hmap, List.length_map, Hlen.1]; clear hmt hnt hstep; word
        have hG : F (uint.nat y) = true := by
          simp [F, all_take_end _ st.server (sint.nat m) hme hmt]
        es_cont hnt hn1' hstep hG
    · rw [decide_eq_false (fun h => h1 (hL.1 h))]
      have hG : F (uint.nat y) = true := by simp [F, h1]
      es_cont hnt hn1' hstep hG
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; clear hnt; word
    have hG : st.electionSafetyInv = true := all_take_end F st.server (sint.nat n) hne hnt
    rw [hG]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
