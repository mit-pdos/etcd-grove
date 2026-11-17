/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__MoreUpToDateCorrectInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__MoreUpToDateCorrectInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Committed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.LastTerm
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

-- A server loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "li_cont" hm:ident hstep:ident hG:ident : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [$hm:ident]
    exact $hstep $hG))

-- The committed-entries check, once the up-to-date condition holds (`hcd`; hygiene off: it names the
-- proof's hypotheses).
set_option hygiene false in
local macro "mu_commit" : tactic => `(tactic| (
    try wp_auto
    obtain ⟨cj, hcj, hc2e⟩ := hcd
    wp_apply wp_Committed p st y2 cj $$ [Hst] as %u2 #Hu2
    · iframe Hst; ipureintro; exact ⟨Hyin2, hcj⟩
    try wp_auto
    wp_apply wp_IsPrefix u2 cj gi.Log' (st.s (uint.nat y)).log $$ [Hu2 Hlogi]
    · iframe Hu2 Hlogi
    by_cases hp : isPrefix cj (st.s (uint.nat y)).log = true
    · rw [hp]
      try wp_auto
      have hG : c2 = true := by rw [hc2e, hp]
      li_cont hm1' hc2t hG
    · rw [Bool.not_eq_true] at hp
      rw [hp]
      try wp_auto
      wp_for_post
      try wp_auto
      wp_for_post
      try wp_auto
      have hb : b = false := hcf (hc2f (by rw [hc2e, hp]))
      rw [hb]
      iapply HΦ; ipureintro; trivial))

theorem State.MoreUpToDateCorrectInv.wp_proof (wp_Committed : State.Committed.spec (GF := GF) (hG := hG))
    (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG))
    (wp_LastTerm : LastTerm.spec (GF := GF) (hG := hG)) :
    State.MoreUpToDateCorrectInv.spec (GF := GF) (hG := hG) := by
  intro p st b
  wp_start as ⟨#Hst, %Hb⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hm, #Hpm, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  iunfold setRO at Hsrv
  icases Hsrv with ⟨%xs, #Hxs, %Hmap⟩
  ihave %Hlen := ownSlice_len $$ Hxs
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  let Gm : ID → ID → EvalM Bool := fun i j => do
    let li := (st.s i).log
    let lj := (st.s j).log
    if Bool.or (decide (lastTerm li > lastTerm lj))
        (lastTerm li == lastTerm lj && decide (li.length ≥ lj.length)) then
      return isPrefix (← st.committed j) li
    return true
  let Fm : ID → EvalM Bool := fun i => st.server.allM (Gm i)
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Server'.len ∧
        (st.server.take (sint.nat n)).allM Fm = .ok true⌝)
      $$ [i Hgi]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.allM_nil]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsy := set_getElem Hmap Hy
    have Hyin : uint.nat y ∈ st.server := List.mem_of_getElem? Hsy
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    obtain ⟨c, hc, hcf, hct⟩ := allM_take_step Fm st.server (sint.nat n) (uint.nat y) b Hsy hnt Hb
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
          (st.server.take (sint.nat m)).allM (Gm (uint.nat y)) = .ok true⌝)
        $$ [i j]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.allM_nil]; rfl⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmt⟩ := Hm
    wp_if_destruct
    · have Hlt2 : sint.nat m < xs.length := by rw [Hlen.1]; word
      obtain ⟨y2, Hy2⟩ : ∃ y, xs[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      have Hsy2 := set_getElem Hmap Hy2
      have Hyin2 : uint.nat y2 ∈ st.server := List.mem_of_getElem? Hsy2
      have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by word
      obtain ⟨c2, hc2, hc2f, hc2t⟩ := allM_take_step (Gm (uint.nat y)) st.server (sint.nat m) (uint.nat y2) c Hsy2 hmt hc
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z g.Server'.len from ⟨hm0, Hif⟩))]
      wp_apply wp_load_slice_index g.Server' (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hy2
      try wp_auto
      icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
      icases servers_at st sm y2 Hyin2 $$ Hsrvs with ⟨%qj, %Hqj, #Hvj⟩
      iunfold serverRO at Hvi Hvj
      icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, #Hlogi, -, -, -, -, -, -⟩
      icases Hvj with ⟨%gj, %mj, #Hqj', %Hfj, #Hlogj, -, -, -, -, -, -⟩
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
      wp_apply wp_LastTerm gi.Log' (st.s (uint.nat y)).log $$ [Hlogi] as %r1 %Hr1
      · iexact Hlogi
      try wp_auto
      wp_apply wp_LastTerm gj.Log' (st.s (uint.nat y2)).log $$ [Hlogj] as %r2 %Hr2
      · iexact Hlogj
      try wp_auto
      ihave #Hlogi0 := Hlogi
      ihave #Hlogj0 := Hlogj
      iunfold logRO at Hlogi0 Hlogj0
      icases Hlogi0 with ⟨%esi, #Hesi, #Hbi⟩
      icases Hlogj0 with ⟨%esj, #Hesj, #Hbj⟩
      ihave %Hli := ownSlice_len $$ Hesi
      ihave %Hlj := ownSlice_len $$ Hesj
      ihave %Hbli := BigSepL2.bigSepL2_length $$ Hbi
      ihave %Hblj := BigSepL2.bigSepL2_length $$ Hbj
      have hzi : sint.Z gi.Log'.len = ((st.s (uint.nat y)).log.length : Int) := by rw [← Hbli, Hli.1]; word
      have hzj : sint.Z gj.Log'.len = ((st.s (uint.nat y2)).log.length : Int) := by rw [← Hblj, Hlj.1]; word
      have hA : Bool.or (decide (lastTerm (st.s (uint.nat y)).log > lastTerm (st.s (uint.nat y2)).log))
            (lastTerm (st.s (uint.nat y)).log == lastTerm (st.s (uint.nat y2)).log &&
              decide ((st.s (uint.nat y)).log.length ≥ (st.s (uint.nat y2)).log.length)) = true →
          ∃ cj, st.committed (uint.nat y2) = .ok cj ∧ c2 = isPrefix cj (st.s (uint.nat y)).log := by
        intro hcd
        have h := hc2
        simp only [Gm] at h
        split at h
        · cases hcj : st.committed (uint.nat y2) with
          | error e => rw [hcj] at h; cases h
          | ok cj => rw [hcj] at h; cases h; exact ⟨cj, rfl, rfl⟩
        · contradiction
      have hB : Bool.or (decide (lastTerm (st.s (uint.nat y)).log > lastTerm (st.s (uint.nat y2)).log))
            (lastTerm (st.s (uint.nat y)).log == lastTerm (st.s (uint.nat y2)).log &&
              decide ((st.s (uint.nat y)).log.length ≥ (st.s (uint.nat y2)).log.length)) = false →
          c2 = true := by
        intro hcd
        have h := hc2
        simp only [Gm] at h
        split at h
        · rename_i hc; rw [hc] at hcd; cases hcd
        · cases h; rfl
      by_cases hgt : lastTerm (st.s (uint.nat y)).log > lastTerm (st.s (uint.nat y2)).log
      · rw [decide_eq_true (show sint.Z r2 < sint.Z r1 by rw [Hr1, Hr2]; exact hgt)]
        have hcd := hA (by simp [hgt])
        mu_commit
      · rw [decide_eq_false (show ¬ sint.Z r2 < sint.Z r1 by rw [Hr1, Hr2]; exact hgt)]
        try wp_auto
        wp_apply wp_LastTerm gi.Log' (st.s (uint.nat y)).log $$ [Hlogi] as %r3 %Hr3
        · iexact Hlogi
        try wp_auto
        wp_apply wp_LastTerm gj.Log' (st.s (uint.nat y2)).log $$ [Hlogj] as %r4 %Hr4
        · iexact Hlogj
        try wp_auto
        by_cases heq : lastTerm (st.s (uint.nat y)).log = lastTerm (st.s (uint.nat y2)).log
        · rw [decide_eq_true ((int_eq_iff r3 r4).2 (by rw [Hr3, Hr4]; exact heq))]
          try wp_auto
          by_cases hge : (st.s (uint.nat y)).log.length ≥ (st.s (uint.nat y2)).log.length
          · rw [decide_eq_true (show sint.Z gj.Log'.len ≤ sint.Z gi.Log'.len by rw [hzi, hzj]; exact_mod_cast hge)]
            have hcd := hA (by simp [heq, hge])
            mu_commit
          · rw [decide_eq_false (show ¬ sint.Z gj.Log'.len ≤ sint.Z gi.Log'.len by
              rw [hzi, hzj]; exact_mod_cast hge)]
            have hG := hB (by simp [heq, hge])
            try wp_auto
            li_cont hm1' hc2t hG
        · rw [decide_eq_false (fun h => heq (by rw [← Hr3, ← Hr4, (int_eq_iff r3 r4).1 h]))]
          have hG := hB (by simp [hgt, heq])
          try wp_auto
          li_cont hm1' hc2t hG
    · -- server `y` passed: the outer loop's next round
      have hme : st.server.length ≤ sint.nat m := by
        rw [← Hmap, List.length_map, Hlen.1]; word
      have hG : c = true := allM_take_end _ st.server (sint.nat m) c hme hmt hc
      li_cont hn1' hct hG
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; word
    have hb : b = true := allM_take_end Fm st.server (sint.nat n) b hne hnt Hb
    rw [hb]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
