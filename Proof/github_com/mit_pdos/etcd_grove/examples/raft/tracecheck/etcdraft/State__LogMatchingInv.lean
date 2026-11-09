/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__LogMatchingInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LogMatchingInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual
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

theorem toNat_sub_one_add_one (z : Int) (h : 1 ≤ z) : z.toNat - 1 + 1 = z.toNat := by omega

-- A server loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "lm_cont" hs:ident hm:ident hstep:ident hG:ident : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by clear $hs $hstep $hG; word, by clear $hs $hstep $hG; word, ?_⟩
    rw [$hm:ident]
    exact $hstep.2 $hG))

theorem State.LogMatchingInv.wp_proof (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    State.LogMatchingInv.spec (GF := GF) (hG := hG) := by
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
  let H : ID → ID → Nat → Bool := fun i j n =>
    Bool.or (((st.s i).log[n]?).map Entry.term != ((st.s j).log[n]?).map Entry.term)
      ((st.s i).log.take (n + 1) == (st.s j).log.take (n + 1))
  let G : ID → ID → Bool := fun i j =>
    (List.range (min (st.s i).log.length (st.s j).log.length)).all (H i j)
  let F : ID → Bool := fun i => st.server.all (G i)
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
    rename_i oi_ptr
    irename : (oi_ptr ↦ n : IProp GF) => Hoi
    icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
    iunfold serverRO at Hvi
    icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, #Hlogi, -, -, -, -, -, -⟩
    icases typedPointsto_split _ _ _ $$ Hqi' with Hqif
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqif
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
      ihave #Hlogi0 := Hlogi
      ihave #Hlogj0 := Hlogj
      iunfold logRO at Hlogi0 Hlogj0
      icases Hlogi0 with ⟨%esi, #Hesi, #Hbi⟩
      icases Hlogj0 with ⟨%esj, #Hesj, #Hbj⟩
      ihave %Hli := ownSlice_len $$ Hesi
      ihave %Hlj := ownSlice_len $$ Hesj
      ihave %Hci := ownSlice_wf $$ Hesi
      ihave %Hcj := ownSlice_wf $$ Hesj
      ihave %Hbli := BigSepL2.bigSepL2_length $$ Hbi
      ihave %Hblj := BigSepL2.bigSepL2_length $$ Hbj
      have hzi : sint.Z gi.Log'.len = ((st.s (uint.nat y)).log.length : Int) := by rw [← Hbli, Hli.1]; word
      have hzj : sint.Z gj.Log'.len = ((st.s (uint.nat y2)).log.length : Int) := by rw [← Hblj, Hlj.1]; word
      have hbi := Hlogs _ Hyin
      have hbj := Hlogs _ Hyin2
      ihave IK : iprop(∃ (k : w64),
          "n" ∷ n_ptr ↦ k ∗
          "%Hk" ∷ ⌜1 ≤ sint.Z k ∧
            sint.Z k - 1 ≤ min ((st.s (uint.nat y)).log.length : Int) ((st.s (uint.nat y2)).log.length : Int) ∧
            (List.range (sint.nat k - 1)).all (H (uint.nat y) (uint.nat y2)) = true⌝)
          $$ [n]
      · iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 1) - 1 = 0 from rfl]; simp⟩
      wp_for IK
      obtain ⟨hk1, hk2, hkt⟩ := Hk
      have hkend : ¬ (sint.Z k ≤ sint.Z gi.Log'.len ∧ sint.Z k ≤ sint.Z gj.Log'.len) →
          G (uint.nat y) (uint.nat y2) = true := by
        intro hc
        have : sint.nat k - 1 = min (st.s (uint.nat y)).log.length (st.s (uint.nat y2)).log.length := by
          rw [hzi, hzj] at hc
          rw [show sint.nat k = (sint.Z k).toNat from rfl]; omega
        simp only [G]; rw [← this]; exact hkt
      by_cases hci : sint.Z k ≤ sint.Z gi.Log'.len
      · rw [decide_eq_true hci]
        try wp_auto
        by_cases hcj : sint.Z k ≤ sint.Z gj.Log'.len
        · rw [decide_eq_true hcj]
          try wp_auto
          have hk0 : 0 ≤ sint.Z (k - W64 1) := by word
          have hkk : sint.nat (k - W64 1) = sint.nat k - 1 := by word
          have Hlti : sint.nat (k - W64 1) < esi.length := by rw [Hli.1]; word
          have Hltj : sint.nat (k - W64 1) < esj.length := by rw [Hlj.1]; word
          obtain ⟨ei, Hei⟩ : ∃ e, esi[sint.nat (k - W64 1)]? = some e := ⟨_, List.getElem?_eq_getElem Hlti⟩
          obtain ⟨ej, Hej⟩ : ∃ e, esj[sint.nat (k - W64 1)]? = some e := ⟨_, List.getElem?_eq_getElem Hltj⟩
          obtain ⟨xi, Hxi⟩ : ∃ x, (st.s (uint.nat y)).log[sint.nat (k - W64 1)]? = some x :=
            ⟨_, List.getElem?_eq_getElem (Hbli ▸ Hlti)⟩
          obtain ⟨xj, Hxj⟩ : ∃ x, (st.s (uint.nat y2)).log[sint.nat (k - W64 1)]? = some x :=
            ⟨_, List.getElem?_eq_getElem (Hblj ▸ Hltj)⟩
          ihave #Hexi := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hei Hxi $$ Hbi
          ihave #Hexj := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hej Hxj $$ Hbj
          iunfold entryRO at Hexi Hexj
          icases Hexi with ⟨%Hexi, -⟩
          icases Hexj with ⟨%Hexj, -⟩
          icases ownSlice_elem_acc _ ei gi.Log' _ esi hk0 Hei $$ Hesi with ⟨Hei', -⟩
          icases ownSlice_elem_acc _ ej gj.Log' _ esj hk0 Hej $$ Hesj with ⟨Hej', -⟩
          icases typedPointsto_split _ _ _ $$ Hei' with Heif
          icases typedPointsto_split _ _ _ $$ Hej' with Hejf
          simp only [TypedPointsto.typedPointstoDef]
          iNamed Heif
          iNamed Hejf
          simp only [_root_.decide_true, ite_true]
          try wp_auto
          have hki : sint.Z (k - W64 1) < sint.Z gi.Log'.len := by word
          have hkj : sint.Z (k - W64 1) < sint.Z gj.Log'.len := by word
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gi.Log'.len
            from ⟨hk0, hki⟩))]
          try wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gj.Log'.len
            from ⟨hk0, hkj⟩))]
          try wp_auto
          have hk' : sint.nat (k + W64 1) - 1 = (sint.nat k - 1) + 1 := by word
          have hrange : (List.range (sint.nat (k + W64 1) - 1)).all (H (uint.nat y) (uint.nat y2)) =
              ((List.range (sint.nat k - 1)).all (H (uint.nat y) (uint.nat y2)) &&
                H (uint.nat y) (uint.nat y2) (sint.nat k - 1)) := by
            rw [hk', List.range_succ, List.all_append]; simp
          rw [hkk] at Hxi Hxj
          have hkk1 : sint.nat k - 1 + 1 = sint.nat k := toNat_sub_one_add_one _ hk1
          have hHt : (ei.Term' = ej.Term') →
              H (uint.nat y) (uint.nat y2) (sint.nat k - 1) =
                ((st.s (uint.nat y)).log.take (sint.nat k) == (st.s (uint.nat y2)).log.take (sint.nat k)) := by
            intro h
            simp only [H, Hxi, Hxj, Option.map_some, hkk1]
            rw [← Hexi.1, ← Hexj.1, h]; simp
          have hHf : ¬ (ei.Term' = ej.Term') → H (uint.nat y) (uint.nat y2) (sint.nat k - 1) = true := by
            intro h
            have : xi.term ≠ xj.term := by rw [← Hexi.1, ← Hexj.1]; exact fun h' => h ((int_eq_iff _ _).2 h')
            simp [H, Hxi, Hxj, this]
          wp_if_destruct
          · -- the terms agree: the prefixes compared
            have hkc : sint.Z k ≤ sint.Z gi.Log'.cap := by word
            have hkcj : sint.Z k ≤ sint.Z gj.Log'.cap := by word
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧
              sint.Z k ≤ sint.Z gi.Log'.cap from ⟨by decide, by word, hkc⟩))]
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧
              sint.Z k ≤ sint.Z gj.Log'.cap from ⟨by decide, by word, hkcj⟩))]
            try wp_auto
            ihave #Hsubi := logRO_subslice gi.Log' (st.s (uint.nat y)).log (W64 0) k
              ⟨by decide, by word, hci⟩ $$ Hlogi
            ihave #Hsubj := logRO_subslice gj.Log' (st.s (uint.nat y2)).log (W64 0) k
              ⟨by decide, by word, hcj⟩ $$ Hlogj
            wp_apply wp_EntriesEqual $$ [Hsubi Hsubj]
            · iframe Hsubi Hsubj
            iintro -
            try wp_auto
            have hsub : ∀ l : List Entry, subslice 0 (sint.nat k) l = l.take (sint.nat k) := by
              intro l; simp [subslice]
            rw [hsub, hsub]
            have hH := hHt Hif
            by_cases he : (st.s (uint.nat y)).log.take (sint.nat k) = (st.s (uint.nat y2)).log.take (sint.nat k)
            · rw [decide_eq_true he]
              try wp_auto
              wp_for_post
              iframe
              iexists _
              iframe
              ipureintro
              refine ⟨by word, by word, ?_⟩
              rw [hrange, hkt, hH, he]; simp
            · rw [decide_eq_false he]
              try wp_auto
              wp_for_post
              try wp_auto
              wp_for_post
              try wp_auto
              wp_for_post
              try wp_auto
              have hG : st.logMatchingInv = false := by
                have hg : G (uint.nat y) (uint.nat y2) = false := by
                  simp only [G, List.all_eq_false]
                  refine ⟨sint.nat k - 1, List.mem_range.2 ?_, ?_⟩
                  · rw [hzi] at hci; rw [hzj] at hcj
                    rw [show sint.nat k = (sint.Z k).toNat from rfl]
                    omega
                  · rw [hH]; simp [he]
                have hF : F (uint.nat y) = false := hstep2.1 hg
                unfold State.logMatchingInv
                exact hstep.1 hF
              rw [hG]
              iapply HΦ; ipureintro; trivial
          · try wp_auto
            wp_for_post
            iframe
            iexists _
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [hrange, hkt, hHf Hif]
        · rw [decide_eq_false hcj]
          try wp_auto
          rw [show decide ((#false : val) = #true) = false from
            decide_eq_false (fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide))]
          simp only [Bool.false_eq_true, ite_false]
          have hG := hkend (fun h => hcj h.2)
          simp only [_root_.decide_true, ite_true]
          lm_cont hmt hm1' hstep2 hG
      · rw [decide_eq_false hci]
        try wp_auto
        rw [show decide ((#false : val) = #true) = false from
          decide_eq_false (fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide))]
        simp only [Bool.false_eq_true, ite_false]
        have hG := hkend (fun h => hci h.1)
        simp only [_root_.decide_true, ite_true]
        lm_cont hmt hm1' hstep2 hG
    · -- server `y` passed: the outer loop's next round
      have hme : st.server.length ≤ sint.nat m := by
        rw [← Hmap, List.length_map, Hlen.1]; clear hmt hnt hstep; word
      have hG : F (uint.nat y) = true := all_take_end _ st.server (sint.nat m) hme hmt
      lm_cont hnt hn1' hstep hG
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; clear hnt; word
    have hG : st.logMatchingInv = true := all_take_end F st.server (sint.nat n) hne hnt
    rw [hG]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
