/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__QuorumLogInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__QuorumLogInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Committed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsQuorum
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

-- Server `y2` does not extend `Committed(i)` (`hP`): `without = append(without, j)`, then the
-- next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "q_append" : tactic => `(tactic| (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, -⟩
    wp_apply wp_slice_append $$ [Hw Hcap Hsl0] as %s1 ⟨Hs, Hcap, -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [hm1', hfil, hP, ← hmW]; simp))

theorem State.QuorumLogInv.wp_proof (wp_Committed : State.Committed.spec (GF := GF) (hG := hG))
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG))
    (wp_IsQuorum : IsQuorum.spec (GF := GF) (hG := hG)) :
    State.QuorumLogInv.spec (GF := GF) (hG := hG) := by
  intro p st b
  wp_start as ⟨#Hst, %Hcfgs, %Hb⟩
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
  let P : List Entry → ID → Bool := fun c j => Bool.or (!st.server.contains j) (!isPrefix c (st.s j).log)
  let Fm : ID → EvalM Bool := fun i => do
    let cfg := st.getConfig i
    let c ← st.committed i
    let without := cfg.filter (P c)
    return !isQuorum without cfg
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
    obtain ⟨cy, hcy, hce⟩ : ∃ cy, st.committed (uint.nat y) = .ok cy ∧
        c = !isQuorum ((st.getConfig (uint.nat y)).filter (P cy)) (st.getConfig (uint.nat y)) := by
      have h := hc
      simp only [Fm] at h
      cases hcy : st.committed (uint.nat y) with
      | error e => rw [hcy] at h; cases h
      | ok cy => rw [hcy] at h; cases h; exact ⟨cy, rfl, rfl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index g.Server' (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    wp_apply wp_GetConfig p st y $$ [Hst] as %csl #Hcsl
    · iframe Hst; ipureintro; exact Hyin
    try wp_auto
    wp_apply wp_Committed p st y cy $$ [Hst] as %u #Hu
    · iframe Hst; ipureintro; exact ⟨Hyin, hcy⟩
    try wp_auto
    rename_i oi_ptr
    irename : (oi_ptr ↦ n : IProp GF) => Hoi
    ihave #Hcsl0 := Hcsl
    iunfold setRO at Hcsl0
    icases Hcsl0 with ⟨%cs, #Hcs, %Hcmap⟩
    ihave %Hclen := ownSlice_len $$ Hcs
    ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
    ihave Hcap0 := ownSliceCap_nil (V := w64) (GF := GF)
    ihave IJ : iprop(∃ (m z : w64) (wsl : GoSlice) (W : List w64),
        "i" ∷ i_ptr ↦ m ∗ "j" ∷ j_ptr ↦ z ∗ "without" ∷ without_ptr ↦ wsl ∗ "Hw" ∷ wsl ↦* W ∗
        "Hcap" ∷ ownSliceCap w64 wsl (DFrac.own 1) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z csl.len ∧
          W.map (fun x => uint.nat x) = ((st.getConfig (uint.nat y)).take (sint.nat m)).filter (P cy)⌝)
        $$ [i j without Hcap0]
    · iexists _, _, slice.nil, []
      iframe
      isplitr
      · iexact Hnil
      isplitr
      · iexact Hcap0
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IJ
    obtain ⟨hm0, hm1, hmW⟩ := Hm
    wp_if_destruct
    · have Hlt2 : sint.nat m < cs.length := by rw [Hclen.1]; word
      obtain ⟨y2, Hy2⟩ : ∃ y, cs[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      have Hsy2 := set_getElem Hcmap Hy2
      have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by word
      have hfil : ((st.getConfig (uint.nat y)).take (sint.nat m + 1)).filter (P cy) =
          ((st.getConfig (uint.nat y)).take (sint.nat m)).filter (P cy) ++
            (if P cy (uint.nat y2) then [uint.nat y2] else []) := by
        rw [List.take_add_one, Hsy2, Option.toList_some, List.filter_append]
        by_cases hP : P cy (uint.nat y2) = true <;> simp [hP]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z csl.len from ⟨hm0, Hif⟩))]
      wp_apply wp_load_slice_index csl (sint.Z m) cs DFrac.discard y2 hm0 $$ [Hcs] as -
      · isplitr
        · iexact Hcs
        ipureintro; exact Hy2
      try wp_auto
      wp_apply wp_map_lookup2 $$ [HS] as -
      · iexact HS
      by_cases hin : uint.nat y2 ∈ st.server
      · icases servers_at st sm y2 hin $$ Hsrvs with ⟨%qv, %Hqv, #Hv⟩
        iunfold serverRO at Hv
        icases Hv with ⟨%gv, %mv, #Hqv', %Hfv, #Hlogv, -, -, -, -, -, -⟩
        icases typedPointsto_split _ _ _ $$ Hqv' with Hqvf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hqvf
        rw [Hqv]
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        try wp_auto
        wp_apply wp_IsPrefix u cy gv.Log' (st.s (uint.nat y2)).log $$ [Hu Hlogv]
        · iframe Hu Hlogv
        by_cases hp : isPrefix cy (st.s (uint.nat y2)).log = true
        · rw [hp]
          try wp_auto
          have hP : P cy (uint.nat y2) = false := by simp [P, hin, hp]
          wp_for_post
          iframe
          iexists _, _, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hm1', hfil, hP, hmW]; simp
        · rw [Bool.not_eq_true] at hp
          rw [hp]
          try wp_auto
          have hP : P cy (uint.nat y2) = true := by simp [P, hp]
          q_append
      · have hnone : sm !! y2 = none := by
          cases h : sm !! y2 with
          | none => rfl
          | some _ => exact absurd ((Hkeys _).1 (by rw [h]; rfl)) hin
        rw [hnone]
        simp only [Option.getD_none, Option.isSome_none]
        try wp_auto
        have hP : P cy (uint.nat y2) = true := by simp [P, hin]
        q_append
    · -- the servers not extending `Committed(i)`, against the configuration
      have hme : sint.nat m = (st.getConfig (uint.nat y)).length := by
        rw [← Hcmap, List.length_map, Hclen.1]; word
      rw [hme, List.take_length] at hmW
      imod ownSlice_persist $$ Hw with #Hw
      wp_apply wp_IsQuorum wsl _ csl _ $$ [Hw Hcsl] as -
      · iframe Hcsl
        isplitr
        · iunfold setRO; iexists W; iframe Hw; ipureintro; exact hmW
        ipureintro
        have h1 : W.length = ((st.getConfig (uint.nat y)).filter (P cy)).length := by
          rw [← hmW, List.length_map]
        have h2 := List.length_filter_le (P cy) (st.getConfig (uint.nat y))
        have h3 := Hcfgs _ Hyin
        omega
      by_cases hq : isQuorum ((st.getConfig (uint.nat y)).filter (P cy)) (st.getConfig (uint.nat y)) = true
      · rw [hq]
        try wp_auto
        wp_for_post
        try wp_auto
        have hb : b = false := hcf (by rw [hce, hq]; rfl)
        rw [hb]
        iapply HΦ; ipureintro; trivial
      · rw [Bool.not_eq_true] at hq
        rw [hq]
        try wp_auto
        have hG : c = true := by rw [hce, hq]; rfl
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hn1']
        exact hct hG
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; word
    have hb : b = true := allM_take_end Fm st.server (sint.nat n) b hne hnt Hb
    rw [hb]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
