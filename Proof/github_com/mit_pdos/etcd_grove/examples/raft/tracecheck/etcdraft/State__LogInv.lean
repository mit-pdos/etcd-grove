/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__LogInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LogInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Committed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsPrefix
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

theorem State.LogInv.wp_proof (wp_Committed : State.Committed.spec (GF := GF) (hG := hG))
    (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG)) :
    State.LogInv.spec (GF := GF) (hG := hG) := by
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
    let ci ← st.committed i
    let cj ← st.committed j
    return isPrefix ci cj || isPrefix cj ci
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
      obtain ⟨ci, cj, hci, hcj, hc2e⟩ :=
        bind2_ok (st.committed (uint.nat y)) (st.committed (uint.nat y2))
          (fun ci cj => isPrefix ci cj || isPrefix cj ci) c2 hc2
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z g.Server'.len from ⟨hm0, Hif⟩))]
      wp_apply wp_load_slice_index g.Server' (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hy2
      try wp_auto
      wp_apply wp_Committed p st y ci $$ [Hst] as %u1 #Hu1
      · iframe Hst; ipureintro; exact ⟨Hyin, hci⟩
      try wp_auto
      wp_apply wp_Committed p st y2 cj $$ [Hst] as %u2 #Hu2
      · iframe Hst; ipureintro; exact ⟨Hyin2, hcj⟩
      try wp_auto
      wp_apply wp_IsPrefix u1 ci u2 cj $$ [Hu1 Hu2]
      · iframe Hu1 Hu2
      by_cases h1 : isPrefix ci cj = true
      · rw [h1]
        try wp_auto
        have hG : c2 = true := by rw [hc2e, h1]
        li_cont hm1' hc2t hG
      · rw [Bool.not_eq_true] at h1
        rw [h1]
        try wp_auto
        wp_apply wp_IsPrefix u2 cj u1 ci $$ [Hu1 Hu2]
        · iframe Hu1 Hu2
        by_cases h2 : isPrefix cj ci = true
        · rw [h2]
          try wp_auto
          have hG : c2 = true := by rw [hc2e, h1, h2]
          li_cont hm1' hc2t hG
        · rw [Bool.not_eq_true] at h2
          rw [h2]
          try wp_auto
          wp_for_post
          try wp_auto
          wp_for_post
          try wp_auto
          have hb : b = false := hcf (hc2f (by rw [hc2e, h1, h2]))
          rw [hb]
          iapply HΦ; ipureintro; trivial
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
