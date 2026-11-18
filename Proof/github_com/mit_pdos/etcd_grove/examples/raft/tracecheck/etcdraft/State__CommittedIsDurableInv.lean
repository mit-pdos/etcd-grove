/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__CommittedIsDurableInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__CommittedIsDurableInv
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

-- The loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "cid_cont" : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by clear hnt hstep hG; word, by clear hnt hstep hG; word, ?_⟩
    rw [hn1']
    exact hstep.2 hG))

theorem State.CommittedIsDurableInv.wp_proof : State.CommittedIsDurableInv.spec (GF := GF) (hG := hG) := by
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
  let F : ID → Bool := fun i =>
    Bool.or ((st.s i).state != leader) (decide ((st.s i).commitIndex ≤ (st.s i).durable.log.length))
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
    icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
    iunfold serverRO at Hvi
    icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, -, -, -, -, -, -, #Hdur⟩
    iunfold durableRO at Hdur
    icases Hdur with ⟨-, #Hdlog, -⟩
    iunfold logRO at Hdlog
    icases Hdlog with ⟨%des, #Hdes, #Hdb⟩
    ihave %Hdl := ownSlice_len $$ Hdes
    ihave %Hdbl := BigSepL2.bigSepL2_length $$ Hdb
    icases typedPointsto_split _ _ _ $$ Hqi' with Hqif
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqif
    icases typedPointsto_split _ _ _ $$ Durable with Hdf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hdf
    wp_apply wp_map_lookup1 $$ [HS] as -
    · iexact HS
    rw [Hqi]
    simp only [Option.getD_some]
    try wp_auto
    try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hnt; word
    have hL : gi.State' = go!"StateLeader" ↔ (st.s (uint.nat y)).state = leader :=
      strRel_eq_iff Hfi.2.1 strRel_leader
    have hdlen : sint.Z gi.Durable'.Log'.len = ((st.s (uint.nat y)).durable.log.length : Int) := by
      rw [← Hdbl, Hdl.1]; word
    have hstep := all_take_step F st.server (sint.nat n) (uint.nat y) Hsy hnt
    by_cases h1 : (st.s (uint.nat y)).state = leader
    · rw [decide_eq_true (hL.2 h1)]
      try wp_auto
      by_cases h2 : (st.s (uint.nat y)).commitIndex ≤ (st.s (uint.nat y)).durable.log.length
      · have h2' : ¬ sint.Z gi.Durable'.Log'.len < sint.Z gi.CommitIndex' := by
          rw [hdlen, Hfi.2.2.2.2.1]; omega
        rw [decide_eq_false h2']
        have hG : F (uint.nat y) = true := by simp [F, h2]
        cid_cont
      · have h2' : sint.Z gi.Durable'.Log'.len < sint.Z gi.CommitIndex' := by
          rw [hdlen, Hfi.2.2.2.2.1]; omega
        rw [decide_eq_true h2']
        try wp_auto
        wp_for_post
        try wp_auto
        have hG : st.committedIsDurableInv = false := by
          unfold State.committedIsDurableInv
          exact hstep.1 (by simp [F, h1, h2])
        rw [hG]
        iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false (fun h => h1 (hL.1 h))]
      have hG : F (uint.nat y) = true := by simp [F, h1]
      cid_cont
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; clear hnt; word
    have hG : st.committedIsDurableInv = true := all_take_end F st.server (sint.nat n) hne hnt
    rw [hG]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
