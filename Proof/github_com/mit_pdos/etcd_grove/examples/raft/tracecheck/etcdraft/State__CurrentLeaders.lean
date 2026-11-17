/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__CurrentLeaders`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__CurrentLeaders

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

theorem State.CurrentLeaders.wp_proof : State.CurrentLeaders.spec (GF := GF) (hG := hG) := by
  intro p st
  wp_start as #Hst
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  iunfold setRO at Hsrv
  icases Hsrv with ⟨%xs, #Hxs, %Hxm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  iapply wp_fupd
  wp_auto
  rename_i ip
  irename : (ip ↦ (zero_val w64 : w64) : IProp GF) => Hj
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List w64) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap w64 (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n jv : w64) (sl : GoSlice) (ys : List w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ ip ↦ jv ∗ "ls" ∷ ls_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ys ∗
      "Hcap" ∷ ownSliceCap w64 sl (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Server'.len ∧
        ys.map (fun x => uint.nat x) = (st.server.take (sint.nat n)).filter (fun i => (st.s i).state == leader)⌝)
      $$ [i Hj ls Hnil Hcap0]
  · iexists _, _, _, []
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hif : sint.Z n < sint.Z g.Server'.len := by simpa using Hif
    have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsx : st.server[sint.nat n]? = some (uint.nat x) := by rw [← Hxm, List.getElem?_map, Hx]; rfl
    have Hii : W64 (Int.ofNat (uint.nat x)) = x := by apply BitVec.eq_of_toNat_eq; simp
    icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
        serverRO (GF := GF) q (st.s j))) Hsx) $$ Hsrvs with ⟨%q, %Hq, #Hsv⟩
    rw [Hii] at Hq
    iunfold serverRO at Hsv
    icases Hsv with ⟨%gs, %mm, #Hq', %Hf, -⟩
    icases typedPointsto_split _ _ _ $$ Hq' with Hqf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hqf with ⟨-, #VS, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hx
    try wp_auto
    wp_apply wp_map_lookup1 $$ [HS] as -
    · iexact HS
    rw [Hq]
    simp only [Option.getD_some, github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
    try wp_auto
    have hL := strRel_eq_iff Hf.2.1 (show strRel go!"StateLeader" leader by unfold strRel leader; decide)
    have htake : (st.server.take (sint.nat (n + W64 1))).filter (fun i => (st.s i).state == leader) =
        (st.server.take (sint.nat n)).filter (fun i => (st.s i).state == leader) ++
          (if (st.s (uint.nat x)).state == leader then [uint.nat x] else []) := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hsx]
      simp [List.filter_append]
      split <;> simp_all
    by_cases hl : (st.s (uint.nat x)).state = leader
    · rw [decide_eq_true (hL.2 hl)]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      wp_apply wp_slice_append $$ [Hsl Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, ← hna]; simp [hl]
    · rw [decide_eq_false (fun e => hl (hL.1 e))]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, ← hna]; simp [hl]
  · have hnx : sint.nat n = st.server.length := by rw [← Hxm, List.length_map, Hxl.1]; word
    rw [hnx, List.take_length] at hna
    imod ownSlice_persist $$ Hsl with #Hsl
    imodintro
    iapply HΦ
    iunfold setRO
    iexists ys
    iframe Hsl
    ipureintro; rw [hna]; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
