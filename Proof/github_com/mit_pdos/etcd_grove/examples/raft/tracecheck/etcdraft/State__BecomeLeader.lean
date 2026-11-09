/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__BecomeLeader`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__BecomeLeader
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsQuorum

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

theorem State.BecomeLeader.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_IsQuorum : IsQuorum.spec (GF := GF) (hG := hG)) :
    State.BecomeLeader.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hvgl⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Candidate]
  rw [decide_strRel Hf.2.1 strRel_candidate]
  by_cases h1 : (st.s (uint.nat i)).state = candidate
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    imodintro
    iapply HΦ
    have : st.becomeLeader (uint.nat i) = none := by
      unfold State.becomeLeader; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true h1]
  wp_auto
  wp_apply wp_GetConfig p st i $$ [Hst] as %sl2 #Hsl2
  · iframe Hst; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_IsQuorum _ _ _ _ $$ [Hvg Hsl2]
  · iframe Hvg Hsl2; ipureintro; exact Hvgl
  iintro -
  try wp_auto
  cases hq : isQuorum (st.s (uint.nat i)).votesGranted (st.getConfig (uint.nat i))
  · wp_auto
    imodintro
    iapply HΦ
    have : st.becomeLeader (uint.nat i) = none := by
      unfold State.becomeLeader; simp [hq]
    rw [this]
    ipureintro; rfl
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  mut_open t, st, [], i, Ht
  ipersist i
  ipersist v
  ipersist w
  irename i => Hip
  irename v => Hvp
  irename w => Hwp
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %nm Hnm
  try wp_auto
  iunfold setRO at Hsrv
  icases Hsrv with ⟨%xs, #Hxs, %Hxm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  rename_i ip
  ihave IH : iprop(∃ (n jv : w64) (mp : GMap w64 w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "Hnm" ∷ nm ↦$ mp ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Server'.len ∧
        ∀ x : w64, mp !! x = if x = i ∧ uint.nat i ∈ st.server.take (sint.nat n) then some gs.Log'.len else none⌝)
      $$ [i j Hnm]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun x => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hif : sint.Z n < sint.Z g.Server'.len := by simpa using Hif
    have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsx : st.server[sint.nat n]? = some (uint.nat x) := by rw [← Hxm, List.getElem?_map, Hx]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hx
    try wp_auto
    have htake : ∀ y, (y ∈ st.server.take (sint.nat (n + W64 1))) ↔ (y ∈ st.server.take (sint.nat n) ∨ y = uint.nat x) := by
      intro y
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hsx]
      simp
    have htake' : ∀ y, (y ∈ st.server.take (sint.nat (n + 1#64))) ↔ (y ∈ st.server.take (sint.nat n) ∨ y = uint.nat x) := htake
    by_cases hx : x = i
    · rw [decide_eq_true hx]
      try wp_auto
      wp_apply wp_mapInsert $$ [Hnm] as Hnm
      · iexact Hnm
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun y => ?_⟩
      subst hx
      by_cases hy : y = x
      · subst hy; rw [GMap.lookup_insert]; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, (htake' _).2 (Or.inr rfl)⟩)]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy), hna y]; simp [hy]
    · rw [decide_eq_false hx]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun y => ?_⟩
      rw [hna y]
      have : uint.nat i ≠ uint.nat x := fun e => hx (word.unsigned_inj (by exact_mod_cast e.symm))
      simp [htake', this]
  · have hnx : sint.nat n = st.server.length := by rw [← Hxm, List.length_map, Hxl.1]; word
    rw [hnx, List.take_length] at hna
    try wp_auto
    have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
    have Hcmi' : ∀ x : w64, sint.Z ((mp !! x).getD (W64 0)) = ((fun (v : Server) => { v with state := leader, lead := uint.nat i, matchIndex := fun j => if j = uint.nat i then (v.log.length : Int) else 0 }) (st.s (uint.nat i))).matchIndex (uint.nat x) := by
      intro x
      rw [hna x]
      by_cases hx : x = i
      · subst hx; simp [Hi, hlen]
      · have : uint.nat x ≠ uint.nat i := fun e => hx (word.unsigned_inj (by exact_mod_cast e))
        simp [hx, this]
    ihave Hcp : cp ↦ ({ gc with State' := go!"StateLeader", Lead' := i, MatchIndex' := nm } : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
        VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp ({ gc with State' := go!"StateLeader", Lead' := i, MatchIndex' := nm } : G.Server) mp ((fun (v : Server) => { v with state := leader, lead := uint.nat i, matchIndex := fun j => if j = uint.nat i then (v.log.length : Int) else 0 }) (st.s (uint.nat i)))
      ⟨Hcf.1, strRel_leader, Hcf.2.2.1, rfl, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩ Hcmi' $$ [Hcp Hnm]
    · iframe Hcp Hnm Hcl Hcr Hcg Hcc Hcd
    ihave Hs := stateOwnHole_close_upd _ _ _ _ _ (fun (v : Server) => { v with state := leader, lead := uint.nat i, matchIndex := fun j => if j = uint.nat i then (v.log.length : Int) else 0 }) Hi $$ [Hh Hc]
    · iframe
    imod stateOwn_persist $$ Hs with #Hs
    imodintro
    iapply HΦ
    have : st.becomeLeader (uint.nat i) = some (st.upd (uint.nat i) (fun (v : Server) => { v with state := leader, lead := uint.nat i, matchIndex := fun j => if j = uint.nat i then (v.log.length : Int) else 0 })) := by
      unfold State.becomeLeader; simp [h1, hq]
    rw [this]
    iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
