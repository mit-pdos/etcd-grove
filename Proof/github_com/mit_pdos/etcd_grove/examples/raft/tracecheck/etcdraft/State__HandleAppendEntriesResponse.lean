/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__HandleAppendEntriesResponse`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HandleAppendEntriesResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__discard

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

theorem State.HandleAppendEntriesResponse.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_discard : State.discard.spec (GF := GF) (hG := hG)) :
    State.HandleAppendEntriesResponse.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hmnd⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have ht := sint_eq_iff gm.Term' gs.CurrentTerm' _ _ Hv.2.2.1 Hf.1
  by_cases h1 : m.term = (st.s (uint.nat i)).currentTerm
  rotate_left
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.handleAppendEntriesResponse (uint.nat i) (uint.nat j) m = none := by
      unfold State.handleAppendEntriesResponse; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true (ht.2 h1)]
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  rw [Hv.2.2.2.2.2.2.2.2.2.1]
  cases hs : m.success
  · try wp_auto
    wp_apply wp_discard t st [] q m $$ [Ht Hmsg] as Ht
    · iframe Ht Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.handleAppendEntriesResponse (uint.nat i) (uint.nat j) m = some (st.discard m) := by
      unfold State.handleAppendEntriesResponse; simp [h1, hs]
    rw [this]
    iexact Ht
  · try wp_auto
    mut_open t, st, [], i, Ht
    try wp_auto
    wp_apply wp_map_lookup1 $$ [Hmm] as -
    · iexact Hmm
    try wp_auto
    wp_apply wp_max_int
    try wp_auto
    wp_apply wp_mapInsert $$ [Hcm] as Hcm
    · iexact Hcm
    try wp_auto
    rw [show (zero_val w64 : w64) = W64 0 from rfl]
    have Hcmi' : ∀ x : w64, sint.Z (((GMap.insert j (if sint.Z gm.MatchIndex' < sint.Z ((mm !! j).getD (W64 0)) then (mm !! j).getD (W64 0) else gm.MatchIndex') mc) !! x).getD (W64 0)) =
        (if uint.nat x = uint.nat j then max ((st.s (uint.nat i)).matchIndex (uint.nat j)) m.matchIndex
          else (st.s (uint.nat i)).matchIndex (uint.nat x)) := by
      intro x
      by_cases hx : x = j
      · subst hx
        rw [GMap.lookup_insert]
        simp only [Option.getD_some, ite_true]
        rw [sint_max, Hmi, Hv.2.2.2.2.2.2.2.2.2.2.1]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hcmi x]
        have : uint.nat x ≠ uint.nat j := fun e => hx (word.unsigned_inj (by exact_mod_cast e))
        simp [this]
    ihave Hcp : cp ↦ (gc : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
        VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp gc _
      ((fun w => { w with matchIndex := fun k => if k = uint.nat j then max ((st.s (uint.nat i)).matchIndex (uint.nat j)) m.matchIndex else w.matchIndex k }) (st.s (uint.nat i))) Hcf Hcmi' $$ [Hcp Hcm]
    · iframe Hcp Hcm Hcl Hcr Hcg Hcc Hcd
    ihave Hs := stateOwnHole_close_upd _ _ _ _ _
      (fun w => { w with matchIndex := fun k => if k = uint.nat j then max ((st.s (uint.nat i)).matchIndex (uint.nat j)) m.matchIndex else w.matchIndex k }) Hi $$ [Hh Hc]
    · iframe
    wp_apply wp_discard t _ _ q m $$ [Hs Hmsg] as Ht
    · iframe Hs Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    unfold State.handleAppendEntriesResponse
    simp only [hs, h1, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
