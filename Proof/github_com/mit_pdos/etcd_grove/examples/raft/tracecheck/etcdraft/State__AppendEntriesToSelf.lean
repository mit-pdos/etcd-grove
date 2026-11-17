/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AppendEntriesToSelf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesToSelf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__send

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

theorem State.AppendEntriesToSelf.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_send : State.send.spec (GF := GF) (hG := hG)) :
    State.AppendEntriesToSelf.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hok⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  have hL := strRel_eq_iff Hf.2.1 (show strRel go!"StateLeader" leader by unfold strRel leader; decide)
  by_cases hl : (st.s (uint.nat i)).state = leader
  · rw [decide_eq_true (hL.2 hl)]
    wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    ihave #Hnil := logRO_nil (GF := GF)
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hmsg : msgRO (GF := GF) «$a0_ptr» { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat i } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      exact ⟨rfl, (show strRel go!"app" "app" by unfold strRel; decide), Hf.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [← Hell, Hesl.1]; word, rfl, rfl⟩
    wp_apply wp_send t st [] _ _ $$ [Ht Hmsg] as Ht
    · iframe Ht Hmsg; ipureintro; exact ⟨Hok.1, Hok.count_lt _⟩
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.appendEntriesToSelf (uint.nat i) = some (st.send { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat i }) := by
      unfold State.appendEntriesToSelf; simp [hl]
    rw [this]
    iexact Ht
  · rw [decide_eq_false (fun e => hl (hL.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.appendEntriesToSelf (uint.nat i) = none := by
      unfold State.appendEntriesToSelf; simp [hl]
    rw [this]
    ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
