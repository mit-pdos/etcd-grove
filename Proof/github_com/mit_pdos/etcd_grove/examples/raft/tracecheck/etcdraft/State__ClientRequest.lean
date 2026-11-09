/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__ClientRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ClientRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__replicate

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

theorem State.ClientRequest.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_replicate : State.replicate.spec (GF := GF) (hG := hG)) :
    State.ClientRequest.spec (GF := GF) (hG := hG) := by
  intro p st i val
  wp_start as ⟨#Hst, %Hi⟩
  read_server
  iapply wp_fupd
  wp_auto
  lookup_server
  try simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Leader]
  rw [decide_strRel Hf.2.1 strRel_leader]
  by_cases h1 : (st.s (uint.nat i)).state = leader
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    imodintro
    iapply HΦ
    have : st.clientRequest (uint.nat i) (sint.Z val) = none := by
      unfold State.clientRequest; simp [h1]
    rw [this]
    ipureintro; rfl
  rw [decide_eq_true h1]
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) DfracDiscarded
  wp_apply wp_replicate t st [] i _ (.val (sint.Z val)) .value $$ [Ht] as Ht
  · iframe Ht
    isplitl []
    · iunfold valueRO
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iunfold setRO; iexists []; iframe Hnil; ipureintro; rfl
      iunfold setRO; iexists []; iframe Hnil; ipureintro; rfl
    ipureintro; exact Hi
  try wp_auto
  imod stateOwn_persist $$ Ht with #Ht
  imodintro
  iapply HΦ
  have : st.clientRequest (uint.nat i) (sint.Z val) = some (st.replicate (uint.nat i) (.val (sint.Z val)) .value) := by
    unfold State.clientRequest; simp [h1]
  rw [this]
  iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
