/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__DropStaleResponse`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__DropStaleResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
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

theorem State.DropStaleResponse.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_discard : State.discard.spec (GF := GF) (hG := hG)) :
    State.DropStaleResponse.spec (GF := GF) (hG := hG) := by
  intro p st i j q m
  wp_start as ⟨#Hst, #Hmsg, %Hi, %Hmnd⟩
  read_server
  read_msg
  iapply wp_fupd
  wp_auto
  lookup_server
  have ht : sint.Z gm.Term' < sint.Z gs.CurrentTerm' ↔ m.term < (st.s (uint.nat i)).currentTerm := by
    rw [Hf.1, Hv.2.2.1]
  by_cases h1 : m.term < (st.s (uint.nat i)).currentTerm
  · rw [decide_eq_true (ht.2 h1)]
    wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    wp_apply wp_discard t st [] q m $$ [Ht Hmsg] as Ht
    · iframe Ht Hmsg; ipureintro; exact Hmnd
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.dropStaleResponse (uint.nat i) (uint.nat j) m = some (st.discard m) := by
      unfold State.dropStaleResponse; simp [h1]
    rw [this]
    iexact Ht
  · rw [decide_eq_false (fun e => h1 (ht.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.dropStaleResponse (uint.nat i) (uint.nat j) m = none := by
      unfold State.dropStaleResponse; simp [h1]
    rw [this]
    ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
