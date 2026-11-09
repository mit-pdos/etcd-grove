/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__becomeFollowerOfTerm`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__becomeFollowerOfTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

theorem State.becomeFollowerOfTerm.wp_proof (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.becomeFollowerOfTerm.spec (GF := GF) (hG := hG) := by
  intro p st M i term
  wp_start as ⟨Hst, %Hi⟩
  wp_auto
  mut_open p, st, M, i, Hst
  simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Follower,
    github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Nil]
  wp_auto
  have hF : strRel go!"StateFollower" follower := by unfold strRel follower; decide
  have e1 := sint_eq_iff gc.CurrentTerm' term _ _ Hcf.1 rfl
  by_cases ht : (st.s (uint.nat i)).currentTerm = sint.Z term
  · rw [decide_eq_true (e1.2 ht)]
    wp_auto
    close_copy { gc with CurrentTerm' := term, State' := go!"StateFollower", Lead' := W64 0 },
      (fun v => { v with currentTerm := sint.Z term, state := follower, lead := nil, votedFor := if v.currentTerm != sint.Z term then nil else v.votedFor }),
      ⟨rfl, hF, by simp [ht, Hcf.2.2.1], rfl, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩
    iapply HΦ; unfold State.becomeFollowerOfTerm; iexact Hs
  · rw [decide_eq_false (fun x => ht (e1.1 x))]
    wp_auto
    close_copy { gc with CurrentTerm' := term, State' := go!"StateFollower", Lead' := W64 0, VotedFor' := W64 0 },
      (fun v => { v with currentTerm := sint.Z term, state := follower, lead := nil, votedFor := if v.currentTerm != sint.Z term then nil else v.votedFor }),
      ⟨rfl, hF, by simp [ht]; rfl, rfl, Hcf.2.2.2.2.1, Hcf.2.2.2.2.2⟩
    iapply HΦ; unfold State.becomeFollowerOfTerm; iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
