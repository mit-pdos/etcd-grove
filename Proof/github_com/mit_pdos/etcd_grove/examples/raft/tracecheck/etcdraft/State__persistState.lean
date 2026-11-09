/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__persistState`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__persistState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.durableOf

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

theorem State.persistState.wp_proof (wp_mut : State.mut.spec (GF := GF) (hG := hG))
    (wp_durableOf : durableOf.spec (GF := GF) (hG := hG)) :
    State.persistState.spec (GF := GF) (hG := hG) := by
  intro p st M i
  wp_start as ⟨Hst, %Hi⟩
  wp_auto
  mut_open p, st, M, i
  ihave Hcp : cp ↦ gc $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
      VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_durableOf cp (DFrac.own 1) gc (st.s (uint.nat i)) $$ [Hcp] as %d ⟨Hcp, #Hd⟩
  · iframe Hcp Hcl Hcc
    ipureintro; exact ⟨Hcf.1, Hcf.2.2.1, Hcf.2.2.2.2.1⟩
  icases typedPointsto_split _ _ _ $$ Hcp with Hcpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcpf
  try wp_auto
  ihave Hcp : cp ↦ ({ gc with Durable' := d } : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex
      VotesResponded VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hc := serverOwn_intro cp ({ gc with Durable' := d } : G.Server) mc
      ((fun v => { v with durable := durableOf v }) (st.s (uint.nat i))) Hcf Hcmi $$ [Hcp Hcm]
  · iframe Hcp Hcm Hcl Hcr Hcg Hcc Hd
  ihave Hs := stateOwnHole_close_upd _ _ _ _ _ (fun v => { v with durable := durableOf v }) Hi $$ [Hh Hc]
  · iframe
  iapply HΦ; unfold State.persistState; iexact Hs

end proof

end Etcdraft
end EtcdGrove
end Perennial
