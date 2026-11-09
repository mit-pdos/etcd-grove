/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__RequestPreVote`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RequestPreVote

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

theorem State.RequestPreVote.wp_proof : State.RequestPreVote.spec (GF := GF) (hG := hG) := by
  intro p st i j
  wp_start as ⟨#Hst, %Hi, %Hpv⟩
  read_server
  wp_auto
  lookup_server
  rw [Hrc.2.1, Hpv]
  wp_auto
  have : st.requestPreVote (uint.nat i) (uint.nat j) = none := by
    unfold State.requestPreVote; simp [Hpv]
  rw [this]
  iapply HΦ
  ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial
