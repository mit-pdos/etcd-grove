/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__Init`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Init

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

theorem Trace.Init.wp_proof : Trace.Init.spec (GF := GF) (hG := hG) := by
  intro t tr
  wp_start as #Ht
  open_trace
  wp_auto
  iapply HΦ
  iunfold tstateRO
  simp only [Trace.initState]
  isplitr
  · iexact Hinit0
  ipureintro
  exact ⟨rfl, rfl⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial
