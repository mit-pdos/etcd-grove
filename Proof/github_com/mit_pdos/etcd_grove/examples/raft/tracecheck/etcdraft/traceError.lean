/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `traceError`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.traceError

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

theorem traceError.wp_proof : traceError.spec (GF := GF) (hG := hG) := by
  intro what line n
  wp_start as -
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; ipureintro
  simp

end proof

end Etcdraft
end EtcdGrove
end Perennial
