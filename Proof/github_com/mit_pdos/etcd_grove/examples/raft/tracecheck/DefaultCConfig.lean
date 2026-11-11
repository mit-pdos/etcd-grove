/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11): the proof of
`DefaultCConfig`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.DefaultCConfig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem DefaultCConfig.wp_proof : DefaultCConfig.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  unfold defaultCConfig
  iapply HΦ
  itrivial

end proof

end TraceCheck
end EtcdGrove
end Perennial
