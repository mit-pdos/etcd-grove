/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `AckFact` (B 73).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.AckFact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem AckFact.wp_proof : AckFact.spec (GF := GF) (hG := hG) := by
  intro src dst t k
  wp_start as #_
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
