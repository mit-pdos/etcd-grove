/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/WitnessStore__Close.lean`. Lean-first (2026-10-20,
witness support).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStore__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem WitnessStore.Close.wp_proof : WitnessStore.Close.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end kvwitness
end EtcdGrove
end Perennial
