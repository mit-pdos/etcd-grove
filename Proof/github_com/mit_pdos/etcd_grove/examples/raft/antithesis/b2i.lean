/-
Lean-first (no Rocq counterpart). #33 parity B2: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/b2i.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.b2i

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem b2i.wp_proof : b2i.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  cases b
  · wp_auto
    simp only [Bool.false_eq_true, ↓reduceIte]
    iapply HΦ
    itrivial
  · wp_auto
    simp only [↓reduceIte]
    iapply HΦ
    itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
