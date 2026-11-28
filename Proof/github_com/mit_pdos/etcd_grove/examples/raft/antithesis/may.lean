/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/may.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.may
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.coin

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

theorem may.wp_proof (wp_coin : coin.spec (GF := GF) (hG := hG)) :
    may.spec (GF := GF) (hG := hG) := by
  intro on
  wp_start
  wp_auto
  cases on
  · wp_auto
    iapply HΦ
    ipureintro; intro h; exact h
  · wp_auto
    wp_apply wp_coin as %b _
    try wp_auto
    iapply HΦ
    ipureintro; intro _; rfl

end proof

end AntHarness
end EtcdGrove
end Perennial
