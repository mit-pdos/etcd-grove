/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/coin.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.coin
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below

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

theorem coin.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    coin.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_below (W64 2) (by decide) as %r _
  try wp_auto
  iapply HΦ
  itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
