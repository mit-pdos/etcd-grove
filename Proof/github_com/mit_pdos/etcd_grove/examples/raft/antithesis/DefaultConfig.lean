/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/DefaultConfig.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DefaultConfig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

theorem DefaultConfig.wp_proof : DefaultConfig.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave H : Φ #defaultCfg $$ [HΦ]
  · iapply HΦ
    ipureintro; trivial
  iExactEq H
  congr 1

end proof

end AntHarness
end EtcdGrove
end Perennial
