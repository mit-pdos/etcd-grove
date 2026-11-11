/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/config.lean`. Lean-first (no
Rocq counterpart): the struct literal, stored and loaded.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.config

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

theorem config.wp_proof : config.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end etcd_partition
end EtcdGrove
end Perennial
