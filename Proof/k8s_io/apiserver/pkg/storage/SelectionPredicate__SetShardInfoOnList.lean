/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__SetShardInfoOnList.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__SetShardInfoOnList
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__ShardingEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.SelectionPredicate.SetShardInfoOnList.wp_proof
    (wp_ShardingEnabled : storage.SelectionPredicate.ShardingEnabled.spec (GF := GF) (hG := hG))
    : storage.SelectionPredicate.SetShardInfoOnList.spec (GF := GF) (hG := hG) := by
  intro pp dq p lx hs
  wp_start as Hp
  (try wp_auto)
  wp_apply (wp_ShardingEnabled pp dq p hs) $$ [$Hp] as Hp
  (try wp_auto)
  iapply HΦ $$ Hp

end proof

end EtcdGrove
end Perennial
