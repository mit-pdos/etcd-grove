/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__Empty.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Empty
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__ShardingEnabled
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__labelFieldEmpty

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

theorem storage.SelectionPredicate.Empty.wp_proof
    (wp_ShardingEnabled : storage.SelectionPredicate.ShardingEnabled.spec (GF := GF) (hG := hG))
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG) := by
  intro pp dq p le fe lm fm hs
  wp_start as ⟨Hp, #Hl, #Hf⟩
  (try wp_auto)
  wp_apply (wp_ShardingEnabled pp dq p hs) $$ [$Hp] as Hp
  (try wp_auto)
  wp_apply (wp_labelFieldEmpty pp dq p le fe lm fm) $$ [$Hp $Hl $Hf] as Hp
  (try wp_auto)
  iapply HΦ $$ Hp

end proof

end EtcdGrove
end Perennial
