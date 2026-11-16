/-
Proof of `Spec/go_etcd_io/etcd/api/v3/mvccpb/Event__IsCreate.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event__IsCreate
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event__GetType
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event__GetKv
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.KeyValue__GetCreateRevision
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.KeyValue__GetModRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.mvccpb.Assumptions]

theorem mvccpb.Event.IsCreate.wp_proof
    (wp_GetType : mvccpb.Event.GetType.spec (GF := GF) (hG := hG))
    (wp_GetKv : mvccpb.Event.GetKv.spec (GF := GF) (hG := hG))
    (wp_GetCR : mvccpb.KeyValue.GetCreateRevision.spec (GF := GF) (hG := hG))
    (wp_GetMR : mvccpb.KeyValue.GetModRevision.spec (GF := GF) (hG := hG)) :
    mvccpb.Event.IsCreate.spec (GF := GF) (hG := hG) := by
  intro p kv t cr mr
  have hdec : decide (t = W32 0 ∧ cr = mr) = (if t = W32 0 then decide (cr = mr) else false) := by
    by_cases ht : t = W32 0 <;> simp [ht]
  rw [hdec]
  wp_start as ⟨⟨%Hp, %Hkv⟩, #Ht, #Hk, #Hcr, #Hmr⟩
  wp_auto
  wp_apply wp_GetType p t $$ []
  · iframe #; ipureintro; exact Hp
  wp_if_destruct
  · wp_apply wp_GetKv p kv $$ []
    · iframe #; ipureintro; exact Hp
    wp_apply wp_GetCR kv cr $$ []
    · iframe #; ipureintro; exact Hkv
    wp_apply wp_GetKv p kv $$ []
    · iframe #; ipureintro; exact Hp
    wp_apply wp_GetMR kv mr $$ []
    · iframe #; ipureintro; exact Hkv
    try simp only [ite_true]
    iapply HΦ; itrivial
  · rename_i Hif
    try simp only [Hif, ite_false]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
