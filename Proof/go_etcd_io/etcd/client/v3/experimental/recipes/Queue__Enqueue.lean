/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Queue__Enqueue.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Queue__Enqueue
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem Queue.Enqueue.wp_proof (hNUK : newUniqueKV.spec (GF := GF) (hG := hG)) :
    Queue.Enqueue.spec (GF := GF) (hG := hG) := by
  intro q client kp val lo
  wp_start as ⟨#Hq, #Hlo, %Hv⟩
  iunfold isQueue at Hq
  icases Hq with ⟨#Hqc, -, #Hqk, %Hkp, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  wp_auto
  wp_apply hNUK kv kp kp val lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact ⟨List.prefix_refl kp, by omega, Hv⟩
  icases Hres with (⟨%Heq, %key, %r, -, #Hr, #Hc, %Hrr⟩ | %Hne)
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, r
    iframe Hr Hc
    ipureintro; exact ⟨Hrr.1, Hrr.2.1⟩
  · (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hne.1

end proof

end recipes
end EtcdGrove
end Perennial
