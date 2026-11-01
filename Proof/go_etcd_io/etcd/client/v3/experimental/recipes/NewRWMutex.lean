/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewRWMutex.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.NewRWMutex
public import Spec.context.TODO

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

theorem NewRWMutex.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    NewRWMutex.spec (GF := GF) (hG := hG) := by
  intro s γ client id pfx
  wp_start as ⟨#Hs, #Hc, #Hcl, %Hpl⟩
  iapply wp_fupd
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  irename «$r0» => Hm
  generalize «$r0_ptr» = m at *
  iStructNamed Hm
  ipersist s
  ipersist ctx
  ipersist pfx
  imodintro
  iapply HΦ
  unfold isRWMutex
  iframe #
  isplitr
  · ipureintro; exact ⟨by simp, by simp; omega⟩
  unfold rwMyKey
  iexists _
  iframe

end proof

end recipes
end EtcdGrove
end Perennial
