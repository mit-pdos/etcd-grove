/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewDoubleBarrier.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.NewDoubleBarrier
public import Spec.context.TODO

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem NewDoubleBarrier.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    NewDoubleBarrier.spec (GF := GF) (hG := hG) := by
  intro s γ client id key count
  wp_start as ⟨#Hs, #Hc, #Hcl, %Hcount⟩
  iapply wp_fupd
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  wp_alloc m as Hm
  iStructNamed Hm
  wp_auto
  ipersist s
  ipersist ctx
  ipersist key
  ipersist count
  imodintro
  iapply HΦ
  unfold isDoubleBarrier
  iframe #
  isplitr
  · ipureintro; exact Hcount
  unfold dbMyKey
  iexists _
  iframe

end proof

end recipes
end EtcdGrove
end Perennial
