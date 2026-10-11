/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewBarrier.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.NewBarrier
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

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

theorem NewBarrier.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    NewBarrier.spec (GF := GF) (hG := hG) := by
  intro client key
  wp_start as #Hc
  iapply wp_fupd
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  wp_alloc b as Hb
  iStructNamed Hb
  wp_auto
  ipersist client
  ipersist ctx
  ipersist key
  imodintro
  iapply HΦ
  unfold isBarrier
  iframe #

end proof

end recipes
end EtcdGrove
end Perennial
