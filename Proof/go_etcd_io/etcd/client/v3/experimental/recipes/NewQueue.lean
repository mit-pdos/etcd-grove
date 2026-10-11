/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewQueue.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.NewQueue
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

theorem NewQueue.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    NewQueue.spec (GF := GF) (hG := hG) := by
  intro client kp
  wp_start as ⟨#Hc, %Hkp⟩
  iapply wp_fupd
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  wp_alloc q as Hq
  iStructNamed Hq
  wp_auto
  ipersist client
  ipersist ctx
  ipersist keyPrefix
  imodintro
  iapply HΦ
  unfold isQueue
  iframe #
  ipureintro; exact Hkp

end proof

end recipes
end EtcdGrove
end Perennial
