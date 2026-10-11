/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newUniqueEphemeralKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKey
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem newUniqueEphemeralKey.wp_proof
    (hNUEKV : newUniqueEphemeralKV.spec (GF := GF) (hG := hG)) :
    newUniqueEphemeralKey.spec (GF := GF) (hG := hG) := by
  intro s γ client id pfx kp lo
  wp_start as ⟨#Hsess, #Hcl, #Hlo, %Hk⟩
  wp_auto
  wp_apply hNUEKV s γ client id pfx kp [] lo $$ [$Hpkg $Hsess $Hcl $Hlo] as %ek %err Hres
  · ipureintro; exact Hk
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end recipes
end EtcdGrove
end Perennial
