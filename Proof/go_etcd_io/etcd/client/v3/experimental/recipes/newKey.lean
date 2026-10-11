/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newKey
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newKV

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

theorem newKey.wp_proof (hNKV : newKV.spec (GF := GF) (hG := hG)) :
    newKey.spec (GF := GF) (hG := hG) := by
  intro kv pfx key lease lo
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  wp_auto
  wp_apply hNKV kv pfx key [] lease lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact Hk
  (try wp_auto)
  iapply HΦ
  icases Hres with (H | H | ⟨%Hne, -⟩)
  · ileft; iexact H
  · iright; ileft; iexact H
  · iright; iright; ipureintro; exact Hne

end proof

end recipes
end EtcdGrove
end Perennial
