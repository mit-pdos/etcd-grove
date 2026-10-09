/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__WithPrefix.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__ensureCompare
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetKey
public import Spec.go_etcd_io.etcd.client.v3.getPrefix
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Cmp.WithPrefix.wp_proof (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_ensureCompare : Cmp.ensureCompare.spec (GF := GF) (hG := hG))
    (wp_GetKey : Compare.GetKey.spec (GF := GF) (hG := hG))
    (wp_getPrefix : getPrefix.spec (GF := GF) (hG := hG)) :
    Cmp.WithPrefix.spec (GF := GF) (hG := hG) := by
  intro c m
  wp_start as #Hc
  iapply wp_fupd
  wp_auto
  wp_apply wp_Clone $$ [$cmp $Hc] as %c' ⟨cmp, %Hnn, Hown⟩
  try wp_auto
  wp_apply wp_ensureCompare $$ [$cmp] as cmp
  · iframe %
  unfold compareOwn
  icases Hown with ⟨%ksl, %esl, %u, Hres, #Htgt, #Hkey, #Hks, Hend, #Hes, Hu, #Hua⟩
  ihave %Hcn := typedPointsto_not_null _ _ _ $$ cmp
  iStructNamed cmp
  try wp_auto
  wp_apply wp_GetKey $$ [$Hkey]
  · iframe %
  wp_apply wp_getPrefix $$ [$Hks] as %esl' ⟨-, #Hes'⟩
  try wp_auto
  ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
  · iapply typedPointsto_combine _ _ _ Hcn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  try wp_auto
  ipersist Hres
  ipersist Hend
  ipersist Hu
  imodintro
  iapply HΦ
  unfold cmpAt compareAt
  dsimp only [cmpWithPrefixM]
  isplitl []
  · ipureintro; exact Hnn
  iexists ksl, esl', u
  iframe #
  unfold compareUnionAt
  iexact Hua

end proof

end EtcdGrove
end Perennial
