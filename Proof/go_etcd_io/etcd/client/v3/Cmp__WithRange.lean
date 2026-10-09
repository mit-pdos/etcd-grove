/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__WithRange.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__WithRange
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__ensureCompare
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

theorem Cmp.WithRange.wp_proof (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_ensureCompare : Cmp.ensureCompare.spec (GF := GF) (hG := hG)) :
    Cmp.WithRange.spec (GF := GF) (hG := hG) := by
  intro c m endKey
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
  wp_apply wp_string_to_bytes endKey as %esl' ⟨Hes', -⟩
  try wp_auto
  ihave Hcmp : (cmp_ptr ↦ c' : IProp GF) $$ [c]
  · iapply typedPointsto_combine _ _ _ Hcn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  try wp_auto
  ipersist Hes'
  ipersist Hres
  ipersist Hend
  ipersist Hu
  imodintro
  iapply HΦ
  unfold cmpAt compareAt
  dsimp only [cmpWithRangeM]
  isplitl []
  · ipureintro; exact Hnn
  iexists ksl, esl', u
  iframe #
  unfold compareUnionAt
  iexact Hua

end proof

end EtcdGrove
end Perennial
