/-
Proof of `Spec/OpGet.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.IsOptsWithPrefix
public import Spec.go_etcd_io.etcd.client.v3.IsOptsWithFromKey
public import Spec.go_etcd_io.etcd.client.v3.Op__applyOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem OpGet.wp_proof (wp_IsOptsWithPrefix : IsOptsWithPrefix.spec (GF := GF) (hG := hG))
    (wp_IsOptsWithFromKey : IsOptsWithFromKey.spec (GF := GF) (hG := hG))
    (wp_applyOpts : Op.applyOpts.spec (GF := GF) (hG := hG)) :
    OpGet.spec (GF := GF) (hG := hG) := by
  intro key sl gs
  wp_start as ⟨#Hopts, %Hnp⟩
  wp_alloc o_ptr as Ho
  wp_auto
  wp_apply wp_IsOptsWithPrefix $$ [$Hopts]
  have Hrest : ∀ Φ' : val → IProp GF,
      (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ o_ptr ↦ sl ∗
        optsAt sl gs ∗ (∀ op, opFullAt op (opGetModel key gs) -∗ Φ' #op)) ⊢
      WP (exceptionDo
        (let: "$r0" :=
          let: "$v1" := (Convert go.string go.byte.SliceType) #key in
            (CompositeLiteral go_etcd_io.etcd.client.v3.Op.ty)
              (LiteralValue
                [KeyedElement (some (KeyField go!"t"))
                    (ElementExpression go_etcd_io.etcd.client.v3.opType.ty go_etcd_io.etcd.client.v3.tRange),
                  KeyedElement (some (KeyField go!"key")) (ElementExpression go.byte.SliceType "$v1")]) in
          let: "ret" := (GoAlloc go_etcd_io.etcd.client.v3.Op.ty) ((GoZeroVal go_etcd_io.etcd.client.v3.Op.ty) #()) in
            do: "ret" <-[go_etcd_io.etcd.client.v3.Op.ty] "$r0" ;;;
              do:
                  (let: "$a0" := ![go_etcd_io.etcd.client.v3.OpOption.ty.SliceType] #o_ptr in
                    ((MethodResolve go_etcd_io.etcd.client.v3.Op.ty.PointerType go!"applyOpts") "ret") "$a0") ;;;
                return: ![go_etcd_io.etcd.client.v3.Op.ty] "ret")) {{ Φ' }}) := by
    intro Φ'
    iintro ⟨#Hpkg, Ho, #Hopts, HΦ'⟩
    iapply wp_fupd
    wp_apply wp_string_to_bytes key as %ksl ⟨Hks, -⟩
    ipersist Hks
    wp_apply wp_applyOpts ret_ptr _ (OpFull.getInit key) sl gs $$ [$ret] as %op' ⟨Hret, #Hat⟩
    · iframe #
      unfold opFullAt opAt OpFields
      dsimp only [OpFull.getInit, OpFull.newOp, OpModel.zero]
      isplitl []
      · isplitl []
        · ipureintro; simp
        · iapply ownSlice_nil
      isplitl []
      · iexact Hks
      ipureintro; simp
    imodintro
    iapply HΦ'
    unfold opGetModel
    iexact Hat
  cases hp : (opFold gs OpFull.newOp).withPrefix
  · wp_auto
    iapply Hrest
    iframe
    iframe #
  · wp_auto
    wp_apply wp_IsOptsWithFromKey $$ [$Hopts]
    cases hk : (opFold gs OpFull.newOp).withFromKey
    · wp_auto
      iapply Hrest
      iframe
      iframe #
    · exact absurd ⟨hp, hk⟩ Hnp

end proof

end EtcdGrove
end Perennial
