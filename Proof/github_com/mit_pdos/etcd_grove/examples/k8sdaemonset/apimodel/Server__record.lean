/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__record.lean`.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__record
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.SrvLemmas
public import Perennial.Spec.sync.Cond__Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem Server.record.wp_proof
    (wp_GetNamespace : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_Broadcast : sync.Cond.Broadcast.spec (GF := GF) (hG := hG)) :
    Server.record.spec (GF := GF) (hG := hG) := by
  intro _ s γ L cfg r tb typ rv obj o
  wp_start as ⟨#Hs, Ht, Ho⟩
  wp_auto
  wp_apply (objAt_GetNamespace wp_GetNamespace obj o) $$ Ho as Ho
  wp_apply (objAt_GetName wp_GetName obj o) $$ Ho as Ho
  ihave ⟨#Hfx, -⟩ := srvFixed_tbl s γ L cfg r $$ Hs
  iunfold tableFixed at Hfx
  icases Hfx with ⟨#Hres, #Hnsd, #Hobjs, #Hemp, -⟩
  iunfold tableLocked at Ht
  icases Ht with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
  cases typ <;> simp only [EvTy.str] <;> wp_auto
  · wp_apply (wp_mapInsert k8s_io.apimachinery.pkg.types.NamespacedName.ty (L.tbl r).objs M
      (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name') obj) $$ HM as HM
    wp_apply wp_copyObject $$ Ho as %x ⟨Ho, Hx⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply (wp_slice_append sl cs _ _ (DFrac.own 1)) $$ [Hsl Hcap Hasl] as %s' ⟨Hsl, Hcap, -⟩
    · iframe
    iNamed Hs
    wp_auto
    wp_apply (wp_Broadcast L.cond _) $$ Hcond
    iapply HΦ
    unfold tableLocked Table.record applyChange
    simp only
    iexists _, s', _
    iframe HM Hlog Hsl Hcap
    isplitl [Hrel Ho]
    · rw [show (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name') = o.key from rfl]
      iapply objsRel_insert
      iframe
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hcs
    unfold changeAt
    iframe Hx
    ipureintro
    exact ⟨rfl, rfl⟩
  · wp_apply (wp_mapInsert k8s_io.apimachinery.pkg.types.NamespacedName.ty (L.tbl r).objs M
      (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name') obj) $$ HM as HM
    wp_apply wp_copyObject $$ Ho as %x ⟨Ho, Hx⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply (wp_slice_append sl cs _ _ (DFrac.own 1)) $$ [Hsl Hcap Hasl] as %s' ⟨Hsl, Hcap, -⟩
    · iframe
    iNamed Hs
    wp_auto
    wp_apply (wp_Broadcast L.cond _) $$ Hcond
    iapply HΦ
    unfold tableLocked Table.record applyChange
    simp only
    iexists _, s', _
    iframe HM Hlog Hsl Hcap
    isplitl [Hrel Ho]
    · rw [show (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name') = o.key from rfl]
      iapply objsRel_insert
      iframe
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hcs
    unfold changeAt
    iframe Hx
    ipureintro
    exact ⟨rfl, rfl⟩
  · wp_apply (wp_mapDelete (L.tbl r).objs M (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name')
      k8s_io.apimachinery.pkg.types.NamespacedName.ty apimodel.object.ty) $$ HM as HM
    wp_apply wp_copyObject $$ Ho as %x ⟨Ho, Hx⟩
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply (wp_slice_append sl cs _ _ (DFrac.own 1)) $$ [Hsl Hcap Hasl] as %s' ⟨Hsl, Hcap, -⟩
    · iframe
    iNamed Hs
    wp_auto
    wp_apply (wp_Broadcast L.cond _) $$ Hcond
    iapply HΦ
    unfold tableLocked Table.record applyChange
    simp only
    iexists _, s', _
    iframe HM Hlog Hsl Hcap
    isplitl [Hrel Ho]
    · rw [show (k8s_io.apimachinery.pkg.types.NamespacedName.mk o.meta.Namespace' o.meta.Name') = o.key from rfl]
      iapply objsRel_delete
      iframe
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hcs
    unfold changeAt
    iframe Hx
    ipureintro
    exact ⟨rfl, rfl⟩

end proof

end apimodel
end EtcdGrove
end Perennial
