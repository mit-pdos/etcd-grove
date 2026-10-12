/-
Proof of `Spec/.../mvcc/treeIndex__keyIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__keyIndex
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.keyIndex.wp_proof
    (wp_Get : btree.BTree.Get.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.keyIndex.spec (GF := GF) (hG := hG) := by
  have wp_Get : btree.BTree.Get.modelSpec (GF := GF) (hG := hG) := btree.BTree.Get.modelSpec_of wp_Get
  intro ti t L q keyi k
  wp_start as ⟨#Htree, Htr, #Hkeyi⟩
  iunfold mvcc.ownTree at Htr
  icases Htr with ⟨%Hsorted, Ht, Hkis⟩
  wp_auto
  wp_apply (wp_Get mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ _ keyi (keyi, k)) $$ [$Ht $Hkeyi]
    as %item %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  have Hfind := mvcc.btFind_items L Hsorted keyi k
  generalize btFind mvcc.kiItemLess (keyi, k) (mvcc.itemsOfEntries L) = f at Hfind ⊢
  cases f with
  | none =>
    icases Hres with % ⟨Hok, Hitem⟩
    subst Hok Hitem
    wp_auto
    iapply HΦ
    isplitl [Ht Hkis]
    · iunfold mvcc.ownTree; iframe Ht Hkis; ipureintro; exact Hsorted
    ipureintro
    cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none => rfl
    | some z => rw [hf] at Hfind; simp at Hfind
  | some v =>
    icases Hres with ⟨%Hok, #Hitem⟩
    subst Hok
    iunfold mvcc.kiItemIs at Hitem
    icases Hitem with ⟨%Hiv, -⟩
    wp_auto
    iapply HΦ
    isplitl [Ht Hkis]
    · iunfold mvcc.ownTree; iframe Ht Hkis; ipureintro; exact Hsorted
    ipureintro
    cases hf : L.find? (fun z => decide (z.2.1 = k)) with
    | none => rw [hf] at Hfind; simp at Hfind
    | some z =>
      rw [hf] at Hfind
      simp only [Option.map_some, Option.some.injEq] at Hfind
      rw [Hiv, Hfind]
      rfl

end proof

end EtcdGrove
end Perennial
