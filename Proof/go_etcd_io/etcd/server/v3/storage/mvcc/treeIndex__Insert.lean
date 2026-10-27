/-
Proof of `Spec/.../mvcc/treeIndex__Insert.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Insert
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.treeIndex.Insert.wp_proof
    (wp_ROI : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Insert.spec (GF := GF) (hG := hG) := by
  have wp_ROI : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) :=
    btree.BTree.ReplaceOrInsert.modelSpec_of wp_ROI
  intro ti L ki k gs m
  wp_start as ⟨Hix, %Hn, #Hkey, Hki, %Hnew⟩
  iunfold mvcc.ownIdxPriv at Hix
  icases Hix with ⟨%t, %lg, #Htree, #Hlg, %Hlgnn, Hmu, Htr⟩
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  ihave #Hitem : mvcc.kiItemIs (GF := GF) ki (ki, k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iexact Hkey
  -- `ti.Lock()`: the promoted method, on private memory
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add (mvcc.idxMuAddr ti)) $$ [$Hmu] as Hmu
  (try wp_auto)
  iunfold mvcc.ownTree at Htr
  icases Htr with ⟨%Hsorted, Ht, Hkis⟩
  have Hfind := mvcc.btFind_items L Hsorted ki k
  have hf : L.find? (fun z => decide (z.2.1 = k)) = none := by
    rw [List.find?_eq_none]
    intro z hz
    simpa using Hnew z hz
  rw [hf, Option.map_none] at Hfind
  -- `ti.tree.ReplaceOrInsert(ki)`
  wp_apply (wp_ROI mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ ki (ki, k))
    $$ [$Ht $Hitem] as %old %ok ⟨Ht, Hres⟩
  · ipureintro; exact mvcc.kiItemLess_swo
  rw [Hfind]
  (try wp_auto)
  -- the deferred `ti.Unlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  wp_apply (plain.wp_Unlock sync.atomic.Int32.wp_Add (mvcc.idxMuAddr ti)) $$ [$Hmu] as Hmu
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.ownIdxPriv
  iexists t, lg
  iframe Hmu
  iframe #
  isplitl []
  · ipureintro; exact Hlgnn
  iunfold mvcc.ownTree
  rw [mvcc.itemsOfEntries_btInsert]
  isplitl []
  · ipureintro; exact btInsert_sorted mvcc.kiItemLess_swo Hsorted
  iframe Ht
  have hperm : (btInsert mvcc.entryLess (ki, k, m) L).Perm ((ki, k, m) :: L) := by
    refine mvcc.btInsert_perm_of_new _ L (fun w hw => ?_)
    have hne : w.2.1 ≠ k := Hnew w hw
    by_cases h1 : go.GoStringLt w.2.1 k
    · exact Or.inl h1
    · by_cases h2 : go.GoStringLt k w.2.1
      · exact Or.inr h2
      · exact absurd (go.goStringLt_eq_of_not_lt h1 h2) hne
  iapply (BigSepL.bigSepL_perm (Φ := fun z => mvcc.ownEntry (GF := GF) z 1) hperm).2
  iapply BigSepL.bigSepL_cons.2
  iframe Hkis
  iunfold mvcc.ownEntry
  isplitl []
  · ipureintro; exact Hn
  iexists gs
  iexact Hki

end proof

end EtcdGrove
end Perennial
