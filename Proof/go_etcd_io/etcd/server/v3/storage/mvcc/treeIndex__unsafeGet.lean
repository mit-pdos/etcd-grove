/-
Proof of `Spec/.../mvcc/treeIndex__unsafeGet.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeGet
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__keyIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__get
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.treeIndex.unsafeGet.wp_proof
    (hKeyIndex : mvcc.treeIndex.keyIndex.spec (GF := GF) (hG := hG))
    (hGet : mvcc.keyIndex.get.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.unsafeGet.spec (GF := GF) (hG := hG) := by
  intro ti t lg L q key k atRev e
  wp_start as ⟨#Htree, #Hlg, Htr, %Hne, #Hkey, #Herr⟩
  wp_auto
  iStructNamedPrefix «$r0» "K"
  ipersist Kkey
  wp_apply (hKeyIndex ti t L q «$r0_ptr» k) $$ [$Htr] as %p ⟨Htr, %Hp⟩
  · iframe Htree
    iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  iunfold mvcc.ownTree at Htr
  icases Htr with ⟨%Hsorted, Ht, Hkis⟩
  have Hidx := mvcc.idxGet_entries L Hsorted k
  cases hf : L.find? (fun z => decide (z.2.1 = k)) with
  | none =>
    rw [hf] at Hp Hidx
    simp only [Option.map_none, Option.getD_none] at Hp Hidx
    subst Hp
    wp_auto
    have h : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) atRev
        (GoInterface.ok e) =
        PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e) := by
      rw [Hidx]; rfl
    rw [← h]
    iapply HΦ
    iframe #
    iunfold mvcc.ownTree
    iframe Ht Hkis
    ipureintro; exact Hsorted
  | some z =>
    rw [hf] at Hp Hidx
    simp only [Option.map_some, Option.getD_some] at Hp Hidx
    subst Hp
    obtain ⟨i, hi, hk⟩ := mvcc.find?_entry_getElem? L k z hf
    icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z q) hi |>.1 $$ Hkis
      with ⟨Hz, Hback⟩
    iunfold mvcc.ownEntry at Hz
    icases Hz with ⟨%Hn, %gs, Hki⟩
    wp_if_destruct
    · exact absurd Hif Hn
    wp_apply (hGet z.1 gs z.2.2 (DFrac.own q) lg atRev e) $$ [$Hki $Herr] as Hki
    · ipureintro; exact Hne z (List.mem_of_getElem? hi)
    cases hg : mvcc.kiGet z.2.2 atRev with
    | none =>
      rw [show mvcc.kiGetVal z.2.2 atRev (GoInterface.ok e) =
        PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e)
        from by simp only [mvcc.kiGetVal, hg]]
      wp_auto
      have h : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) atRev
          (GoInterface.ok e) =
          PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e) := by
        rw [Hidx]; simp only [Option.getD_some, mvcc.kiGetVal, hg]
      rw [← h]
      iapply HΦ
      iframe #
      iunfold mvcc.ownTree
      isplitl []
      · ipureintro; exact Hsorted
      iframe Ht
      ispecialize Hback $$ %z
      have hset : L.set i z = L := by
        obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 hi
        rw [← e]; exact List.set_getElem_self h
      have hset' : ([∗list] z' ∈ L.set i z, mvcc.ownEntry (GF := GF) z' q) =
          ([∗list] z' ∈ L, mvcc.ownEntry (GF := GF) z' q) := by rw [hset]
      rw [← hset']
      iapply Hback
      iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hn
      iexists gs; iexact Hki

    | some r =>
      obtain ⟨m, c, v⟩ := r
      rw [show mvcc.kiGetVal z.2.2 atRev (GoInterface.ok e) =
        PairV (PairV (PairV #(mvcc.revVal m) #(mvcc.revVal c)) #v) #GoInterface.nil
        from by simp only [mvcc.kiGetVal, hg]]
      wp_auto
      have h : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) atRev
          (GoInterface.ok e) =
          PairV (PairV (PairV #(mvcc.revVal m) #(mvcc.revVal c)) #v) #GoInterface.nil := by
        rw [Hidx]; simp only [Option.getD_some, mvcc.kiGetVal, hg]
      rw [← h]
      iapply HΦ
      iframe #
      iunfold mvcc.ownTree
      isplitl []
      · ipureintro; exact Hsorted
      iframe Ht
      ispecialize Hback $$ %z
      have hset : L.set i z = L := by
        obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 hi
        rw [← e]; exact List.set_getElem_self h
      have hset' : ([∗list] z' ∈ L.set i z, mvcc.ownEntry (GF := GF) z' q) =
          ([∗list] z' ∈ L, mvcc.ownEntry (GF := GF) z' q) := by rw [hset]
      rw [← hset']
      iapply Hback
      iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hn
      iexists gs; iexact Hki


end proof

end EtcdGrove
end Perennial
