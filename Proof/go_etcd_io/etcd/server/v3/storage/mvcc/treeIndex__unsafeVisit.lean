/-
Proof of `Spec/.../mvcc/treeIndex__unsafeVisit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeVisit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__Less
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__AscendGreaterOrEqual
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

theorem mvcc.treeIndex.unsafeVisit.wp_proof
    (wp_Asc : btree.BTree.AscendGreaterOrEqual.spec (GF := GF) (hG := hG))
    (hLess : mvcc.keyIndex.Less.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.unsafeVisit.spec (GF := GF) (hG := hG) := by
  have wp_Asc : btree.BTree.AscendGreaterOrEqual.modelSpec (GF := GF) (hG := hG) :=
    btree.BTree.AscendGreaterOrEqual.modelSpec_of wp_Asc
  intro ti t L q key endk k e f P Q
  wp_start as ⟨#Htree, Htr, #Hkey, #Hend, HP, #Hf⟩
  iunfold mvcc.visitSpec at Hf
  iunfold mvcc.ownTree at Htr
  icases Htr with ⟨%Hsorted, Ht, Hkis⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hend
  wp_auto
  ipersist endi
  iStructNamedPrefix «$r0» "K"
  iStructNamedPrefix «$r1» "E"
  ipersist Kkey
  ipersist Ekey
  ihave #Hitem : mvcc.kiItemIs (GF := GF) «$r0_ptr» («$r0_ptr», k) $$ []
  · iunfold mvcc.kiItemIs
    isplitl []
    · ipureintro; rfl
    iunfold mvcc.kiKey
    iexists key
    iframe #
  ihave #Hendkey : mvcc.kiKey (GF := GF) «$r1_ptr» e $$ []
  · iunfold mvcc.kiKey
    iexists endk
    iframe #
  have hGs : (mvcc.fromKey L k).Pairwise mvcc.entryLess :=
    mvcc.fromKey_sorted ((mvcc.itemsOfEntries_sorted_iff L).1 Hsorted) k
  have hvis : mvcc.rangeEntries L k e = (mvcc.fromKey L k).takeWhile (mvcc.belowEnd e) := by
    rw [mvcc.rangeEntries_eq, mvcc.filter_belowEnd_eq_takeWhile e _ hGs]
  have hG := mvcc.btAscendGe_entries L «$r0_ptr» k
  wp_apply (wp_Asc mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess _ (DFrac.own q) «$r0_ptr» («$r0_ptr», k) _
    (fun i => iprop(⌜i ≤ (mvcc.fromKey L k).length ∧
        ∀ j (h : j < (mvcc.fromKey L k).length), j < i → mvcc.belowEnd e (mvcc.fromKey L k)[j] = true⌝ ∗
      P i ∗ f_ptr ↦ f ∗ [∗list] z ∈ L, mvcc.ownEntry z q))
    iprop((Q ∨ P (mvcc.rangeEntries L k e).length) ∗ f_ptr ↦ f ∗ [∗list] z ∈ L, mvcc.ownEntry z q))
    $$ [$Ht $Hitem HP f Hkis] as ⟨Ht, Hpost⟩
  · isplitr
    · ipureintro; exact mvcc.kiItemLess_swo
    isplitl [HP f Hkis]
    · iframe HP f Hkis
      ipureintro
      exact ⟨Nat.zero_le _, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    unfold btIterSpec
    iintro %i %p %v %Hv
    wp_start_folded as ⟨⟨%Hi, HP, Hfp, Hkis⟩, #Hitv⟩
    rw [hG] at Hv
    unfold mvcc.itemsOfEntries at Hv
    rw [List.getElem?_map] at Hv
    cases hz : (mvcc.fromKey L k)[i]? with
    | none => rw [hz] at Hv; simp at Hv
    | some z =>
    rw [hz] at Hv
    simp only [Option.map_some, Option.some.injEq] at Hv
    subst Hv
    iunfold mvcc.kiItemIs at Hitv
    icases Hitv with ⟨%Hpz, #Hkz⟩
    subst Hpz
    have hi : i < (mvcc.fromKey L k).length := (List.getElem?_eq_some_iff.1 hz).1
    have hzG : (mvcc.fromKey L k)[i] = z := (List.getElem?_eq_some_iff.1 hz).2
    have hzL : z ∈ L := (mvcc.fromKey_sublist L k).subset (List.mem_of_getElem? hz)
    ihave #Hkz' : mvcc.kiKey (GF := GF) z.1 z.2.1 $$ []
    · iexact Hkz
    -- the visitor's call, once `z` is in range (`belowEnd e z`)
    have hgo : ∀ (hb : mvcc.belowEnd e z = true), (mvcc.rangeEntries L k e)[i]? = some z := by
      intro hb
      rw [hvis, mvcc.takeWhile_getElem? _ _ i]
      · exact hz
      · intro j hj hji
        rcases Nat.lt_or_eq_of_le hji with hlt | rfl
        · exact Hi.2 j hj hlt
        · rw [hzG]; exact hb
    wp_auto
    wp_if_destruct
    · -- `len(end) > 0`: compare with `end`
      wp_apply (hLess z.1 «$r1_ptr» z.2.1 e) $$ [$Hkz' $Hendkey]
      (try wp_auto)
      wp_if_destruct
      · have hb : mvcc.belowEnd e z = true := by
          unfold mvcc.belowEnd
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr Hif
        ihave #Hfi := Hf $$ %i %z %(hgo hb)
        icases BigSepL.bigSepL_mem_acc hzL $$ Hkis with ⟨Hz, Hback⟩
        wp_apply Hfi $$ [HP Hz] with %cont ⟨Hz, Hc⟩
        · iframe HP Hz
          iunfold mvcc.kiItemIs
          isplitl []
          · ipureintro; rfl
          iexact Hkz'
        ihave Hkis := Hback $$ Hz
        cases cont
        · wp_auto
          iapply HΦ
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hfp Hkis
          ileft
          iexact Hc
        · wp_auto
          iapply HΦ
          simp only [↓reduceIte]
          iframe Hfp Hkis Hc
          ipureintro
          refine ⟨hi, fun j hj hji => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt | rfl
          · exact Hi.2 j hj hlt
          · rw [hzG]; exact hb
      · -- `!item.Less(endi)`: stop, having visited `[0, i)`
        have hne : e ≠ [] := by
          intro he; subst he; simp at Hlen; word
        have hb : mvcc.belowEnd e z = false := by
          unfold mvcc.belowEnd
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
          exact ⟨hne, Hif⟩
        have hvisi : (mvcc.rangeEntries L k e).length = i := by
          rw [hvis, mvcc.takeWhile_eq_take _ _ i Hi.2 Hi.1 (Or.inr ⟨hi, by rw [hzG]; exact hb⟩)]
          exact List.length_take_of_le Hi.1
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hfp Hkis
        iright
        rw [hvisi]
        iexact HP
    · -- `len(end) == 0`: no upper bound
      have he : e = [] := by
        cases e with
        | nil => rfl
        | cons c cs => exfalso; simp at Hlen; word
      have hb : mvcc.belowEnd e z = true := by
        unfold mvcc.belowEnd; rw [he]; simp
      ihave #Hfi := Hf $$ %i %z %(hgo hb)
      icases BigSepL.bigSepL_mem_acc hzL $$ Hkis with ⟨Hz, Hback⟩
      wp_apply Hfi $$ [HP Hz] with %cont ⟨Hz, Hc⟩
      · iframe HP Hz
        iunfold mvcc.kiItemIs
        isplitl []
        · ipureintro; rfl
        iexact Hkz'
      ihave Hkis := Hback $$ Hz
      cases cont
      · wp_auto
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hfp Hkis
        ileft
        iexact Hc
      · wp_auto
        iapply HΦ
        simp only [↓reduceIte]
        iframe Hfp Hkis Hc
        ipureintro
        refine ⟨hi, fun j hj hji => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hji) with hlt | rfl
        · exact Hi.2 j hj hlt
        · rw [hzG]; exact hb
  -- after the iteration
  have hGlen : (btAscendGe mvcc.kiItemLess («$r0_ptr», k) (mvcc.itemsOfEntries L)).length =
      (mvcc.fromKey L k).length := by
    rw [hG]; unfold mvcc.itemsOfEntries; exact List.length_map _
  rw [hGlen]
  icases Hpost with (⟨Hq, Hfp, Hkis⟩ | ⟨%Hall, HP, Hfp, Hkis⟩)
  · iapply HΦ
    iunfold mvcc.ownTree
    iframe Ht Hkis
    isplitl []
    · ipureintro; exact Hsorted
    iexact Hq
  · iapply HΦ
    iunfold mvcc.ownTree
    iframe Ht Hkis
    isplitl []
    · ipureintro; exact Hsorted
    iright
    have hvisi : (mvcc.rangeEntries L k e).length = (mvcc.fromKey L k).length := by
      rw [hvis, mvcc.takeWhile_eq_take _ _ _ Hall.2 (Nat.le_refl _) (Or.inl rfl), List.take_length]
    rw [hvisi]
    iexact HP

end proof

end EtcdGrove
end Perennial
