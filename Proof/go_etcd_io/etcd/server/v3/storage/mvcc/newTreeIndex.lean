/-
Proof of `Spec/.../mvcc/newTreeIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__Less
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New
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

/-- Reader tokens of the index's lock are reader handles (with the tree's address). -/
theorem idxReaders_of_toks (ti t : Loc) (γ : mvcc.IdxNames) : ∀ (n : Nat),
    ti.[treeIndex, go!"tree"] ↦□ t ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.idxMuAddr ti) (mvcc.idxLockInv (GF := GF) t γ)) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.idxReader ti γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨#Ht, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iunfold mvcc.idxReader; iexists t; iframe H1; iexact Ht
    · iapply idxReaders_of_toks ti t γ n; iframe Hs; iexact Ht

theorem mvcc.newTreeIndex.wp_proof
    (wp_btree_New : btree.New.spec (GF := GF) (hG := hG))
    (hLess : mvcc.keyIndex.Less.spec (GF := GF) (hG := hG)) :
    mvcc.newTreeIndex.spec (GF := GF) (hG := hG) := by
  have wp_btree_New : btree.New.modelSpec (GF := GF) (hG := hG) := btree.New.modelSpec_of wp_btree_New
  intro lg
  wp_start as %Hlgnn
  wp_auto
  -- `btree.New(32, func(aki, bki) bool { return aki.Less(bki) })`
  wp_apply (wp_btree_New mvcc.kiPtrT (W64 32) _ mvcc.kiItemIs mvcc.kiItemLess) $$ [] as %t Ht
  · isplitr
    · ipureintro; constructor <;> word
    isplitr
    · ipureintro; exact mvcc.kiItemLess_swo
    unfold btLessSpec
    iintro %a %b %va %vb
    imodintro
    iintro %Φ' ⟨#Hva, #Hvb⟩ HΦ'
    iunfold mvcc.kiItemIs at Hva
    iunfold mvcc.kiItemIs at Hvb
    icases Hva with ⟨%Hpa, #Hka⟩
    icases Hvb with ⟨%Hpb, #Hkb⟩
    wp_auto
    wp_apply (hLess a b va.2 vb.2) $$ [$Hka $Hkb]
    rw [show decide (go.GoStringLt va.2 vb.2) = decide (mvcc.kiItemLess va vb) from rfl]
    iapply HΦ'
    itrivial
  wp_alloc ti as Hti
  iStructNamed Hti
  ipersist tree
  ipersist lg
  imod mono_list_own_alloc (GF := GF) ([] : List mvcc.HistItem) with ⟨%γh, Hhauth, #Hhlb⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γn, Hnauth, #Hnlb⟩
  let γ : mvcc.IdxNames := ⟨γh, γn⟩
  have hshape : mvcc.histShape [] [] = [] := rfl
  have hevs : (mvcc.evsOf ([] ++ [[]])).length = 0 := rfl
  have hwf : mvcc.IdxWf [] [] := by
    refine ⟨⟨fun _ => rfl, fun r cs i k hr hi => ?_⟩, by simp, by simp, fun _ h => by simp at h⟩
    simp only [List.nil_append, List.getElem?_singleton] at hr
    split at hr
    · simp only [Option.some.injEq] at hr; subst hr; simp at hi
    · simp at hr
  imod sync.init_RWMutex (mvcc.idxLockInv (hG := hG) t γ) (mvcc.idxMuAddr ti) $$ [Hnauth Ht] RWMutex
    with Htoks
  · inext
    unfold mvcc.idxLockInv
    iexists [], [], []
    simp only [named, γ]
    rw [hshape, hevs]
    iframe Hnauth
    isplitl []
    · iexact Hhlb
    isplitl [Ht]
    · iunfold mvcc.ownTree
      rw [show mvcc.itemsOfEntries [] = [] from rfl]
      iframe Ht
      isplitl []
      · ipureintro; exact List.Pairwise.nil
      iapply BigSepL.bigSepL_nil_intro; iempintro
    ipureintro
    exact ⟨rfl, hwf⟩
  wp_auto
  -- one token's guard
  have hpos : 0 < Int.toNat sync.rwmutex.actualMaxReaders :=
    Int.lt_toNat.2 (by simpa using sync.actualMaxReaders_pos)
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
  icases sync.ownRWMutex_guard _ _ $$ Htok with ⟨Htok, #Hguard⟩
  iapply HΦ
  iexists γ
  isplitl []
  · iunfold mvcc.isTreeIndex
    iexists t, lg
    simp only [named, γ]
    iframe #
    ipureintro; exact Hlgnn
  isplitl [Hhauth]
  · iunfold mvcc.idxWriter
    simp only [γ]
    rw [hshape, hevs]
    iframe Hhauth
    isplitl []
    · iexact Hnlb
    ipureintro; exact hwf
  rw [← List.replicate_succ]
  iapply idxReaders_of_toks ti t γ (m + 1)
  isplitl []
  · iexact tree
  rw [List.replicate_succ]
  iapply BigSepL.bigSepL_cons.2
  iframe Htok Htoks

end proof

end EtcdGrove
end Perennial
