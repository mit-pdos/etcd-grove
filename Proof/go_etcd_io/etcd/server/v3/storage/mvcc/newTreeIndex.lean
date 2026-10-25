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
theorem mvcc.newTreeIndex.wp_proof
    (wp_btree_New : btree.New.spec (GF := GF) (hG := hG))
    (hLess : mvcc.keyIndex.Less.spec (GF := GF) (hG := hG)) :
    mvcc.newTreeIndex.spec (GF := GF) (hG := hG) := by
  have wp_btree_New : btree.New.modelSpec (GF := GF) (hG := hG) := btree.New.modelSpec_of wp_btree_New
  intro γ lg n log₀
  wp_start as ⟨%Hlgnn, Hnauth, Hcmp, #Hclb, #Hllb⟩
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
  have hcmph := (ghostVar_fractional (GF := GF) γ.cmp ((-1 : Int), ([] : List Loc))).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hcmph
  icases hcmph.1 $$ Hcmp with ⟨Hcmp, Hcmpr⟩
  wp_auto
  iapply HΦ
  isplitl [RWMutex Ht]
  · iunfold mvcc.ownIdxPriv
    iexists t, lg
    iframe tree lg RWMutex
    isplitl []
    · ipureintro; exact Hlgnn
    iunfold mvcc.ownTree
    rw [show mvcc.itemsOfEntries [] = [] from rfl]
    iframe Ht
    isplitl []
    · ipureintro; exact List.Pairwise.nil
    iapply BigSepL.bigSepL_nil_intro; iempintro
  isplitl [Hnauth Hcmp]
  · iunfold mvcc.idxLockG
    iframe Hnauth
    isplitl []
    · iexact Hclb
    isplitl []
    · iexists log₀; iexact Hllb
    iunfold mvcc.idxCmpOwn
    iexists -1, []
    iframe Hcmp
    ipureintro; simp
  iunfold mvcc.idxCompactor; iexact Hcmpr

end proof

end EtcdGrove
end Perennial
