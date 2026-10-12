/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

The five sorters (`kvSortBy*`, around a `kvSort` of the result's slice) are `sort.Interface`s
over the list of the result's (pointer, key-value) pairs (`sorterR`), ordered by `kvLtBy` of
their target (`sorter_*`); `sort.Sort` (or `sort.Reverse` then `sort.Sort`) leaves a
permutation sorted by it (`pairwise_of_sorted`, `pairwise_of_sorted_rev`). The `default:`
branch (`lg.Panic`) is unreachable: the target is one of the five (`validSortTarget`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.sortRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsDefaultOrdering
public import Spec.sort.Sort
public import Spec.sort.Reverse
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort__Len
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort__Swap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByKey__Less
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByVersion__Less
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByCreate__Less
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByMod__Less
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSortByValue__Less

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- What a sorter over the slice `sl` holds: the pointers of `l`, their key-values (owned), with
non-negative revisions and versions. -/
def txn.sorterR (sl : GoSlice) (l : List (Loc × EtcdKv)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ txn.kvsAt l ∗ ⌜∀ x ∈ l, txn.kvOk x.2⌝)

theorem txn.sorter_key
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hLess : txn.kvSortByKey.Less.spec (GF := GF) (hG := hG)) (sp ks : Loc) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByKey, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ⊢
      sorterSpec (interface.mk (go.GoType.PointerType kvSortByKey.ty) #sp) (txn.sorterR sl)
        (fun a b => txn.kvLtBy (W64 0) a.2 b.2) := by
  iintro ⟨#Hpkg, #Hsp, #Hks⟩
  unfold sorterSpec txn.sorterR
  isplitr
  · imodintro
    iintro %l
    wp_start as ⟨Hs, Hk, %Hok⟩
    wp_auto
    wp_apply (hLen ks sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hks $Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hok
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sp ks sl l (DFrac.own 1) i j a b) $$ [$Hsp $Hks $Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro; exact ⟨hi, hj, ha, hb⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_method_call
  wp_call
  wp_auto
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) := slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap ks sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hks $Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  isplitl [Hk]
  · unfold txn.kvsAt
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun x => txn.kvAt x.1 x.2) hp).1
    iexact Hk
  ipureintro
  intro x hx
  exact Hok x (hp.symm.mem_iff.1 hx)

theorem txn.sorter_version
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hLess : txn.kvSortByVersion.Less.spec (GF := GF) (hG := hG)) (sp ks : Loc) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByVersion, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ⊢
      sorterSpec (interface.mk (go.GoType.PointerType kvSortByVersion.ty) #sp) (txn.sorterR sl)
        (fun a b => txn.kvLtBy (W64 1) a.2 b.2) := by
  iintro ⟨#Hpkg, #Hsp, #Hks⟩
  unfold sorterSpec txn.sorterR
  isplitr
  · imodintro
    iintro %l
    wp_start as ⟨Hs, Hk, %Hok⟩
    wp_auto
    wp_apply (hLen ks sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hks $Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hok
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sp ks sl l (DFrac.own 1) i j a b) $$ [$Hsp $Hks $Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro
      exact ⟨hi, hj, ha, hb, Hok a (List.mem_of_getElem? ha), Hok b (List.mem_of_getElem? hb)⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_method_call
  wp_call
  wp_auto
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) := slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap ks sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hks $Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  isplitl [Hk]
  · unfold txn.kvsAt
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun x => txn.kvAt x.1 x.2) hp).1
    iexact Hk
  ipureintro
  intro x hx
  exact Hok x (hp.symm.mem_iff.1 hx)

theorem txn.sorter_create
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hLess : txn.kvSortByCreate.Less.spec (GF := GF) (hG := hG)) (sp ks : Loc) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByCreate, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ⊢
      sorterSpec (interface.mk (go.GoType.PointerType kvSortByCreate.ty) #sp) (txn.sorterR sl)
        (fun a b => txn.kvLtBy (W64 2) a.2 b.2) := by
  iintro ⟨#Hpkg, #Hsp, #Hks⟩
  unfold sorterSpec txn.sorterR
  isplitr
  · imodintro
    iintro %l
    wp_start as ⟨Hs, Hk, %Hok⟩
    wp_auto
    wp_apply (hLen ks sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hks $Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hok
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sp ks sl l (DFrac.own 1) i j a b) $$ [$Hsp $Hks $Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro
      exact ⟨hi, hj, ha, hb, Hok a (List.mem_of_getElem? ha), Hok b (List.mem_of_getElem? hb)⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_method_call
  wp_call
  wp_auto
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) := slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap ks sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hks $Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  isplitl [Hk]
  · unfold txn.kvsAt
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun x => txn.kvAt x.1 x.2) hp).1
    iexact Hk
  ipureintro
  intro x hx
  exact Hok x (hp.symm.mem_iff.1 hx)

theorem txn.sorter_mod
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hLess : txn.kvSortByMod.Less.spec (GF := GF) (hG := hG)) (sp ks : Loc) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByMod, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ⊢
      sorterSpec (interface.mk (go.GoType.PointerType kvSortByMod.ty) #sp) (txn.sorterR sl)
        (fun a b => txn.kvLtBy (W64 3) a.2 b.2) := by
  iintro ⟨#Hpkg, #Hsp, #Hks⟩
  unfold sorterSpec txn.sorterR
  isplitr
  · imodintro
    iintro %l
    wp_start as ⟨Hs, Hk, %Hok⟩
    wp_auto
    wp_apply (hLen ks sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hks $Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hok
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sp ks sl l (DFrac.own 1) i j a b) $$ [$Hsp $Hks $Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro
      exact ⟨hi, hj, ha, hb, Hok a (List.mem_of_getElem? ha), Hok b (List.mem_of_getElem? hb)⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_method_call
  wp_call
  wp_auto
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) := slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap ks sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hks $Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  isplitl [Hk]
  · unfold txn.kvsAt
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun x => txn.kvAt x.1 x.2) hp).1
    iexact Hk
  ipureintro
  intro x hx
  exact Hok x (hp.symm.mem_iff.1 hx)

theorem txn.sorter_value
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hLess : txn.kvSortByValue.Less.spec (GF := GF) (hG := hG)) (sp ks : Loc) (sl : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      sp.[kvSortByValue, go!"kvSort"] ↦□ ks ∗ ks.[kvSort, go!"kvs"] ↦□ sl ⊢
      sorterSpec (interface.mk (go.GoType.PointerType kvSortByValue.ty) #sp) (txn.sorterR sl)
        (fun a b => txn.kvLtBy (W64 4) a.2 b.2) := by
  iintro ⟨#Hpkg, #Hsp, #Hks⟩
  unfold sorterSpec txn.sorterR
  isplitr
  · imodintro
    iintro %l
    wp_start as ⟨Hs, Hk, %Hok⟩
    wp_auto
    wp_apply (hLen ks sl (l.map Prod.fst) (DFrac.own 1)) $$ [$Hks $Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
    ipureintro; exact Hok
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    wp_apply (hLess sp ks sl l (DFrac.own 1) i j a b) $$ [$Hsp $Hks $Hs $Hk] as ⟨Hs, Hk⟩
    · ipureintro; exact ⟨hi, hj, ha, hb⟩
    iapply HΦ
    iframe
    ipureintro; exact Hok
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ ⟨Hs, Hk, %Hok⟩ HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  wp_method_call
  wp_call
  wp_auto
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) := slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
  wp_apply (hSwap ks sl (l.map Prod.fst) i j a.1 b.1) $$ [$Hks $Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb]; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  isplitl [Hk]
  · unfold txn.kvsAt
    iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun x => txn.kvAt x.1 x.2) hp).1
    iexact Hk
  ipureintro
  intro x hx
  exact Hok x (hp.symm.mem_iff.1 hx)

theorem txn.w32_of_sint (x : w32) (k : Int) (h0 : -2 ^ 31 ≤ k) (h1 : k < 2 ^ 31)
    (h : sint.Z x = k) : x = W32 k := by
  apply BitVec.eq_of_toInt_eq
  have : sint.Z (W32 k) = k := by word
  unfold sint.Z at h this
  rw [h, this]

/-- A valid sort target is one of the five. -/
theorem txn.target_cases (o : OpFull) (target : w32) (h : txn.validSortTarget o)
    (ho : o.sortTarget = W64 (sint.Z target)) :
    target = W32 0 ∨ target = W32 1 ∨ target = W32 2 ∨ target = W32 3 ∨ target = W32 4 := by
  unfold txn.validSortTarget at h
  rw [ho] at h
  have e : sint.Z (W64 (sint.Z target)) = sint.Z target := by word
  rw [e] at h
  have : sint.Z target = 0 ∨ sint.Z target = 1 ∨ sint.Z target = 2 ∨ sint.Z target = 3 ∨
      sint.Z target = 4 := by omega
  rcases this with h | h | h | h | h
  · exact Or.inl (txn.w32_of_sint _ _ (by omega) (by omega) h)
  · exact Or.inr (Or.inl (txn.w32_of_sint _ _ (by omega) (by omega) h))
  · exact Or.inr (Or.inr (Or.inl (txn.w32_of_sint _ _ (by omega) (by omega) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (txn.w32_of_sint _ _ (by omega) (by omega) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (txn.w32_of_sint _ _ (by omega) (by omega) h))))

/-- The server's adjusted order (`sortOrder`: ascending for a target other than the key with no
order) against the client model's `effSortOrder`: the server sorts (off its default ordering)
exactly when `effSortOrder` is not `0`, and then it is the adjusted order. -/
theorem txn.effSortOrder_srv (k re : GoString) (rev limit : w64) (order target : w32)
    (ser ko co : Bool) (minM maxM minC maxC : w64) :
    (txn.rangeOpOf k re rev limit order target ser ko co minM maxM minC maxC).effSortOrder =
      (let so := if target ≠ W32 0 ∧ order = W32 0 then W32 1 else order
       if so = W32 0 ∨ (target = W32 0 ∧ so = W32 1) then W64 0 else W64 (sint.Z so)) := by
  simp only [OpFull.effSortOrder, txn.rangeOpOf]
  simp only [sext32_eq order 0 (by omega) (by omega), sext32_eq target 0 (by omega) (by omega),
    sext32_eq order 1 (by omega) (by omega)]
  have hz : (W64 (sint.Z target) = 0#64) ↔ target = 0#32 := sext32_eq target 0 (by omega) (by omega)
  by_cases ho : order = 0#32 <;> by_cases ht : target = 0#32 <;>
    simp [ho, ht, hz] <;> rfl

theorem txn.swo_flip {E : Type} {R : E → E → Prop} (h : slices.StrictWeakOrder R) :
    slices.StrictWeakOrder (fun a b => R b a) where
  strict_weak_order_irrefl x := h.strict_weak_order_irrefl x
  strict_weak_order_trans _ _ _ h1 h2 := h.strict_weak_order_trans _ _ _ h2 h1
  strict_weak_order_equiv := {
    refl := fun x => ⟨h.strict_weak_order_irrefl x, h.strict_weak_order_irrefl x⟩
    symm := fun hh => ⟨hh.2, hh.1⟩
    trans := fun h1 h2 =>
      let r := h.strict_weak_order_equiv.trans ⟨h1.2, h1.1⟩ ⟨h2.2, h2.1⟩
      ⟨r.2, r.1⟩ }

theorem txn.sortRangeResults.wp_proof
    (hIsDef : txn.IsDefaultOrdering.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hRev : sort.Reverse.spec (GF := GF) (hG := hG))
    (hLen : txn.kvSort.Len.spec (GF := GF) (hG := hG))
    (hSwap : txn.kvSort.Swap.spec (GF := GF) (hG := hG))
    (hKey : txn.kvSortByKey.Less.spec (GF := GF) (hG := hG))
    (hVer : txn.kvSortByVersion.Less.spec (GF := GF) (hG := hG))
    (hCre : txn.kvSortByCreate.Less.spec (GF := GF) (hG := hG))
    (hMod : txn.kvSortByMod.Less.spec (GF := GF) (hG := hG))
    (hVal : txn.kvSortByValue.Less.spec (GF := GF) (hG := hG)) :
    txn.sortRangeResults.spec (GF := GF) (hG := hG) := by
  intro rr r lg o rev count vs
  wp_start as ⟨Hrr, #Hr, %Hvalid, %Hprem⟩
  ihave #Hr2 := Hr
  iunfold txn.rangeRequestIs at Hr2
  icases Hr2 with ⟨%Hnn, %ksl, %esl, %k, %e, %rv, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  iunfold txn.rangeResultIs at Hrr
  icases Hrr with ⟨%sl, %l, %Hl, Hrr, Hsl⟩
  iunfold txn.kvsOwnAt at Hsl
  icases Hsl with ⟨Hs, Hkv⟩
  wp_auto
  wp_join iprop(∃ so : w32, sortOrder_ptr ↦ so ∗
      ⌜so = if target ≠ W32 0 ∧ order = W32 0 then W32 1 else order⌝) with [sortOrder]
    as ⟨%so, sortOrder, %Hso⟩
  · iexists order; iframe; ipureintro; simp
  · wp_if_destruct
    · simp only [etcdserverpb.RangeRequest_ASCEND]
      wp_auto
      isplitl []
      · ipureintro; trivial
      iexists (W32 1); iframe; ipureintro; exact (ite_eq_left ⟨Hif, trivial⟩).symm
    · isplitl []
      · ipureintro; trivial
      iexists order; iframe; ipureintro; exact (ite_eq_right (fun h => Hif h.2)).symm
  wp_apply hIsDef
  have Heff : o.effSortOrder =
      if so = W32 0 ∨ (target = W32 0 ∧ so = W32 1) then W64 0 else W64 (sint.Z so) := by
    rw [Ho, txn.effSortOrder_srv, Hso]
  have Htgt : o.sortTarget = W64 (sint.Z target) := by rw [Ho]; rfl
  wp_if_destruct
  rotate_left
  · ipersist rr
    ipersist r
    wp_join iprop(∃ (x : GoInterfaceOk) (t : w64), sorter_ptr ↦ GoInterface.ok x ∗
        sorterSpec x (txn.sorterR sl) (fun a b => txn.kvLtBy t a.2 b.2) ∗ ⌜t = o.sortTarget⌝ ∗
        rr ↦ ({ KVs' := sl, Rev' := rev, Count' := count } : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult))
      with [sorter Hrr] as ⟨%x, %t, sorter, #Hx, %Ht, Hrr⟩
    · iStructNamed «$v0»
      ipersist kvs
      wp_bind (GoAlloc kvSortByKey.ty _)
      wp_alloc sp as Hsp
      iStructNamed Hsp
      ipersist kvSort
      wp_auto
      isplitl []
      · ipureintro; trivial
      iexists (interface.mk (go.GoType.PointerType kvSortByKey.ty) #sp), (W64 0)
      iframe sorter Hrr
      isplitl []
      · iapply (txn.sorter_key hLen hSwap hKey sp «$v0_ptr» sl)
        iframe Hpkg kvSort kvs
      ipureintro
      rw [Htgt, of_decide_eq_true Hif.symm]; rfl
    · wp_if_destruct
      · iStructNamed «$v0»
        ipersist kvs
        wp_bind (GoAlloc kvSortByVersion.ty _)
        wp_alloc sp as Hsp
        iStructNamed Hsp
        ipersist kvSort
        wp_auto
        isplitl []
        · ipureintro; trivial
        iexists (interface.mk (go.GoType.PointerType kvSortByVersion.ty) #sp), (W64 1)
        iframe sorter Hrr
        isplitl []
        · iapply (txn.sorter_version hLen hSwap hVer sp «$v0_ptr» sl)
          iframe Hpkg kvSort kvs
        ipureintro
        rw [Htgt, of_decide_eq_true Hif.symm]; rfl
      · wp_if_destruct
        · iStructNamed «$v0»
          ipersist kvs
          wp_bind (GoAlloc kvSortByCreate.ty _)
          wp_alloc sp as Hsp
          iStructNamed Hsp
          ipersist kvSort
          wp_auto
          isplitl []
          · ipureintro; trivial
          iexists (interface.mk (go.GoType.PointerType kvSortByCreate.ty) #sp), (W64 2)
          iframe sorter Hrr
          isplitl []
          · iapply (txn.sorter_create hLen hSwap hCre sp «$v0_ptr» sl)
            iframe Hpkg kvSort kvs
          ipureintro
          rw [Htgt, of_decide_eq_true Hif.symm]; rfl
        · wp_if_destruct
          · iStructNamed «$v0»
            ipersist kvs
            wp_bind (GoAlloc kvSortByMod.ty _)
            wp_alloc sp as Hsp
            iStructNamed Hsp
            ipersist kvSort
            wp_auto
            isplitl []
            · ipureintro; trivial
            iexists (interface.mk (go.GoType.PointerType kvSortByMod.ty) #sp), (W64 3)
            iframe sorter Hrr
            isplitl []
            · iapply (txn.sorter_mod hLen hSwap hMod sp «$v0_ptr» sl)
              iframe Hpkg kvSort kvs
            ipureintro
            rw [Htgt, of_decide_eq_true Hif.symm]; rfl
          · wp_if_destruct
            · iStructNamed «$v0»
              ipersist kvs
              wp_bind (GoAlloc kvSortByValue.ty _)
              wp_alloc sp as Hsp
              iStructNamed Hsp
              ipersist kvSort
              wp_auto
              isplitl []
              · ipureintro; trivial
              iexists (interface.mk (go.GoType.PointerType kvSortByValue.ty) #sp), (W64 4)
              iframe sorter Hrr
              isplitl []
              · iapply (txn.sorter_value hLen hSwap hVal sp «$v0_ptr» sl)
                iframe Hpkg kvSort kvs
              ipureintro
              rw [Htgt, of_decide_eq_true Hif.symm]; rfl
            · exfalso
              rcases txn.target_cases o target Hvalid Htgt with h | h | h | h | h <;> simp_all

    -- the sort
    have Hsorts : ¬(so = W32 0 ∨ target = W32 0 ∧ so = W32 1) := by assumption
    have Heffs : o.effSortOrder = W64 (sint.Z so) := by rw [Heff, ite_eq_right Hsorts]
    have Hpre : (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) →
        l.length ≤ 2 ^ 62 ∧ ∀ y ∈ l, txn.kvOk y.2 := by
      intro h
      obtain ⟨h1, h2⟩ := Hprem h
      subst Hl
      exact ⟨by simpa using h1, fun y hy => h2 y.2 (List.mem_map_of_mem hy)⟩
    subst Ht
    wp_if_destruct
    · have hso1 : so = W32 1 := of_decide_eq_true Hif.symm
      have heff1 : o.effSortOrder = W64 1 := by rw [Heffs, hso1]; rfl
      obtain ⟨hlen, hok⟩ := Hpre (Or.inl heff1)
      wp_apply (hSort (Loc × EtcdKv) x (txn.sorterR sl) (fun a b => txn.kvLtBy o.sortTarget a.2 b.2) l
          (txn.kvLtBy_swo o.sortTarget Prod.snd)) $$ [Hs Hkv]
        as %l' ⟨HR, %Hl'⟩
      · iframe Hx; unfold txn.sorterR; iframe; ipureintro; exact ⟨hok, hlen⟩
      unfold txn.sorterR
      icases HR with ⟨Hs, Hkv, -⟩
      iapply HΦ
      iexists l'.map Prod.snd
      isplitl
      · iunfold txn.rangeResultIs
        iexists sl, l'
        isplitr
        · ipureintro; rfl
        iframe Hrr
        iunfold txn.kvsOwnAt
        iframe
      ipureintro
      refine ⟨?_, fun _ => txn.pairwise_of_sorted Prod.snd o.sortTarget l' Hl'.2, ?_, ?_⟩
      · rw [← Hl]; exact (Hl'.1.map Prod.snd).symm
      · intro h; rw [heff1] at h; cases h
      · intro h; exact absurd heff1 h
    · wp_if_destruct
      · have hso2 : so = W32 2 := by simpa using Hif
        have heff2 : o.effSortOrder = W64 2 := by rw [Heffs, hso2]; rfl
        obtain ⟨hlen, hok⟩ := Hpre (Or.inr heff2)
        wp_apply (hRev (Loc × EtcdKv) x (txn.sorterR sl) (fun a b => txn.kvLtBy o.sortTarget a.2 b.2))
          $$ [$Hx] as %y #Hy
        wp_apply (hSort (Loc × EtcdKv) y (txn.sorterR sl) (fun a b => txn.kvLtBy o.sortTarget b.2 a.2) l
            (txn.swo_flip (txn.kvLtBy_swo o.sortTarget Prod.snd))) $$ [Hs Hkv]
          as %l' ⟨HR, %Hl'⟩
        · iframe Hy; unfold txn.sorterR; iframe; ipureintro; exact ⟨hok, hlen⟩
        unfold txn.sorterR
        icases HR with ⟨Hs, Hkv, -⟩
        iapply HΦ
        iexists l'.map Prod.snd
        isplitl
        · iunfold txn.rangeResultIs
          iexists sl, l'
          isplitr
          · ipureintro; rfl
          iframe Hrr
          iunfold txn.kvsOwnAt
          iframe
        ipureintro
        refine ⟨?_, ?_, fun _ => txn.pairwise_of_sorted_rev Prod.snd o.sortTarget l' Hl'.2, ?_⟩
        · rw [← Hl]; exact (Hl'.1.map Prod.snd).symm
        · intro h; rw [heff2] at h; cases h
        · intro _ h; exact absurd heff2 h
      · rename_i Hn1
        have hn1 : so ≠ W32 1 := fun h => Hn1 (by simp [h])
        have hn2 : so ≠ W32 2 := fun h => Hif (by simp [h])
        have he1 : o.effSortOrder ≠ W64 1 := by
          rw [Heffs]; exact fun h => hn1 ((sext32_eq so 1 (by omega) (by omega)).1 h)
        have he2 : o.effSortOrder ≠ W64 2 := by
          rw [Heffs]; exact fun h => hn2 ((sext32_eq so 2 (by omega) (by omega)).1 h)
        iapply HΦ
        iexists vs
        isplitl
        · iunfold txn.rangeResultIs
          iexists sl, l
          isplitr
          · ipureintro; exact Hl
          iframe Hrr
          iunfold txn.kvsOwnAt
          iframe
        ipureintro
        exact ⟨List.Perm.refl _, fun h => absurd h he1, fun h => absurd h he2, fun _ _ => rfl⟩
  · have Heff0 : o.effSortOrder = W64 0 := by rw [Heff, ite_eq_left Hif]
    iapply HΦ
    iexists vs
    isplitl
    · iunfold txn.rangeResultIs
      iexists sl, l
      isplitr
      · ipureintro; exact Hl
      iframe Hrr
      iunfold txn.kvsOwnAt
      iframe
    ipureintro
    refine ⟨List.Perm.refl _, ?_, ?_, fun _ _ => rfl⟩
    · intro h; rw [Heff0] at h; cases h
    · intro h; rw [Heff0] at h; cases h

end proof

end EtcdGrove
end Perennial
