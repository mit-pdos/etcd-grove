/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Clone
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Ascend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete
public import Spec.go_uber_org.zap.Logger__Panic
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactMaps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BtreeAscend

@[expose] public section

set_option linter.unusedVariables false
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

/-- A pointer of the entries other than the `j`-th's is one of the entries without it. -/
theorem mvcc.ptrs_eraseIdx (L : List mvcc.IdxEntry) (j : Nat) (z : mvcc.IdxEntry) (hj : L[j]? = some z)
    (p : Loc) (hp : p ∈ L.map Prod.fst) (hne : p ≠ z.1) : p ∈ (L.eraseIdx j).map Prod.fst := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw
  have hkj : k ≠ j := by
    intro e; subst e
    exact hne (by rw [(List.getElem?_eq_some_iff.1 hj).2])
  apply List.mem_map_of_mem
  rw [List.mem_iff_getElem]
  by_cases hlt : k < j
  · refine ⟨k, by rw [List.length_eraseIdx]; split <;> omega, ?_⟩
    rw [List.getElem_eraseIdx_of_lt _ hlt]
  · have hjl := (List.getElem?_eq_some_iff.1 hj).1
    refine ⟨k - 1, by rw [List.length_eraseIdx]; split <;> omega, ?_⟩
    rw [List.getElem_eraseIdx_of_ge _ (by omega)]
    congr 1; omega

/-- With distinct pointers, the `i`-th entry's is not among the later ones. -/
theorem mvcc.nodup_drop_ne (L : List mvcc.IdxEntry) (hnd : (L.map Prod.fst).Nodup) (i : Nat)
    (z : mvcc.IdxEntry) (hz : L[i]? = some z) (p : Loc) (hp : p ∈ (L.drop (i + 1)).map Prod.fst) :
    p ≠ z.1 := by
  have hpw : L.Pairwise (fun a b => a.1 ≠ b.1) := by
    have := hnd; unfold List.Nodup at this; rwa [List.pairwise_map] at this
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
  obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.1 hw
  rw [List.length_drop] at hk
  have hil := (List.getElem?_eq_some_iff.1 hz)
  have := List.pairwise_iff_getElem.1 hpw i (i + 1 + k) hil.1 (by omega) (by omega)
  rw [hil.2] at this
  rw [← hkw, List.getElem_drop]
  have e : i + 1 + k = i + 1 + k := rfl
  intro h
  apply this
  rw [h]

theorem mvcc.treeIndex.Compact.wp_proof
    (h0 : zap.Int64.spec (GF := GF) (hG := hG))
    (h1 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h2 : btree.BTree.Clone.spec (GF := GF) (hG := hG))
    (h3 : btree.BTree.Ascend.spec (GF := GF) (hG := hG))
    (h4 : mvcc.keyIndex.compact.spec (GF := GF) (hG := hG))
    (h5 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h6 : btree.BTree.Delete.spec (GF := GF) (hG := hG))
    (h7 : zap.Logger.Panic.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG) := by
  have h3 : btree.BTree.Ascend.modelSpec (GF := GF) (hG := hG) := btree.BTree.Ascend.modelSpec_of h3
  have h2 : btree.BTree.Clone.modelSpec (GF := GF) (hG := hG) := btree.BTree.Clone.modelSpec_of h2
  have h6 : btree.BTree.Delete.modelSpec (GF := GF) (hG := hG) := btree.BTree.Delete.modelSpec_of h6
  intro ti γ rev log c
  wp_start as ⟨#Hti, #Hlb, #Hcert, Hcmp, %Hc⟩
  obtain ⟨Hcr, Hr0, Hrl⟩ := Hc
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  wp_auto
  wp_apply (wp_map_make1 (K := Revision) (V := Unit)) as %m Hm
  (try wp_auto)
  wp_apply h0 _ _ as %f1 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply h1 lg _ _ $$ []
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- `ti.Lock()`: the promoted method, through the guard
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
  wp_auto_lc 1
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog0, %pend0, %L0, %cmax0, HP⟩
  iNamedSuffix HP "0"
  -- the compactor's state: the last compaction `c`, nothing pending; now `rev`, the clone pending
  iunfold mvcc.idxCmpOwn at Hcmp0
  icases Hcmp0 with ⟨%cc, %P, Hg0, %Hcc⟩
  iunfold mvcc.idxCompactor at Hcmp
  ihave %Hag := ghostVar_agree γ.cmp _ _ _ _ $$ Hg0 Hcmp
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  imod ghostVar_update_halves (sint.Z rev, L0.map Prod.fst) γ.cmp _ _ $$ Hg0 Hcmp with ⟨Hg0, Hcmp⟩
  have Hrz : sint.Z rev < 2 ^ 63 := by word
  have HcmR : cmax0 ≤ sint.Z rev := by have := Hcc.1; omega
  have Hb0 := Hwf0.logB
  -- what the clone has: every key with a revision compaction at `rev` keeps
  ihave Hkn : mvcc.idxKnows γ (.cert log) $$ []
  · rw [mvcc.idxKnows_cert]; iexact Hcert
  icases mvcc.idxKnows_facts γ (.cert log) log rfl ilog0 pend0 1 $$ Hkn Hhist0 Hnev0
    with ⟨%Hf0, -, Hnev0⟩
  obtain ⟨Hcmp0, Hcnt0, Hlwf, Hllen, Hlcs⟩ := Hf0
  have HbLog : mvcc.LogB log := ⟨Hllen, Hlcs⟩
  have Hkeys : ∀ r, mvcc.keepAt log (sint.Z rev) r →
      ∃ z ∈ L0, mvcc.kiAvail (W64 (sint.Z rev)) (mvcc.kiOfKey (mvcc.evsOf log) z.2.1) = some r :=
    fun r hk => mvcc.keepAt_keys log ilog0 pend0 Hcmp0 Hcnt0 Hb0 HbLog HL0.1 (sint.Z rev) (by omega)
      HcmR (by omega) r hk
  -- the clone
  icases mvcc.ownTree_keys t L0 1 $$ Htree0 with ⟨Htree0, #Hkeys0⟩
  iunfold mvcc.ownTree at Htree0
  icases Htree0 with ⟨%Hsorted0, Ht0, Hkis0⟩
  ihave %Hnd0 := mvcc.kiKeys_nodup L0 ((mvcc.itemsOfEntries_sorted_iff L0).1 Hsorted0) $$ Hkeys0
  wp_apply (h2 mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess (mvcc.itemsOfEntries L0)) $$ [Ht0]
    as %t2 ⟨Ht0, Ht2⟩
  · iframe Ht0; ipureintro; exact mvcc.kiItemLess_swo
  (try wp_auto)
  -- `ti.Unlock()`: the levels are now at most `rev`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  ihave #HlogLb : monoListLbOwn γ.log log $$ []
  · iunfold mvcc.idxCert at Hcert; icases Hcert with ⟨-, -, -, #H⟩; iexact H
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hnev0 Ht0 Hkis0 Hg0]
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog0, pend0, L0, sint.Z rev
    simp only [named]
    iframe Hnev0
    isplitl []
    · iexact Hhist0
    isplitl [Ht0 Hkis0]
    · iunfold mvcc.ownTree; iframe Ht0 Hkis0; ipureintro; exact Hsorted0
    isplitl []
    · iexact Hlb
    isplitl []
    · iexists log; iframe HlogLb; ipureintro; exact Hrl
    isplitl []
    · ipureintro; exact ⟨HL0.1.mono HcmR, by omega⟩
    isplitl []
    · ipureintro; exact Hwf0
    iunfold mvcc.idxCmpOwn
    iexists sint.Z rev, L0.map Prod.fst
    iframe Hg0
    ipureintro
    exact ⟨Int.le_refl _, fun p hp => hp, fun _ => Hr0⟩
  (try wp_auto)
  -- the iteration over the clone: each key index compacted under the lock
  wp_apply (h3 mvcc.kiPtrT t2 mvcc.kiItemIs mvcc.kiItemLess (mvcc.itemsOfEntries L0) (DFrac.own 1) _
    (fun i => iprop(ti_ptr ↦ ti ∗ rev_ptr ↦ rev ∗ available_ptr ↦ m ∗
      ghostVar γ.cmp (1 : Qp).half (sint.Z rev, (L0.drop i).map Prod.fst) ∗
      ∃ A : GMap Revision Unit, ownMap m (DFrac.own 1) A ∗
        ⌜∀ r, (A.lookup (mvcc.revVal r)).isSome ↔
          ∃ z ∈ L0.take i, mvcc.kiAvail (W64 (sint.Z rev)) (mvcc.kiOfKey (mvcc.evsOf log) z.2.1) = some r⌝))
    iprop(False))
    $$ [Ht2 ti rev available Hcmp Hm] as ⟨Ht2, Hpost⟩
  · isplitr
    · ipureintro; exact mvcc.kiItemLess_swo
    iframe Ht2 ti rev available
    isplitl [Hcmp Hm]
    · rw [List.drop_zero]
      iframe Hcmp
      iexists ∅
      iframe Hm
      ipureintro
      intro r
      simp
    unfold btIterSpec
    iintro %i %p %v %Hv
    wp_start_folded as ⟨⟨Hti, Hrev, Hav, Hcmp, %A, Hm, %HA⟩, #Hitv⟩
    -- the item: the clone's `i`-th entry
    unfold mvcc.itemsOfEntries at Hv
    rw [List.getElem?_map] at Hv
    cases hzi : L0[i]? with
    | none => rw [hzi] at Hv; simp at Hv
    | some zi =>
    rw [hzi] at Hv
    simp only [Option.map_some, Option.some.injEq] at Hv
    subst Hv
    iunfold mvcc.kiItemIs at Hitv
    icases Hitv with ⟨%Hpz, #Hkzi⟩
    simp only at Hpz
    subst Hpz
    have Hil : i < L0.length := (List.getElem?_eq_some_iff.1 hzi).1
    have HziE : L0[i] = zi := (List.getElem?_eq_some_iff.1 hzi).2
    wp_auto
    -- `ti.Lock()`
    rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Lock")]
    wp_call
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HP⟩
    wp_auto_lc 1
    iunfold mvcc.idxLockInv at HP
    icases HP with ⟨%ilog, %pend, %L, %cmax, HP⟩
    iNamedSuffix HP "L"
    iunfold mvcc.idxCmpOwn at HcmpL
    icases HcmpL with ⟨%cc, %P, HgL, %Hcc⟩
    ihave %Hag := ghostVar_agree γ.cmp _ _ _ _ $$ HgL Hcmp
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    -- the clone's key index is still in the tree (only the compactor deletes)
    have Hmem : zi.1 ∈ L.map Prod.fst :=
      Hcc.2.1 _ (by rw [List.drop_eq_getElem_cons Hil, HziE]; exact List.mem_cons_self)
    obtain ⟨z, hzL, hzp⟩ := List.mem_map.1 Hmem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hzL
    icases mvcc.ownTree_entry t L 1 z hzL $$ HtreeL with ⟨HtreeL, %Hzn, #Hkz⟩
    rw [← hzp]
    simp only
    ihave %Hk := mvcc.kiKey_agree z.1 z.2.1 zi.2.1 $$ Hkz Hkzi
    iunfold mvcc.ownTree at HtreeL
    icases HtreeL with ⟨%HsortedL, HtL, HkisL⟩
    have HW : W64 (sint.Z rev) = rev := by word
    have HsL : (mvcc.idxOfEntries L).Pairwise mvcc.idxLess := HLL.1.1
    have HzI : (mvcc.idxOfEntries L)[j]? = some (z.2.1, z.2.2) := by
      unfold mvcc.idxOfEntries; rw [List.getElem?_map, hj]; rfl
    have Hget : mvcc.idxGet (mvcc.idxOfEntries L) z.2.1 = some z.2.2 :=
      mvcc.idxGet_of_mem _ HsL (z.2.1, z.2.2) (List.mem_of_getElem? HzI)
    have HbL := HwfL.logB
    have HcmL : cmax ≤ sint.Z rev := Hcc.1
    have HcmB : cmax < 2 ^ 63 := by omega
    have Hok : mvcc.gensOk z.2.2 := mvcc.IdxCRep.gensOk HbL HLL.1 HcmB Hget
    obtain ⟨cz, -, -, -, Hzne⟩ := mvcc.IdxCRep.get_some HLL.1 Hget
    -- borrow the entry
    icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hj |>.1 $$ HkisL
      with ⟨Hz, Hback⟩
    iunfold mvcc.ownEntry at Hz
    icases Hz with ⟨-, %gs, Hzki⟩
    wp_apply (h4 z.1 gs z.2.2 lg rev m A Hlgnn Hok Hzne) $$ [Hzki Hm] as ⟨%gs', Hzki, Hm⟩
    · iframe Hzki Hm
    wp_apply (h5 z.1 gs' (mvcc.kiCompact rev z.2.2) (DFrac.own 1)) $$ [Hzki] as Hzki
    · iframe Hzki
    ispecialize Hback $$ %(z.1, z.2.1, mvcc.kiCompact rev z.2.2) [Hzki]
    · iunfold mvcc.ownEntry
      isplitl []
      · ipureintro; exact Hzn
      iexists gs'; iexact Hzki
    -- the compactor moves on
    imod ghostVar_update_halves (sint.Z rev, (L0.drop (i + 1)).map Prod.fst) γ.cmp _ _ $$ HgL Hcmp
      with ⟨HgL, Hcmp⟩
    -- the map: the key's kept revision, as the log has it
    ihave Hkn : mvcc.idxKnows γ (.cert log) $$ []
    · rw [mvcc.idxKnows_cert]; iexact Hcert
    icases mvcc.idxKnows_facts γ (.cert log) log rfl ilog pend 1 $$ Hkn HhistL HnevL
      with ⟨%Hf, -, HnevL⟩
    obtain ⟨Hcmpf, Hcntf, -, -, -⟩ := Hf
    have Havail : mvcc.kiAvail rev z.2.2 =
        mvcc.kiAvail (W64 (sint.Z rev)) (mvcc.kiOfKey (mvcc.evsOf log) zi.2.1) := by
      rw [← Hk, ← mvcc.reader_avail log ilog pend Hcmpf Hcntf (by have := HwfL.2.1; omega) HbLog
        z.2.1 (sint.Z rev) (by omega) Hrl,
        ← mvcc.IdxCRep.avail_some HbL HLL.1 (sint.Z rev) HcmL Hrz Hget, HW]
    have HA' : ∀ r, ((mvcc.availAdd A (mvcc.kiAvail rev z.2.2)).lookup (mvcc.revVal r)).isSome ↔
        ∃ z' ∈ L0.take (i + 1),
          mvcc.kiAvail (W64 (sint.Z rev)) (mvcc.kiOfKey (mvcc.evsOf log) z'.2.1) = some r := by
      intro r
      rw [mvcc.availAdd_lookup, HA r, Havail, List.take_add_one, hzi]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨z', hz', h⟩ | h)
        · exact ⟨z', Or.inl hz', h⟩
        · exact ⟨zi, Or.inr rfl, h⟩
      · rintro ⟨z', (hz' | rfl), h⟩
        · exact Or.inl ⟨z', hz', h⟩
        · exact Or.inr h
    have Hptr : ∀ p ∈ (L0.drop (i + 1)).map Prod.fst, p ∈ L.map Prod.fst ∧ p ≠ z.1 := by
      intro p hp
      refine ⟨Hcc.2.1 p ?_, ?_⟩
      · rw [List.drop_eq_getElem_cons Hil, List.map_cons]; exact List.mem_cons_of_mem _ hp
      · rw [hzp]; exact mvcc.nodup_drop_ne L0 Hnd0 i zi hzi p hp
    cases Hemp : mvcc.kiIsEmpty (mvcc.kiCompact rev z.2.2)
    · -- not emptied: the key index stays, compacted
      wp_pures
      (try wp_auto)
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
      wp_call
      (try wp_auto)
      have hset := mvcc.itemsOfEntries_set L j z (z.1, z.2.1, mvcc.kiCompact rev z.2.2) hj rfl rfl
      have hidx : mvcc.IdxCRep (sint.Z rev) (mvcc.evsOf (ilog ++ [pend]))
          (mvcc.idxOfEntries (L.set j (z.1, z.2.1, mvcc.kiCompact rev z.2.2))) := by
        have := mvcc.IdxCRep.compactAt HbL HLL.1 HcmL Hrz j z.2.1 z.2.2 HzI
        rw [HW, Hemp] at this
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        rw [mvcc.idxOfEntries_set]; exact this
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL HtL Hback HgL]
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L.set j (z.1, z.2.1, mvcc.kiCompact rev z.2.2), sint.Z rev
        simp only [named]
        iframe HnevL
        isplitl []
        · iexact HhistL
        isplitl [HtL Hback]
        · iunfold mvcc.ownTree; rw [hset]; iframe HtL Hback; ipureintro; exact HsortedL
        isplitl []
        · iexact Hlb
        isplitl []
        · iexists log; iframe HlogLb; ipureintro; exact Hrl
        isplitl []
        · ipureintro; exact ⟨hidx, by omega⟩
        isplitl []
        · ipureintro; exact HwfL
        iunfold mvcc.idxCmpOwn
        iexists sint.Z rev, (L0.drop (i + 1)).map Prod.fst
        iframe HgL
        ipureintro
        refine ⟨Int.le_refl _, fun p hp => ?_, fun _ => Hr0⟩
        rw [mvcc.ptrs_set L j z (z.1, z.2.1, mvcc.kiCompact rev z.2.2) hj rfl]
        exact (Hptr p hp).1
      (try wp_auto)
      iapply HΦ
      simp only [↓reduceIte]
      iframe Hti Hrev Hav Hcmp
      iexists _
      iframe Hm
      ipureintro; exact HA'
    · -- emptied: deleted from the tree
      wp_pures
      wp_auto
      ihave #Hitem : mvcc.kiItemIs z.1 (z.1, z.2.1) $$ []
      · iunfold mvcc.kiItemIs
        isplitl []
        · ipureintro; rfl
        iexact Hkz
      wp_apply (h6 mvcc.kiPtrT t mvcc.kiItemIs mvcc.kiItemLess (mvcc.itemsOfEntries L) z.1 (z.1, z.2.1))
        $$ [HtL] as %old %ok ⟨HtL, Hres⟩
      · iframe HtL Hitem; ipureintro; exact mvcc.kiItemLess_swo
      have HsE : L.Pairwise mvcc.entryLess := (mvcc.itemsOfEntries_sorted_iff L).1 HsortedL
      cases hf : btFind mvcc.kiItemLess (z.1, z.2.1) (mvcc.itemsOfEntries L) with
      | none =>
        exfalso
        rw [mvcc.btFind_items L HsortedL z.1 z.2.1] at hf
        simp only [Option.map_eq_none_iff] at hf
        have := List.find?_eq_none.1 hf z hzL
        simp at this
      | some w =>
      simp only
      icases Hres with ⟨%Hok, -⟩
      subst Hok
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"Unlock")]
      wp_call
      (try wp_auto)
      have hdel := mvcc.btDelete_items_eraseIdx L HsE j z z.1 hj
      have hidx : mvcc.IdxCRep (sint.Z rev) (mvcc.evsOf (ilog ++ [pend])) (mvcc.idxOfEntries (L.eraseIdx j)) := by
        have := mvcc.IdxCRep.compactAt HbL HLL.1 HcmL Hrz j z.2.1 z.2.2 HzI
        rw [HW, Hemp] at this
        simp only [↓reduceIte] at this
        rw [mvcc.idxOfEntries_eraseIdx]; exact this
      have hjl : j < L.length := (List.getElem?_eq_some_iff.1 hj).1
      icases mvcc.bigSepL_ownEntry_eraseIdx 1 (L.set j (z.1, z.2.1, mvcc.kiCompact rev z.2.2)) j _
        (List.getElem?_set_self hjl) $$ Hback with ⟨-, Hback⟩
      rw [List.eraseIdx_set_eq]
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk HnevL HtL Hback HgL]
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L.eraseIdx j, sint.Z rev
        simp only [named]
        iframe HnevL
        isplitl []
        · iexact HhistL
        isplitl [HtL Hback]
        · iunfold mvcc.ownTree
          rw [← hdel]
          iframe HtL Hback
          ipureintro; exact btDelete_sorted HsortedL
        isplitl []
        · iexact Hlb
        isplitl []
        · iexists log; iframe HlogLb; ipureintro; exact Hrl
        isplitl []
        · ipureintro; exact ⟨hidx, by omega⟩
        isplitl []
        · ipureintro; exact HwfL
        iunfold mvcc.idxCmpOwn
        iexists sint.Z rev, (L0.drop (i + 1)).map Prod.fst
        iframe HgL
        ipureintro
        exact ⟨Int.le_refl _, fun p hp => mvcc.ptrs_eraseIdx L j z hj p (Hptr p hp).1 (Hptr p hp).2,
          fun _ => Hr0⟩
      (try wp_auto)
      iapply HΦ
      simp only [↓reduceIte]
      iframe Hti Hrev Hav Hcmp
      iexists _
      iframe Hm
      ipureintro; exact HA'
  icases Hpost with (%Hf | ⟨Hti, Hrev, Hav, Hcmp, %A, Hm, %HA⟩)
  · exact Hf.elim
  have Hlen : (mvcc.itemsOfEntries L0).length = L0.length := by unfold mvcc.itemsOfEntries; simp
  simp only [Hlen, List.drop_length, List.take_length, List.map_nil] at HA ⊢
  wp_auto
  iapply HΦ
  iunfold mvcc.idxCompactor
  iframe Hcmp
  iexists A
  iframe Hm
  ipureintro
  intro r
  rw [HA r]
  constructor
  · rintro ⟨z, -, hz⟩; exact ⟨z.2.1, hz⟩
  · intro hk; exact Hkeys r hk

end proof

end EtcdGrove
end Perennial
