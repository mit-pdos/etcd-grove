/-
Proof of `Spec/.../mvcc/watcherGroup__add.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__add
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSetByKey__add
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffineInterval
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Insert
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

theorem mvcc.watcherGroup.add.wp_proof
    (hSAdd : mvcc.watcherSet.add.spec (GF := GF) (hG := hG))
    (hKAdd : mvcc.watcherSetByKey.add.spec (GF := GF) (hG := hG))
    (hIvl : adt.NewStringAffineInterval.spec (GF := GF) (hG := hG))
    (hFind : adt.intervalTree.Find.spec (GF := GF) (hG := hG))
    (hInsert : adt.intervalTree.Insert.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.add.spec (GF := GF) (hG := hG) := by
  intro wg W ws wa r fcs
  wp_start as ⟨Hg, #Hfix, %Hwa, %Hsz⟩
  iunfold mvcc.ownWatcherGroupAt at Hg
  icases Hg with ⟨%km, %t, %KM, %L, Hg⟩
  iNamed Hg
  ihave #Hfix' := Hfix
  iunfold mvcc.watcherFixed at Hfix'
  icases Hfix' with ⟨%Hnn, %ks, %es, #Hk, #Hks, #He, #Hes, #Hs, #Hi, #Hf⟩
  -- the members with `wa`'s fixed fields
  ihave #Hfixed' : [∗map] w ↦ r' ∈ <[wa := r]> W, ∃ fcs', mvcc.watcherFixed w r' fcs' $$ []
  · iapply (BigSepM.bigSepM_insert (m := W) Hwa).2
    iframe Hfixed
    iexists fcs; iexact Hfix
  wp_auto
  wp_method_call
  wp_call
  wp_load
  simp only
  wp_apply hSAdd $$ [$Hws] as Hws
  · ipureintro; rw [GMap.domSet, GMap.lookup_fmap, Hwa]; rfl
  rw [show <[wa := ()]> (GMap.domSet W) = GMap.domSet (<[wa := r]> W) from
    (GMap.fmap_insert _ _ _ _).symm]
  cases hend : r.end? with
  | none =>
    icases Hes with %Hes
    subst Hes
    rw [_root_.decide_eq_true rfl]
    wp_auto
    wp_method_call
    wp_call
    wp_load
    simp only
    wp_apply hKAdd $$ [$Hkm] as ⟨%KM', Hkm⟩
    · iframe Hfix; ipureintro; exact ⟨Hwa, hend⟩
    wp_auto
    iapply HΦ
    have Hsame : ∀ z ∈ L, mvcc.ivlMembers (<[wa := r]> W) z.1 = mvcc.ivlMembers W z.1 :=
      fun z _ => mvcc.ivlMembers_insert_ne W wa r z.1 Hwa (by rw [hend]; simp)
    iapply mvcc.ownWatcherGroupAt_intro wg (<[wa := r]> W) km ws t KM' L
    · refine ⟨HL.1, fun ivl => ?_⟩
      rw [HL.2 ivl]
      constructor
      · rintro ⟨w, r', e, hw, he, rfl⟩
        refine ⟨w, r', e, ?_, he, rfl⟩
        rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [Hwa] at hw; cases hw)]
        exact hw
      · rintro ⟨w, r', e, hw, he, rfl⟩
        by_cases hww : w = wa
        · subst hww; rw [GMap.lookup_insert] at hw; cases hw; rw [hend] at he; cases he
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hww)] at hw
          exact ⟨w, r', e, hw, he, rfl⟩
    iframe Hwg Hws Hfixed' Hkm Hivt
    iapply mvcc.rangeSets_congr W _ L Hsame $$ Hranges
  | some e =>
    icases Hes with ⟨%Hes, #Hes⟩
    rw [_root_.decide_eq_false Hes]
    wp_auto
    wp_apply wp_bytes_to_string ks r.key DFrac.discard $$ [$Hks] as -
    wp_apply wp_bytes_to_string es e DFrac.discard $$ [$Hes] as -
    wp_apply hIvl r.key e
    wp_apply hFind $$ [$Hivt] as %p Hp
    have Hnd := mvcc.sorted_nodup L HL.1
    icases Hp with (⟨%z, %Hz, %Hpn, Hp, Hback⟩ | ⟨%Hpn, Hivt⟩)
    · obtain ⟨hzL, hz1⟩ := Hz
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hzL
      icases (BigSepL.bigSepL_lookup_acc_impl hi) $$ Hranges with ⟨Hz, Hranges⟩
      iunfold mvcc.rangeSet at Hz
      icases Hz with ⟨%m0, %Hz2, Hm0⟩
      rw [_root_.decide_eq_false Hpn]
      wp_auto
      ihave Hivt := Hback $$ Hp
      rw [Hz2]
      wp_auto
      ihave Hm0 : mvcc.ownWatcherSet m0 (mvcc.ivlMembers W z.1) $$ [Hm0]
      · iexact Hm0
      wp_apply hSAdd $$ [$Hm0] as Hm0
      · ipureintro; rw [mvcc.ivlMembers, mvcc.membersBy_lookup, Hwa]
      iapply HΦ
      iapply mvcc.ownWatcherGroupAt_intro wg (<[wa := r]> W) km ws t KM L
      · refine mvcc.rangesOk_insert_range W L L wa r e Hwa hend HL.2 HL.1 (fun ivl => ?_)
        constructor
        · exact Or.inl
        · rintro (h | rfl)
          · exact h
          · rw [← hz1]; exact List.mem_map_of_mem hzL
      iframe Hwg Hws Hfixed'
      isplitl [Hkm]
      · iapply mvcc.ownKeyMap_insert_range km KM W wa r Hwa (by rw [hend]; simp) $$ Hkm
      iframe Hivt
      iapply Hranges
      · imodintro
        iintro %k %y %hy %hki Hy
        have hne := mvcc.entries_ne L Hnd hy hi hki
        unfold mvcc.rangeSet
        rw [mvcc.ivlMembers_insert_ne W wa r y.1 Hwa (by
          rw [hend]; simp only [Option.map_some, ne_eq, Option.some.injEq]; rw [← hz1]
          exact Ne.symm hne)]
        iexact Hy
      unfold mvcc.rangeSet
      iexists m0
      isplitl []
      · ipureintro; exact Hz2
      have hz' : mvcc.ivlMembers (<[wa := r]> W) z.1 = <[wa := ()]> (mvcc.ivlMembers W z.1) := by
        rw [hz1]; exact mvcc.ivlMembers_insert_eq W wa r e Hwa hend
      rw [hz']
      iexact Hm0
    · obtain ⟨rfl, Hnotin⟩ := Hpn
      have Hemp : mvcc.ivlMembers W (r.key, e) = ∅ := by
        rw [mvcc.ivlMembers_empty_iff, ← HL.2]; exact Hnotin
      rw [_root_.decide_eq_true rfl, Bool.not_true]
      wp_auto
      rw [go.make1_underlying, go.is_underlying (t := watcherSet.ty)]
      wp_apply (wp_map_make1 (K := Loc) (V := Unit)) as %mn Hmn
      wp_method_call
      wp_call
      wp_load
      ihave Hmn : mvcc.ownWatcherSet mn ∅ $$ [Hmn]
      · iunfold mvcc.ownWatcherSet; iexact Hmn
      wp_apply hSAdd $$ [$Hmn] as Hmn
      · ipureintro; rfl
      wp_apply hInsert $$ [$Hivt] as Hivt
      · ipureintro; have := mvcc.rangesOk_length_le W L HL; omega
      iapply HΦ
      iapply mvcc.ownWatcherGroupAt_intro wg (<[wa := r]> W) km ws t KM
        (adt.ivtInsert ((r.key, e), interface.mkOk watcherSet.ty #mn) L)
      · refine mvcc.rangesOk_insert_range W L _ wa r e Hwa hend HL.2
          (adt.ivtInsert_sorted _ L HL.1 Hnotin) (fun ivl => ?_)
        simp only [List.mem_map, adt.mem_ivtInsert]
        constructor
        · rintro ⟨z, rfl | hz, rfl⟩
          · exact Or.inr rfl
          · exact Or.inl ⟨z, hz, rfl⟩
        · rintro (⟨z, hz, rfl⟩ | rfl)
          · exact ⟨z, Or.inr hz, rfl⟩
          · exact ⟨_, Or.inl rfl, rfl⟩
      iframe Hwg Hws Hfixed'
      isplitl [Hkm]
      · iapply mvcc.ownKeyMap_insert_range km KM W wa r Hwa (by rw [hend]; simp) $$ Hkm
      iframe Hivt
      iapply (BigSepL.bigSepL_perm (adt.ivtInsert_perm _ L)).2
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hmn]
      · unfold mvcc.rangeSet
        iexists mn
        isplitl []
        · ipureintro; rfl
        simp only
        rw [mvcc.ivlMembers_insert_eq W wa r e Hwa hend, Hemp]
        iexact Hmn
      iapply mvcc.rangeSets_congr W _ L (fun z hz => ?_) $$ Hranges
      apply mvcc.ivlMembers_insert_ne W wa r z.1 Hwa
      rw [hend]; simp only [Option.map_some, ne_eq, Option.some.injEq]
      intro h; exact Hnotin (h ▸ List.mem_map_of_mem hz)

end proof

end EtcdGrove
end Perennial
