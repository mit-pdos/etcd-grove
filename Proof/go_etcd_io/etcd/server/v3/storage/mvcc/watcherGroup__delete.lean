/-
Proof of `Spec/.../mvcc/watcherGroup__delete.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__delete
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__delete
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSetByKey__delete
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffineInterval
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Find
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Delete
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

theorem mvcc.watcherGroup.delete.wp_proof
    (hSDel : mvcc.watcherSet.delete.spec (GF := GF) (hG := hG))
    (hKDel : mvcc.watcherSetByKey.delete.spec (GF := GF) (hG := hG))
    (hIvl : adt.NewStringAffineInterval.spec (GF := GF) (hG := hG))
    (hFind : adt.intervalTree.Find.spec (GF := GF) (hG := hG))
    (hDel : adt.intervalTree.Delete.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.delete.spec (GF := GF) (hG := hG) := by
  intro wg W ws wa r fcs
  wp_start as ⟨Hg, #Hfix⟩
  icases mvcc.ownWatcherGroupAt_member wg W ws wa r fcs $$ [Hg] with ⟨Hg, %Hwa⟩
  · iframe Hg Hfix
  iunfold mvcc.ownWatcherGroupAt at Hg
  icases Hg with ⟨%km, %t, %KM, %L, Hg⟩
  iNamed Hg
  ihave #Hfix' := Hfix
  iunfold mvcc.watcherFixed at Hfix'
  icases Hfix' with ⟨%Hnn, %ks, %es, #Hk, #Hks, #He, #Hes, #Hs, #Hi, #Hf⟩
  iunfold mvcc.ownWatcherSet at Hws
  wp_auto
  simp only
  wp_apply wp_map_lookup2 $$ Hws as Hws
  rcases Hwa with HwaN | HwaS
  · -- not a member
    rw [GMap.delete_notin _ _ HwaN, HwaN]
    simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false,
      Bool.not_false]
    wp_auto
    iapply HΦ
    iapply mvcc.ownWatcherGroupAt_intro wg W km ws t KM L HL
    iframe Hwg Hfixed Hkm Hivt Hranges
    iunfold mvcc.ownWatcherSet; iexact Hws
  rw [HwaS]
  simp only [Option.map_some, Option.isSome_some, _root_.decide_true, Bool.not_true]
  ihave #Hfixed' : [∗map] w ↦ r' ∈ GMap.delete wa W, ∃ fcs', mvcc.watcherFixed w r' fcs' $$ []
  · icases (BigSepM.bigSepM_delete (m := W) HwaS).1 $$ Hfixed with ⟨-, H⟩
    iexact H
  wp_auto
  wp_method_call
  wp_call
  wp_load
  simp only
  ihave Hws : mvcc.ownWatcherSet ws (GMap.domSet W) $$ [Hws]
  · iunfold mvcc.ownWatcherSet; iexact Hws
  wp_apply hSDel $$ [$Hws] as Hws
  · ipureintro; rw [GMap.domSet, GMap.lookup_fmap, HwaS]; rfl
  rw [show GMap.delete wa (GMap.domSet W) = GMap.domSet (GMap.delete wa W) from
    (GMap.fmap_delete _ _ _).symm]
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
    wp_apply hKDel $$ [$Hkm] as ⟨%KM', Hkm⟩
    · iframe Hfix; ipureintro; exact ⟨hend, Or.inr HwaS⟩
    iapply HΦ
    iapply mvcc.ownWatcherGroupAt_intro wg (GMap.delete wa W) km ws t KM' L
      (mvcc.rangesOk_delete_key W L wa r HwaS hend HL)
    iframe Hwg Hws Hfixed' Hkm Hivt
    iapply mvcc.rangeSets_congr W _ L (fun z _ =>
      mvcc.ivlMembers_delete_ne W wa r HwaS z.1 (by rw [hend]; simp)) $$ Hranges
  | some e =>
    icases Hes with ⟨%Hes, #Hes⟩
    rw [_root_.decide_eq_false Hes]
    wp_auto
    wp_apply wp_bytes_to_string ks r.key DFrac.discard $$ [$Hks] as -
    wp_apply wp_bytes_to_string es e DFrac.discard $$ [$Hes] as -
    wp_apply hIvl r.key e
    wp_apply hFind $$ [$Hivt] as %p Hp
    have Hnd := mvcc.sorted_nodup L HL.1
    have Hin : (r.key, e) ∈ L.map Prod.fst := (HL.2 _).2 ⟨wa, r, e, HwaS, hend, rfl⟩
    obtain ⟨z, hf⟩ : ∃ z, L.find? (fun z => decide (z.1 = (r.key, e))) = some z := by
      cases h : L.find? (fun z => decide (z.1 = (r.key, e))) with
      | some z => exact ⟨z, rfl⟩
      | none =>
        exfalso
        obtain ⟨z, hz, hz1⟩ := List.mem_map.1 Hin
        have := List.find?_eq_none.1 h z hz
        simp [hz1] at this
    rw [hf]
    icases Hp with ⟨%Hpn, Hp, Hback⟩
    have hz1 : z.1 = (r.key, e) := by simpa using List.find?_some hf
    have Hperm := mvcc.perm_eraseP_of_find? L _ z hf
    icases (BigSepL.bigSepL_perm Hperm).1 $$ Hranges with Hranges
    icases BigSepL.bigSepL_cons.1 $$ Hranges with ⟨Hz, Hrest⟩
    iunfold mvcc.rangeSet at Hz
    icases Hz with ⟨%m0, %Hz2, Hm0⟩
    rw [_root_.decide_eq_false Hpn]
    wp_auto
    ihave Hivt := Hback $$ Hp
    rw [Hz2]
    wp_auto
    rw [go.delete_underlying, go.is_underlying (t := watcherSet.ty)]
    iunfold mvcc.ownWatcherSet at Hm0
    wp_apply wp_mapDelete $$ Hm0 as Hm0
    wp_apply wp_map_len_lt $$ Hm0 as ⟨Hm0, %Hlt⟩
    rw [← mvcc.ivlMembers_delete] at Hlt ⊢
    -- the other entries' sets, the key map
    have Hne : ∀ y ∈ L.eraseP (fun z => decide (z.1 = (r.key, e))), y.1 ≠ (r.key, e) :=
      fun y hy => ((mvcc.mem_eraseP_fst L Hnd _ y).1 hy).2
    have Hsame : ∀ y ∈ L.eraseP (fun z => decide (z.1 = (r.key, e))),
        mvcc.ivlMembers (GMap.delete wa W) y.1 = mvcc.ivlMembers W y.1 :=
      fun y hy => mvcc.ivlMembers_delete_ne W wa r HwaS y.1 (by
        rw [hend]; simp only [Option.map_some, ne_eq, Option.some.injEq]
        exact Ne.symm (Hne y hy))
    ihave Hrest := mvcc.rangeSets_congr W (GMap.delete wa W) _ Hsame $$ Hrest
    ihave Hkm := mvcc.ownKeyMap_delete_range km KM W wa r HwaS (by rw [hend]; simp) $$ Hkm
    have Hother : ∀ ivl, ivl ≠ (r.key, e) →
        ((∃ w r' e', GMap.delete wa W !! w = some r' ∧ r'.end? = some e' ∧ ivl = (r'.key, e')) ↔
          ivl ∈ L.map Prod.fst) := fun ivl hne => by
      rw [HL.2 ivl]
      exact mvcc.exists_ivl_delete W wa r HwaS ivl (by
        rw [hend]; simp only [Option.map_some, ne_eq, Option.some.injEq]; exact Ne.symm hne)
    wp_if_destruct
    · -- the interval's set is empty now: it goes from the tree
      have H0 : GMap.size (mvcc.ivlMembers (GMap.delete wa W) z.1) = 0 := by word
      rw [GMap.map_size_empty_iff, hz1, mvcc.ivlMembers_empty_iff] at H0
      wp_apply hDel $$ [$Hivt] as Hivt
      rw [_root_.decide_eq_true Hin]
      wp_auto
      iapply HΦ
      iapply mvcc.ownWatcherGroupAt_intro wg (GMap.delete wa W) km ws t KM
        (L.eraseP fun z => decide (z.1 = (r.key, e)))
      · refine ⟨HL.1.sublist (List.eraseP_sublist), fun ivl => ?_⟩
        have hm : ivl ∈ (L.eraseP fun z => decide (z.1 = (r.key, e))).map Prod.fst ↔
            ivl ∈ L.map Prod.fst ∧ ivl ≠ (r.key, e) := by
          simp only [List.mem_map]
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨y, ((mvcc.mem_eraseP_fst L Hnd _ y).1 hy).1, rfl⟩, Hne y hy⟩
          · rintro ⟨⟨y, hy, rfl⟩, hne⟩
            exact ⟨y, (mvcc.mem_eraseP_fst L Hnd _ y).2 ⟨hy, hne⟩, rfl⟩
        rw [hm]
        by_cases hi : ivl = (r.key, e)
        · subst hi
          constructor
          · rintro ⟨-, h⟩; exact absurd rfl h
          · intro h; exact absurd h H0
        · rw [Hother ivl hi]
          exact ⟨fun h => h.1, fun h => ⟨h, hi⟩⟩
      iframe Hwg Hws Hfixed' Hkm Hivt Hrest
    · iapply HΦ
      have H0 : GMap.size (mvcc.ivlMembers (GMap.delete wa W) z.1) ≠ 0 := by
        intro h; apply Hif; rw [h]; rfl
      rw [ne_eq, GMap.map_size_empty_iff, hz1, mvcc.ivlMembers_empty_iff, Classical.not_not] at H0
      iapply mvcc.ownWatcherGroupAt_intro wg (GMap.delete wa W) km ws t KM L
      · refine ⟨HL.1, fun ivl => ?_⟩
        by_cases hi : ivl = (r.key, e)
        · subst hi
          exact ⟨fun _ => H0, fun _ => Hin⟩
        · exact (Hother ivl hi).symm
      iframe Hwg Hws Hfixed' Hkm Hivt
      iapply (BigSepL.bigSepL_perm Hperm).2
      iapply BigSepL.bigSepL_cons.2
      iframe Hrest
      unfold mvcc.rangeSet
      iexists m0
      isplitl []
      · ipureintro; exact Hz2
      iunfold mvcc.ownWatcherSet
      iexact Hm0

end proof

end EtcdGrove
end Perennial
