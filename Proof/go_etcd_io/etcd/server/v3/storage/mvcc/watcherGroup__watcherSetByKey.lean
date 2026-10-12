/-
Proof of `Spec/.../mvcc/watcherGroup__watcherSetByKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__watcherSetByKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSet__union
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffinePoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Stab
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

theorem mvcc.watcherGroup.watcherSetByKey.wp_proof
    (hPoint : adt.NewStringAffinePoint.spec (GF := GF) (hG := hG))
    (hStab : adt.intervalTree.Stab.spec (GF := GF) (hG := hG))
    (hUnion : mvcc.watcherSet.union.spec (GF := GF) (hG := hG)) :
    mvcc.watcherGroup.watcherSetByKey.spec (GF := GF) (hG := hG) := by
  intro wg W key
  wp_start as Hg
  iunfold mvcc.ownWatcherGroup at Hg
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iunfold mvcc.ownKeyMap at Hkm
  icases Hkm with ⟨Hkm, %Hdom, Hsets⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hkm as Hkm
  wp_apply hPoint key
  wp_apply hStab $$ [$Hivt] as %ivs %ps ⟨Hivt, Hps, Hcap, %Hlen, #Hpts⟩
  ihave %Hsl := ownSlice_len $$ Hps
  have Hcov := mvcc.coverUpTo_stab W L HL key
  -- the key's own set: lent, or none
  have HkeyE : KM !! key = none → mvcc.keyMembers W key = ∅ := fun hk => by
    rw [mvcc.keyMembers_empty_iff]; intro h; have := (Hdom key).2 h; rw [hk] at this; cases this
  by_cases h0 : adt.stab (key, key ++ go!"\x00") L = []
  · -- no range holds the key: the key's set, or `nil`
    have Hlen0 : ivs.len = W64 0 := by
      rw [h0] at Hlen; rw [Hlen] at Hsl
      have h1 := Hsl.1; have h2 := Hsl.2
      simp only [List.length_nil] at h1
      word
    rw [Hlen0, _root_.decide_eq_true rfl, _root_.decide_eq_true rfl]
    rw [h0, List.map_nil, mvcc.coverUpTo_nil] at Hcov
    rw [← Hcov]
    wp_auto
    cases hk : KM !! key with
    | none =>
      simp only [Option.getD_none]
      iapply HΦ
      isplitl []
      · iunfold mvcc.ownWatcherSetOpt; ileft; ipureintro; exact ⟨rfl, HkeyE hk⟩
      iintro -
      iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
      iframe Hwg Hws Hfixed Hivt Hranges
      iunfold mvcc.ownKeyMap
      iframe Hkm Hsets
      ipureintro; exact Hdom
    | some m0 =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc (m := KM) hk).1 $$ Hsets with ⟨Hset, Hsets⟩
      iunfold mvcc.ownWatcherSet at Hset
      ihave %Hm0 := ownMap_not_nil _ _ _ $$ Hset
      iapply HΦ
      isplitl [Hset]
      · iunfold mvcc.ownWatcherSetOpt; iright; iunfold mvcc.ownWatcherSet; iexact Hset
      iintro Hset
      iunfold mvcc.ownWatcherSetOpt at Hset
      icases Hset with (%Hnil | Hset)
      · exact absurd Hnil.1 Hm0
      iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
      iframe Hwg Hws Hfixed Hivt Hranges
      iunfold mvcc.ownKeyMap
      iframe Hkm
      isplitl []
      · ipureintro; exact Hdom
      iapply Hsets $$ Hset
  have Hlenne : ivs.len ≠ W64 0 := by
    intro h; apply h0; rw [h] at Hsl
    have h1 := Hsl.1
    rw [Hlen] at h1
    apply List.eq_nil_of_length_eq_zero; rw [h1]; rfl
  rw [_root_.decide_eq_false Hlenne]
  wp_auto
  rw [_root_.decide_eq_false Hlenne]
  wp_auto
  wp_bind (If (Val #(decide (ivs.len = W64 1))) _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #(decide (ivs.len = W64 1 ∧ KM !! key = none))⌝ ∗
      wkeys_ptr ↦ (KM !! key).getD (zero_val GoMap) ∗
      [∗map] k ↦ m ∈ KM, mvcc.ownWatcherSet m (mvcc.keyMembers W k))))
  isplitl [wkeys Hsets]
  · by_cases hl : ivs.len = W64 1
    · rw [_root_.decide_eq_true hl]
      wp_auto
      cases hk : KM !! key with
      | none =>
        simp only [Option.getD_none]
        rw [show (zero_val GoMap) = map.nil from rfl]
        wp_auto
        iframe wkeys Hsets
        ipureintro
        rw [_root_.decide_eq_true ⟨hl, trivial⟩]
      | some m0 =>
        simp only [Option.getD_some]
        icases (BigSepM.bigSepM_lookup_acc (m := KM) hk).1 $$ Hsets with ⟨Hset, Hsets⟩
        iunfold mvcc.ownWatcherSet at Hset
        wp_apply wp_map_len_lt $$ Hset as ⟨Hset, %Hlt⟩
        have Hne : GMap.size (mvcc.keyMembers W key) ≠ 0 := by
          rw [ne_eq, GMap.map_size_empty_iff, mvcc.keyMembers_empty_iff, Classical.not_not]
          exact (Hdom key).1 (by rw [hk]; rfl)
        have Hne' : W64 (GMap.size (mvcc.keyMembers W key) : Int) ≠ W64 0 := by
          intro h; apply Hne; word
        rw [_root_.decide_eq_false Hne']
        iframe wkeys
        isplitl []
        · ipureintro
          rw [_root_.decide_eq_false (fun h => by cases h.2)]
        iapply Hsets
        iunfold mvcc.ownWatcherSet
        iexact Hset
    · rw [_root_.decide_eq_false hl]
      wp_auto
      iframe wkeys Hsets
      ipureintro
      rw [_root_.decide_eq_false (fun h => hl h.1)]
  iintro %v ⟨%Hv, wkeys, Hsets⟩
  subst Hv
  by_cases hB : ivs.len = W64 1 ∧ KM !! key = none
  · -- one range holds the key, no key set: that range's set
    rw [_root_.decide_eq_true hB]
    obtain ⟨hl1, hk⟩ := hB
    have HSt1 : (adt.stab (key, key ++ go!"\x00") L).length = 1 := by
      rw [← Hlen, Hsl.1, hl1]; rfl
    obtain ⟨z, hSt⟩ : ∃ z, adt.stab (key, key ++ go!"\x00") L = [z] := by
      match h : adt.stab (key, key ++ go!"\x00") L, HSt1 with
      | [z], _ => exact ⟨z, rfl⟩
    obtain ⟨p0, hps⟩ : ∃ p0, ps = [p0] := by
      match ps, Hlen with
      | [p0], _ => exact ⟨p0, rfl⟩
      | [], h => rw [hSt] at h; cases h
      | _ :: _ :: _, h => rw [hSt] at h; cases h
    subst hps
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ivs.len by
      rw [hl1]; decide)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) p0 ivs _ [p0] (by decide) (by simp) $$ Hps
      with ⟨Hp0, Hps⟩
    wp_auto
    rw [hSt] at Hcov
    rw [hSt]
    simp only [List.zip_cons_cons, List.zip_nil_left]
    icases BigSepL.bigSepL_singleton.1 $$ Hpts with ⟨%Hp0n, #Hp0v⟩
    icases mvcc.iv_split p0 _ _ $$ Hp0v with ⟨-, #Hval⟩
    have hzL : z ∈ L := by
      have : z ∈ adt.stab (key, key ++ go!"\x00") L := by rw [hSt]; simp
      exact (List.mem_filter.1 this).1
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hzL
    icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hranges with ⟨Hz, Hranges⟩
    iunfold mvcc.rangeSet at Hz
    icases Hz with ⟨%m, %Hz2, Hm⟩
    simp only
    rw [Hz2]
    wp_auto
    have HS : mvcc.membersBy W (·.covers key) = mvcc.ivlMembers W z.1 := by
      rw [← Hcov, List.map_cons, List.map_nil, show [z.1] = [] ++ [z.1] from rfl,
        mvcc.coverUpTo_snoc, mvcc.coverUpTo_nil, HkeyE hk, GMap.mapEmpty_union]
    rw [HS]
    iunfold mvcc.ownWatcherSet at Hm
    ihave %Hmn := ownMap_not_nil _ _ _ $$ Hm
    iapply HΦ
    isplitl [Hm]
    · iunfold mvcc.ownWatcherSetOpt; iright; iunfold mvcc.ownWatcherSet; iexact Hm
    iintro Hm
    iunfold mvcc.ownWatcherSetOpt at Hm
    icases Hm with (%Hnil | Hm)
    · exact absurd Hnil.1 Hmn
    ihave Hranges := Hranges $$ [Hm]
    · iunfold mvcc.rangeSet; iexists m; iframe Hm; ipureintro; exact Hz2
    have hset : L.set i z = L := by
      obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hi; exact List.set_getElem_self h
    rw [hset]
    iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
    iframe Hwg Hws Hfixed Hivt Hranges
    iunfold mvcc.ownKeyMap
    iframe Hkm Hsets
    ipureintro; exact Hdom
  -- the copy case: a fresh set, the union of the key's set and the ranges' sets
  rw [_root_.decide_eq_false hB]
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := watcherSet.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Unit)) as %mret Hret
  simp only
  wp_apply wp_map_lookup1 $$ Hkm as Hkm
  ihave Hopt : iprop(mvcc.ownWatcherSetOpt ((KM !! key).getD (zero_val GoMap)) (mvcc.keyMembers W key) ∗
      (mvcc.ownWatcherSetOpt ((KM !! key).getD (zero_val GoMap)) (mvcc.keyMembers W key) -∗
        [∗map] k ↦ m ∈ KM, mvcc.ownWatcherSet m (mvcc.keyMembers W k))) $$ [Hsets]
  · cases hk : KM !! key with
    | none =>
      simp only [Option.getD_none]
      isplitr
      · iunfold mvcc.ownWatcherSetOpt; ileft; ipureintro; exact ⟨rfl, HkeyE hk⟩
      iintro -
      iexact Hsets
    | some m0 =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc (m := KM) hk).1 $$ Hsets with ⟨Hset, Hsets⟩
      ihave Hset' := Hset
      iunfold mvcc.ownWatcherSet at Hset'
      ihave %Hm0 := ownMap_not_nil _ _ _ $$ Hset'
      isplitl [Hset']
      · iunfold mvcc.ownWatcherSetOpt; iright; iunfold mvcc.ownWatcherSet; iexact Hset'
      iintro H
      iunfold mvcc.ownWatcherSetOpt at H
      icases H with (%Hnil | H)
      · exact absurd Hnil.1 Hm0
      iapply Hsets $$ H
  icases Hopt with ⟨Hopt, Hback⟩
  wp_method_call
  wp_call
  wp_load
  ihave Hret : mvcc.ownWatcherSet mret ∅ $$ [Hret]
  · iunfold mvcc.ownWatcherSet; iexact Hret
  wp_apply hUnion $$ [$Hret $Hopt] as ⟨Hret, Hopt⟩
  · ipureintro; exact GMap.map_disjoint_empty_l _
  ihave Hsets := Hback $$ Hopt
  rw [GMap.mapEmpty_union, ← mvcc.coverUpTo_nil]
  -- the ranges' sets: those of the overlapping entries (the stabbed ones), and the others
  have HStf : adt.stab (key, key ++ go!"\x00") L =
      L.filter (fun z => decide (adt.ivlCmp (key, key ++ go!"\x00") z.1 = 0)) := rfl
  have HStnd : ((adt.stab (key, key ++ go!"\x00") L).map Prod.fst).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup (mvcc.sorted_nodup L HL.1)
  generalize HStdef : adt.stab (key, key ++ go!"\x00") L = St at Hcov Hlen HStf HStnd ⊢
  icases (BigSepL.bigSepL_perm (List.filter_append_perm
      (fun z => decide (adt.ivlCmp (key, key ++ go!"\x00") z.1 = 0)) L)).2 $$ Hranges with Hranges
  icases BigSepL.bigSepL_append.1 $$ Hranges with ⟨HSt, Hothers⟩
  rw [← HStf]
  have HpsLen : ps.length = St.length := Hlen
  ihave HI : iprop(∃ (j : w64) (itv : Loc),
      "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ itv ∗ "ret" ∷ ret_ptr ↦ mret ∗
      "Hps" ∷ ivs ↦* ps ∗ "HSt" ∷ ([∗list] z ∈ St, mvcc.rangeSet W z) ∗
      "Hret" ∷ mvcc.ownWatcherSet mret
        (mvcc.coverUpTo W key ((St.take (sint.nat j)).map Prod.fst)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ St.length⌝) $$ [i item ret Hps HSt Hret]
  · have h0' : (List.take (sint.nat (W64 0)) St).map Prod.fst = [] := by simp
    iexists W64 0, _
    simp only [named]
    rw [h0']
    iframe
    ipureintro; exact ⟨by decide, Nat.zero_le _⟩
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z ivs.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hjl : sint.nat j < St.length := by
      have := Hsl.1; rw [HpsLen] at this; word
    obtain ⟨pj, hpj⟩ : ∃ pj, ps[sint.nat j]? = some pj :=
      ⟨_, List.getElem?_eq_getElem (by rw [HpsLen]; exact hjl)⟩
    obtain ⟨zj, hzj⟩ : ∃ zj, St[sint.nat j]? = some zj := ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ivs.len from ⟨Hj.1, Hlt⟩)]
    wp_apply wp_load_slice_index ivs (sint.Z j) ps _ pj Hj.1 $$ [Hps] as Hps
    · iframe Hps; ipureintro; exact hpj
    have hzip : (ps.zip St)[sint.nat j]? = some (pj, zj) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hpj, hzj⟩
    icases (BigSepL.bigSepL_lookup_acc hzip).1 $$ Hpts with ⟨⟨%Hpn, #Hpv⟩, -⟩
    icases mvcc.iv_split pj _ _ $$ Hpv with ⟨-, #Hval⟩
    icases (BigSepL.bigSepL_lookup_acc hzj).1 $$ HSt with ⟨Hz, HSt⟩
    iunfold mvcc.rangeSet at Hz
    icases Hz with ⟨%m, %Hz2, Hm⟩
    wp_auto
    rw [Hz2]
    wp_auto
    wp_method_call
    wp_call
    wp_load
    have hnotin : zj.1 ∉ (St.take (sint.nat j)).map Prod.fst := by
      intro hm
      obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
      obtain ⟨k, hk, hky⟩ := List.getElem_of_mem hy
      rw [List.getElem_take] at hky
      have hk' : (St.map Prod.fst)[k]? = some zj.1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem (by simp at hk; omega)]; simp [hky, hy1]
      have hj' : (St.map Prod.fst)[sint.nat j]? = some zj.1 := by
        rw [List.getElem?_map, hzj]; rfl
      have := list_nodup_getElem?_inj _ HStnd k (sint.nat j) zj.1 hk' hj'
      simp at hk; omega
    iunfold mvcc.ownWatcherSet at Hm
    ihave %Hmn := ownMap_not_nil _ _ _ $$ Hm
    ihave Hm : mvcc.ownWatcherSetOpt m (mvcc.ivlMembers W zj.1) $$ [Hm]
    · iunfold mvcc.ownWatcherSetOpt; iright; iunfold mvcc.ownWatcherSet; iexact Hm
    wp_apply hUnion $$ [$Hret $Hm] as ⟨Hret, Hm⟩
    · ipureintro; exact mvcc.coverUpTo_disjoint W key _ _ hnotin
    iunfold mvcc.ownWatcherSetOpt at Hm
    icases Hm with (%Hnil | Hm)
    · exact absurd Hnil.1 Hmn
    ihave HSt := HSt $$ [Hm]
    · iunfold mvcc.rangeSet; iexists m; iframe Hm; ipureintro; exact Hz2
    have hset : St.set (sint.nat j) zj = St := by
      obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hzj; exact List.set_getElem_self h
    rw [hset, ← mvcc.coverUpTo_snoc]
    have htake : (St.take (sint.nat j)).map Prod.fst ++ [zj.1] =
        (St.take (sint.nat (j + W64 1))).map Prod.fst := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hzj]; simp
    rw [htake]
    wp_for_post
    iframe
    iexists j + W64 1, pj
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  · have hjl : sint.nat j = St.length := by
      have := Hsl.1; rw [HpsLen] at this; word
    rw [hjl, List.take_length, Hcov]
    iapply HΦ
    isplitl [Hret]
    · iunfold mvcc.ownWatcherSetOpt; iright; iexact Hret
    iintro -
    iapply mvcc.ownWatcherGroup_intro wg W km ws t KM L HL
    iframe Hwg Hws Hfixed Hivt
    isplitl [Hkm Hsets]
    · iunfold mvcc.ownKeyMap
      iframe Hkm Hsets
      ipureintro; exact Hdom
    iapply (BigSepL.bigSepL_perm (List.filter_append_perm
      (fun z => decide (adt.ivlCmp (key, key ++ go!"\x00") z.1 = 0)) L)).1
    iapply BigSepL.bigSepL_append.2
    rw [← HStf]
    iframe HSt Hothers

end proof

end EtcdGrove
end Perennial
