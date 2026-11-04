/-
`shared.reindex()` (U2 internal): the cache rebuilt from the free ids (obtained back
through the interface, `freePageIds`) and the pending ids.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.reindex()`: the cache becomes exactly the free and pending ids. -/
abbrev shared.reindex.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (c : GMap w64 Unit), fl.WFw →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownShC s I.iface fl c ∗ I.own fl.free }}
    (App (Val #(methods (go.GoType.PointerType shared.ty)
      go!"reindex" #s)) (Val #()))
  {{ RET #(); ownShW s I.iface fl ∗ I.own fl.free }}

theorem shared.reindex.wp_proof (I : FLImpl (GF := GF)) (hF : I.FreePageIdsSpec) :
    shared.reindex.spec I := by
  intro s fl c Hwf
  wp_start as ⟨Hsh, Hown⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hpds
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply (hF fl.free) $$ [Hown] as %r ⟨Hr, Hback⟩
  · iframe
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_map_make2 (K := w64) (V := Unit)) as %mc Hmc
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  ihave IH : iprop(∃ (n idv : w64) (cm : GMap w64 Unit),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ idv ∗ "Hmc" ∷ mc ↦$ cm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fl.free.length : Int) ∧
        ∀ x, (cm !! x).isSome ↔ x ∈ fl.free.take (sint.nat n)⌝) $$ [i id Hmc]
  · iexists W64 0, _, ∅
    iframe
    ipureintro
    refine ⟨by word, by word, fun x => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat n < fl.free.length := by word
    list_elem fl.free (sint.nat n) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index r (sint.Z n) fl.free _ e Hn.1 $$ [Hr] with Hr
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_apply wp_mapInsert $$ Hmc as Hmc
    wp_for_post
    iframe
    iexists n + W64 1, e, <[e := ()]> cm
    iframe
    ipureintro
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    refine ⟨by word, by word, fun x => ?_⟩
    rw [hn1, List.take_add_one, He_lookup]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton]
    by_cases hx : x = e
    · subst hx; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      simp [hx, Hn.2.2 x]
  have Hall : sint.nat n = fl.free.length := by word
  rw [Hall, List.take_length] at Hn
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (tp : Loc) (cm : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "Hpds" ∷ ([∗map] _t ↦ p;pd ∈ pp;fl.pending, ownPending p pd) ∗
      "Hmc" ∷ mc ↦$ cm ∗ "txp" ∷ txp_ptr ↦ tp ∗ "t" ∷ t_ptr ↦ s ∗
      "Hca" ∷ structFieldRef shared go!"cache" s ↦ mc ∗
      "%Hcm" ∷ ⌜∀ x, (cm !! x).isSome ↔
        x ∈ fl.free ∨ x ∈ (keys.take i.toNat).flatMap (fun t => (fl.pendingOf t).ids)⌝)) $$ Hpending
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hpds Hmc txp t Hca]
  · iexists _, cm
    simp only [Int.toNat_zero, List.take_zero, List.flatMap_nil, List.not_mem_nil, _root_.or_false]
    iframe
    ipureintro; exact ⟨Int.le_refl _, Hn.2.2⟩
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨pd, Hpd⟩ := Option.isSome_iff_exists.1
      ((Hdom key).1 (by simp only [show Std.get? pp key = some p from Hp, Option.isSome_some]))
    icases BigSepM2.bigSepM2_lookup_acc Hp Hpd $$ Hpds with ⟨Hpo, Hback2⟩
    iunfold ownPending at Hpo
    icases Hpo with ⟨%ids, %atx, Hidsf, Hids, Hidc, Hatxf, Hatx, Hatxc, Hlrb⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hids
    wp_auto
    ihave IH2 : iprop(∃ (j pid : w64) (cm' : GMap w64 Unit),
        "i" ∷ i_ptr ↦ j ∗ "pendingID" ∷ pendingID_ptr ↦ pid ∗ "Hmc" ∷ mc ↦$ cm' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pd.ids.length : Int) ∧
          ∀ x, (cm' !! x).isSome ↔ (x ∈ fl.free ∨
            x ∈ (keys.take i.toNat).flatMap (fun t => (fl.pendingOf t).ids)) ∨
            x ∈ pd.ids.take (sint.nat j)⌝) $$ [i pendingID Hmc]
    · iexists W64 0, _, cm
      iframe
      ipureintro
      refine ⟨by word, by word, fun x => ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp [Hcm x]
    wp_for IH2
    wp_if_destruct
    · have Hb : sint.nat j < pd.ids.length := by word
      list_elem pd.ids (sint.nat j) as e
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index ids (sint.Z j) pd.ids _ e Hj.1 $$ [Hids] with Hids
      · iframe; ipureintro; exact He_lookup
      try wp_auto
      wp_apply wp_mapInsert $$ Hmc as Hmc
      wp_for_post
      iframe
      iexists j + W64 1, e, <[e := ()]> cm'
      iframe
      ipureintro
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      refine ⟨by word, by word, fun x => ?_⟩
      rw [hj1, List.take_add_one, He_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      by_cases hx : x = e
      · subst hx; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx)]
        simp [hx, Hj.2.2 x]
    have Hjall : sint.nat j = pd.ids.length := by word
    rw [Hjall, List.take_length] at Hj
    ihave Hpds := Hback2 $$ [Hidsf Hids Hidc Hatxf Hatx Hatxc Hlrb]
    · iunfold ownPending; iexists ids, atx; iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists p, cm'
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    have Hpo : fl.pendingOf key = pd := by
      simp [FLPg.pendingOf, show fl.pending !! key = some pd from Hpd]
    refine ⟨by omega, fun x => ?_⟩
    rw [Htake, List.flatMap_append, Hj.2.2 x]
    simp [Hpo, or_assoc]
  iintro HP Hpending
  iNamed HP
  rw [show (GMap.size pp : Int).toNat = keys.length by omega, List.take_length] at Hcm
  have Hperm := pendingIds_perm_keys fl keys (fun k => (Hkset k).trans (Hdom k)) Hknodup
  wp_auto
  ihave Hown := Hback $$ Hr
  iapply HΦ
  iframe Hown
  iunfold ownShW
  iexists cm
  isplitl
  · iunfold ownShC
    iexists al, mc, pe, pp
    iframe
  · ipureintro
    refine ⟨fun x => ?_, Hwf⟩
    rw [Hcm x]
    simp only [FLPg.allIds, List.mem_append, Hperm.mem_iff]

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
