/-
Proof of `Spec/.../mvcc/watcherSetByKey__delete.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherSetByKey__delete

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

theorem mvcc.watcherSetByKey.delete.wp_proof :
    mvcc.watcherSetByKey.delete.spec (GF := GF) (hG := hG) := by
  intro km KM W wa r fcs
  wp_start as ⟨Hkm, #Hfix, %Hpre⟩
  obtain ⟨Hend, Hwa⟩ := Hpre
  iunfold mvcc.ownKeyMap at Hkm
  icases Hkm with ⟨Hkm, %Hdom, Hsets⟩
  iunfold mvcc.watcherFixed at Hfix
  icases Hfix with ⟨%Hnn, %ks, %es, #Hk, #Hks, #He, #Hes, #Hs, #Hi, #Hf⟩
  wp_auto
  wp_apply wp_bytes_to_string ks r.key DFrac.discard $$ [$Hks] as -
  wp_apply wp_map_lookup2 $$ Hkm as Hkm
  -- `wa` in no key set but its own key's
  have Hin : ∀ k, (mvcc.keyMembers W k !! wa).isSome = true → W !! wa = some r ∧ k = r.key := by
    intro k hk
    obtain ⟨r', hr', hp⟩ := (mvcc.mem_membersBy W _ wa).1 hk
    rcases Hwa with h | h
    · rw [h] at hr'; cases hr'
    · rw [h] at hr'; cases hr'; simp at hp; exact ⟨h, hp.2.symm⟩
  -- the key map without `wa`, for the sets left unchanged
  have Hsame : ∀ k S, mvcc.keyMembers W k = S → (S !! wa).isSome = false →
      mvcc.keyMembers (GMap.delete wa W) k = S := by
    intro k S hS hn
    rw [mvcc.keyMembers_delete, hS]
    apply GMap.delete_notin
    cases h : S !! wa
    · rfl
    · rw [h] at hn; cases hn
  cases hk : KM !! r.key with
  | none =>
    simp only [Option.isSome_none, decide_false, Bool.false_eq_true]
    have HwaN : W !! wa = none := by
      rcases Hwa with h | h
      · exact h
      · exfalso
        have := (Hdom r.key).2 ⟨wa, r, h, Hend, rfl⟩
        rw [hk] at this; cases this
    wp_auto
    rw [HwaN, Option.isSome_none]
    iapply HΦ
    iexists KM
    iunfold mvcc.ownKeyMap
    iframe Hkm
    rw [GMap.delete_notin _ _ HwaN]
    iframe Hsets
    ipureintro; exact Hdom
  | some m0 =>
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    icases (BigSepM.bigSepM_delete (m := KM) hk).1 $$ Hsets with ⟨Hset, Hsets⟩
    iunfold mvcc.ownWatcherSet at Hset
    wp_auto
    wp_apply wp_map_lookup2 $$ Hset as Hset
    rcases Hwa with HwaN | HwaS
    · -- not a member: nothing changes
      have Hn : (mvcc.keyMembers W r.key !! wa).isSome = false := by
        rw [mvcc.keyMembers, mvcc.membersBy_lookup, HwaN]; rfl
      simp only [HwaN, Option.filter_none, Option.map_none, Option.isSome_none,
        Bool.false_eq_true, _root_.decide_false]
      wp_auto
      iapply HΦ
      iexists KM
      iunfold mvcc.ownKeyMap
      iframe Hkm
      rw [GMap.delete_notin _ _ HwaN]
      isplitl []
      · ipureintro; exact Hdom
      iapply (BigSepM.bigSepM_delete (m := KM) hk).2
      iframe Hsets
      iunfold mvcc.ownWatcherSet
      iexact Hset
    · have Hy : (mvcc.keyMembers W r.key !! wa).isSome = true := by
        rw [mvcc.keyMembers, mvcc.membersBy_lookup, HwaS]; simp [Hend]
      simp only [HwaS, Option.filter_some, Hend, _root_.decide_true, Bool.true_and,
        Option.map_some, Option.isSome_some, ite_true]
      wp_auto
      rw [go.delete_underlying, go.is_underlying (t := watcherSet.ty)]
      wp_apply wp_mapDelete $$ Hset as Hset
      wp_apply wp_map_len_lt $$ Hset as ⟨Hset, %Hlt⟩
      -- the sets of the other keys do not hold `wa`
      have Hothers : ∀ k, k ≠ r.key →
          mvcc.keyMembers (GMap.delete wa W) k = mvcc.keyMembers W k := by
        intro k hne
        apply Hsame k _ rfl
        cases h : (mvcc.keyMembers W k !! wa).isSome
        · rfl
        · exact absurd (Hin k h).2 hne
      have Hrest : ([∗map] k ↦ v ∈ Iris.Std.PartialMap.delete KM r.key,
            mvcc.ownWatcherSet (GF := GF) v (mvcc.keyMembers W k)) ⊢
          [∗map] k ↦ v ∈ Iris.Std.PartialMap.delete KM r.key,
            mvcc.ownWatcherSet v (mvcc.keyMembers (GMap.delete wa W) k) := by
        apply BigSepM.bigSepM_mono
        intro k v hkv
        have hne : k ≠ r.key := by
          rintro rfl
          exact absurd hkv (by simp [Iris.Std.PartialMap.get?, Iris.Std.PartialMap.delete])
        rw [Hothers k hne]
      ihave Hsets := Hrest $$ Hsets
      have HW'k : ∀ k, k ≠ r.key → ((∃ w r', (GMap.delete wa W) !! w = some r' ∧
          r'.end? = none ∧ r'.key = k) ↔ ∃ w r', W !! w = some r' ∧ r'.end? = none ∧ r'.key = k) := by
        intro k hne
        constructor
        · rintro ⟨w, r', hw, he, hk⟩
          by_cases hww : w = wa
          · subst hww; rw [GMap.lookup_delete] at hw; cases hw
          · rw [GMap.lookup_delete_ne _ (Ne.symm hww)] at hw; exact ⟨w, r', hw, he, hk⟩
        · rintro ⟨w, r', hw, he, hk⟩
          by_cases hww : w = wa
          · subst hww; rw [HwaS] at hw; cases hw; exact absurd hk.symm hne
          · rw [← GMap.lookup_delete_ne _ (Ne.symm hww)] at hw; exact ⟨w, r', hw, he, hk⟩
      rw [← mvcc.keyMembers_delete]
      wp_if_destruct
      · -- the set is empty now: its key goes
        rw [go.delete_underlying, go.is_underlying (t := watcherSetByKey.ty)]
        wp_apply wp_mapDelete $$ Hkm as Hkm
        iapply HΦ
        iexists (GMap.delete r.key KM)
        iunfold mvcc.ownKeyMap
        iframe Hkm Hsets
        ipureintro
        rw [← mvcc.keyMembers_delete] at Hlt
        have H0 : GMap.size (mvcc.keyMembers (GMap.delete wa W) r.key) = 0 := by word
        rw [GMap.map_size_empty_iff, mvcc.keyMembers_empty_iff] at H0
        intro k
        by_cases hkk : k = r.key
        · subst hkk
          rw [GMap.lookup_delete]
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          exact H0
        · rw [GMap.lookup_delete_ne _ (Ne.symm hkk), Hdom k, HW'k k hkk]
      · iapply HΦ
        iexists KM
        iunfold mvcc.ownKeyMap
        iframe Hkm
        isplitl []
        · ipureintro
          have H0 : GMap.size (mvcc.keyMembers (GMap.delete wa W) r.key) ≠ 0 := by
            intro h; apply Hif; rw [h]; rfl
          rw [ne_eq, GMap.map_size_empty_iff, mvcc.keyMembers_empty_iff, Classical.not_not] at H0
          intro k
          by_cases hkk : k = r.key
          · subst hkk
            rw [hk]
            simp only [Option.isSome_some, true_iff]
            exact H0
          · rw [Hdom k, HW'k k hkk]
        iapply (BigSepM.bigSepM_delete (m := KM) hk).2
        iframe Hsets
        iunfold mvcc.ownWatcherSet
        iexact Hset

end proof

end EtcdGrove
end Perennial
