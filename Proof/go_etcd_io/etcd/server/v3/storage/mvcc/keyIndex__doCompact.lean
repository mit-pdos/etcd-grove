/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b; the loop of
etcd-io/etcd#22377, which walks past a tombstone at `atRev` when the key was put again in that
revision).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__doCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__walk
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isRecreatedAt

@[expose] public section

set_option linter.unusedVariables false

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

theorem mvcc.keyIndex.doCompact.wp_proof
    (h0 : mvcc.generation.walk.spec (GF := GF) (hG := hG))
    (h1 : mvcc.generation.isRecreatedAt.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.doCompact.spec (GF := GF) (hG := hG) := by
  intro p gs ki dq atRev m A Hok
  wp_start as ⟨Hki, Hm⟩
  obtain ⟨Hne, Hnonlast⟩ := Hok
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  have Hpos := List.length_pos_iff.2 Hne
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gs.len := by word
  wp_auto
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  wp_auto
  -- the scan of the generations: `doCompact` walks past those before `gi` (`SkipGen`)
  ihave IH : iprop(∃ gi : w64,
      "genIdx" ∷ genIdx_ptr ↦ gi ∗
      "g" ∷ g_ptr ↦ sliceIndexRef generation (sint.Z gi) gs ∗
      "%Hgi" ∷ ⌜0 ≤ sint.Z gi ∧ sint.Z gi < ki.gens.length ∧
        ∀ j, j < (sint.Z gi).toNat → mvcc.SkipGen atRev (ki.gens.getD j mvcc.Gen.empty)
          (ki.gens.getD (j + 1) mvcc.Gen.empty)⌝)
      $$ [genIdx g]
  · iexists W64 0
    iframe genIdx g
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro j hj
    rw [show (sint.Z (W64 0)).toNat = 0 by rfl] at hj
    omega
  wp_for IH
  wp_if_destruct
  · -- not the last generation: its tombstone
    have Hgl : sint.Z gi + 1 < ki.gens.length := by word
    obtain ⟨gm0, Hgm0⟩ : ∃ gm, ki.gens[(sint.Z gi).toNat]? = some gm :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hgd0 : ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty = gm0 := by
      simp [List.getD_eq_getElem?_getD, Hgm0]
    have Hrne : gm0.revs ≠ [] := by
      rw [← Hgd0]; exact Hnonlast _ (by omega)
    icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z gi) gm0 Hgi.1 Hgm0 $$ Hgens
      with ⟨%gv0, Hel, Hg, Hback⟩
    iunfold mvcc.ownGen at Hg
    icases Hg with ⟨%Hfields, Hrevs, Hcap⟩
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map] at Hrlen
    icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, %Hnn⟩
    have Hlast := mvcc.revs_last gm0.revs gv0.revs'.len Hrne Hrlen.1
    have HbL : 0 ≤ sint.Z (gv0.revs'.len - W64 1) ∧
        sint.Z (gv0.revs'.len - W64 1) < sint.Z gv0.revs'.len := by
      have := List.length_pos_iff.2 Hrne; word
    wp_auto
    simp only [HbL, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z (gv0.revs'.len - W64 1)) _ gv0.revs' dq _ HbL.1 Hlast
      $$ Hrevs with ⟨Hlel, Hlback⟩
    icases mvcc.rev_split _ _ _ $$ Hlel with ⟨HlMain, HlSub, %Hlnn⟩
    wp_auto
    ihave Hlel := mvcc.rev_combine (sliceIndexRef Revision (sint.Z (gv0.revs'.len - W64 1)) gv0.revs')
      _ dq Hlnn $$ [HlMain HlSub]
    · iframe HlMain HlSub
    ispecialize Hlback $$ %_ Hlel
    rw [mvcc.set_same Hlast]
    ihave Hel := mvcc.gen_combine (sliceIndexRef generation (sint.Z gi) gs) gv0 dq Hnn
      $$ [Hver Hcreated Hrevsf]
    · iframe Hver Hcreated Hrevsf
    ihave Hg : iprop(mvcc.ownGen gv0 gm0 dq) $$ [Hlback Hcap]
    · iunfold mvcc.ownGen; iframe Hlback Hcap; ipureintro; exact Hfields
    ispecialize Hback $$ %gv0 %gm0 Hel Hg
    rw [mvcc.set_same Hgm0]
    irename Hback => Hgens
    wp_if_destruct
    · -- its tombstone is above `atRev`: this generation
      have HnS : ¬ mvcc.SkipGen atRev (ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty)
          (ki.gens.getD ((sint.Z gi).toNat + 1) mvcc.Gen.empty) := by
        intro hs; have := hs.tomb_le; unfold mvcc.tombZ at this; rw [Hgd0] at this; omega
      wp_for_post
      have HcgI : mvcc.compactGenIdx atRev ki.gens = (sint.Z gi).toNat :=
        mvcc.compactGenIdx_eq atRev ki.gens _ (by omega) Hgi.2.2 (Or.inr HnS)
      obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[(sint.Z gi).toNat]? = some gm :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z gi) gm Hgi.1 Hgm $$ Hgens
        with ⟨%gv, Hel, Hg, Hback⟩
      wp_apply (h0 (sliceIndexRef generation (sint.Z gi) gs) gv gm dq _ (mvcc.pAbove atRev)
        iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) A ∗ atRev_ptr ↦ atRev)
        (fun r => iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) (GMap.insert (mvcc.revVal r) () A) ∗
          atRev_ptr ↦ atRev))) $$ [Hel Hg Hm available atRev] as ⟨Hel, Hg, Hpost⟩
      · iframe Hel Hg Hm available atRev
        iunfold mvcc.walkFnSpecR
        imodintro
        iintro %r
        wp_start as ⟨Hav, Hm, Hat⟩
        wp_auto
        wp_if_destruct
        · -- at or below `atRev`: kept
          wp_apply (wp_mapInsert Revision.ty m A r (zero_val Unit)) $$ [$Hm] as Hm
          have hp : mvcc.pAbove atRev (mvcc.revOf r) = false := by
            unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_false (by omega)
          simp only [hp, Bool.false_eq_true, ↓reduceIte, mvcc.revVal_revOf]
          iapply HΦ
          iframe
        · -- above `atRev`: on
          have hp : mvcc.pAbove atRev (mvcc.revOf r) = true := by
            unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_true (by omega)
          simp only [hp, ↓reduceIte]
          iapply HΦ
          iframe
      have Hgd : ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty = gm := by
        simp [List.getD_eq_getElem?_getD, Hgm]
      ispecialize Hback $$ %gv %gm Hel Hg
      rw [mvcc.set_same Hgm]
      have Hcr : mvcc.compactRevIdx atRev ki = mvcc.genWalk gm.revs (mvcc.pAbove atRev) := by
        unfold mvcc.compactRevIdx; rw [HcgI, Hgd]
      have Hav : mvcc.kiAvail atRev ki = if mvcc.genWalk gm.revs (mvcc.pAbove atRev) = -1 then none
          else some (gm.revs.getD (mvcc.genWalk gm.revs (mvcc.pAbove atRev)).toNat mvcc.Rev.zero) := by
        unfold mvcc.kiAvail; rw [HcgI, Hgd]
      rw [HcgI, Hcr, Hav, show W64 (((sint.Z gi).toNat : Nat) : Int) = gi by word]
      unfold mvcc.walkPost
      split
      · rename_i hw
        icases Hpost with ⟨Hav, Hm, Hat⟩
        iapply HΦ
        simp only [mvcc.availAdd]
        iframe Hm
        iunfold mvcc.ownKi
        iframe
      · rename_i hw
        icases Hpost with ⟨Hav, Hm, Hat⟩
        iapply HΦ
        simp only [mvcc.availAdd]
        iframe Hm
        iunfold mvcc.ownKi
        iframe
    · -- at or below `atRev`
      wp_if_destruct
      · -- at `atRev`: was the key put again in this revision (the next generation)?
        generalize HT : (gm0.revs.getLastD mvcc.Rev.zero).main = atRev at *
        have Hb1 : 0 ≤ sint.Z (gi + W64 1) ∧ sint.Z (gi + W64 1) < sint.Z gs.len := by word
        simp only [Hb1, _root_.and_self, ↓reduceIte]
        obtain ⟨gm1, Hgm1⟩ : ∃ gm, ki.gens[(sint.Z (gi + W64 1)).toNat]? = some gm :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        have Hgd1 : ki.gens.getD ((sint.Z gi).toNat + 1) mvcc.Gen.empty = gm1 := by
          rw [show (sint.Z gi).toNat + 1 = (sint.Z (gi + W64 1)).toNat by word,
            List.getD_eq_getElem?_getD, Hgm1]; rfl
        icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z (gi + W64 1)) gm1 Hb1.1 Hgm1 $$ Hgens
          with ⟨%gv1, Hel1, Hg1, Hback1⟩
        ihave %Hnn1 := typedPointsto_not_null _ _ _ $$ Hel1
        wp_apply (h1 _ gv1 gm1 dq atRev) $$ [Hel1 Hg1] as ⟨Hel1, Hg1⟩
        · iframe; ipureintro; exact Hnn1
        ispecialize Hback1 $$ %gv1 %gm1 Hel1 Hg1
        rw [mvcc.set_same Hgm1]
        irename Hback1 => Hgens
        wp_if_destruct
        · -- put again in this revision: the tombstone is superseded, the next generation
          have HS : mvcc.SkipGen atRev (ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty)
              (ki.gens.getD ((sint.Z gi).toNat + 1) mvcc.Gen.empty) := by
            right
            refine ⟨by unfold mvcc.tombZ; rw [Hgd0]; word, ?_⟩
            rw [Hgd1]; simpa using Hif
          have Hb1 : 0 ≤ sint.Z (gi + W64 1) ∧ sint.Z (gi + W64 1) < sint.Z gs.len := by word
          simp only [Hb1, _root_.and_self, ↓reduceIte]
          wp_auto
          wp_for_post
          iframe
          iexists gi + W64 1
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          intro j hj
          rw [show (sint.Z (gi + W64 1)).toNat = (sint.Z gi).toNat + 1 by word] at hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
          · exact Hgi.2.2 j hj
          · exact HS

        · -- not put again: this generation (the tombstone is the key's last word at `atRev`)
          have HnS : ¬ mvcc.SkipGen atRev (ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty)
              (ki.gens.getD ((sint.Z gi).toNat + 1) mvcc.Gen.empty) := by
            rintro (hs | ⟨-, hs⟩)
            · unfold mvcc.tombZ at hs; rw [Hgd0, HT] at hs; omega
            · rw [Hgd1] at hs; simp_all
          wp_for_post
          have HcgI : mvcc.compactGenIdx atRev ki.gens = (sint.Z gi).toNat :=
            mvcc.compactGenIdx_eq atRev ki.gens _ (by omega) Hgi.2.2 (Or.inr HnS)
          obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[(sint.Z gi).toNat]? = some gm :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z gi) gm Hgi.1 Hgm $$ Hgens
            with ⟨%gv, Hel, Hg, Hback⟩
          wp_apply (h0 (sliceIndexRef generation (sint.Z gi) gs) gv gm dq _ (mvcc.pAbove atRev)
            iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) A ∗ atRev_ptr ↦ atRev)
            (fun r => iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) (GMap.insert (mvcc.revVal r) () A) ∗
              atRev_ptr ↦ atRev))) $$ [Hel Hg Hm available atRev] as ⟨Hel, Hg, Hpost⟩
          · iframe Hel Hg Hm available atRev
            iunfold mvcc.walkFnSpecR
            imodintro
            iintro %r
            wp_start as ⟨Hav, Hm, Hat⟩
            wp_auto
            wp_if_destruct
            · -- at or below `atRev`: kept
              wp_apply (wp_mapInsert Revision.ty m A r (zero_val Unit)) $$ [$Hm] as Hm
              have hp : mvcc.pAbove atRev (mvcc.revOf r) = false := by
                unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_false (by omega)
              simp only [hp, Bool.false_eq_true, ↓reduceIte, mvcc.revVal_revOf]
              iapply HΦ
              iframe
            · -- above `atRev`: on
              have hp : mvcc.pAbove atRev (mvcc.revOf r) = true := by
                unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_true (by omega)
              simp only [hp, ↓reduceIte]
              iapply HΦ
              iframe
          have Hgd : ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty = gm := by
            simp [List.getD_eq_getElem?_getD, Hgm]
          ispecialize Hback $$ %gv %gm Hel Hg
          rw [mvcc.set_same Hgm]
          have Hcr : mvcc.compactRevIdx atRev ki = mvcc.genWalk gm.revs (mvcc.pAbove atRev) := by
            unfold mvcc.compactRevIdx; rw [HcgI, Hgd]
          have Hav : mvcc.kiAvail atRev ki = if mvcc.genWalk gm.revs (mvcc.pAbove atRev) = -1 then none
              else some (gm.revs.getD (mvcc.genWalk gm.revs (mvcc.pAbove atRev)).toNat mvcc.Rev.zero) := by
            unfold mvcc.kiAvail; rw [HcgI, Hgd]
          rw [HcgI, Hcr, Hav, show W64 (((sint.Z gi).toNat : Nat) : Int) = gi by word]
          unfold mvcc.walkPost
          split
          · rename_i hw
            icases Hpost with ⟨Hav, Hm, Hat⟩
            iapply HΦ
            simp only [mvcc.availAdd]
            iframe Hm
            iunfold mvcc.ownKi
            iframe
          · rename_i hw
            icases Hpost with ⟨Hav, Hm, Hat⟩
            iapply HΦ
            simp only [mvcc.availAdd]
            iframe Hm
            iunfold mvcc.ownKi
            iframe

      · -- below `atRev`: the next generation
        have HS : mvcc.SkipGen atRev (ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty)
            (ki.gens.getD ((sint.Z gi).toNat + 1) mvcc.Gen.empty) := by
          left; unfold mvcc.tombZ; rw [Hgd0]
          have : (gm0.revs.getLastD mvcc.Rev.zero).main ≠ atRev := by simpa using Hif
          have h2 : sint.Z (gm0.revs.getLastD mvcc.Rev.zero).main ≠ sint.Z atRev := fun h => this (by word)
          omega
        have Hb1 : 0 ≤ sint.Z (gi + W64 1) ∧ sint.Z (gi + W64 1) < sint.Z gs.len := by word
        simp only [Hb1, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_for_post
        iframe
        iexists gi + W64 1
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro j hj
        rw [show (sint.Z (gi + W64 1)).toNat = (sint.Z gi).toNat + 1 by word] at hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
        · exact Hgi.2.2 j hj
        · exact HS
  · -- the last generation
    have Hgi' : sint.Z gi = (ki.gens.length : Int) - 1 := by word
    have HcgI : mvcc.compactGenIdx atRev ki.gens = (sint.Z gi).toNat :=
      mvcc.compactGenIdx_eq atRev ki.gens _ (by omega) Hgi.2.2 (Or.inl (by omega))
    obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[(sint.Z gi).toNat]? = some gm :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z gi) gm Hgi.1 Hgm $$ Hgens
      with ⟨%gv, Hel, Hg, Hback⟩
    wp_apply (h0 (sliceIndexRef generation (sint.Z gi) gs) gv gm dq _ (mvcc.pAbove atRev)
      iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) A ∗ atRev_ptr ↦ atRev)
      (fun r => iprop(available_ptr ↦ m ∗ ownMap m (DFrac.own 1) (GMap.insert (mvcc.revVal r) () A) ∗
        atRev_ptr ↦ atRev))) $$ [Hel Hg Hm available atRev] as ⟨Hel, Hg, Hpost⟩
    · iframe Hel Hg Hm available atRev
      iunfold mvcc.walkFnSpecR
      imodintro
      iintro %r
      wp_start as ⟨Hav, Hm, Hat⟩
      wp_auto
      wp_if_destruct
      · -- at or below `atRev`: kept
        wp_apply (wp_mapInsert Revision.ty m A r (zero_val Unit)) $$ [$Hm] as Hm
        have hp : mvcc.pAbove atRev (mvcc.revOf r) = false := by
          unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_false (by omega)
        simp only [hp, Bool.false_eq_true, ↓reduceIte, mvcc.revVal_revOf]
        iapply HΦ
        iframe
      · -- above `atRev`: on
        have hp : mvcc.pAbove atRev (mvcc.revOf r) = true := by
          unfold mvcc.pAbove; rw [mvcc.revOf_main]; exact decide_eq_true (by omega)
        simp only [hp, ↓reduceIte]
        iapply HΦ
        iframe
    have Hgd : ki.gens.getD (sint.Z gi).toNat mvcc.Gen.empty = gm := by
      simp [List.getD_eq_getElem?_getD, Hgm]
    ispecialize Hback $$ %gv %gm Hel Hg
    rw [mvcc.set_same Hgm]
    have Hcr : mvcc.compactRevIdx atRev ki = mvcc.genWalk gm.revs (mvcc.pAbove atRev) := by
      unfold mvcc.compactRevIdx; rw [HcgI, Hgd]
    have Hav : mvcc.kiAvail atRev ki = if mvcc.genWalk gm.revs (mvcc.pAbove atRev) = -1 then none
        else some (gm.revs.getD (mvcc.genWalk gm.revs (mvcc.pAbove atRev)).toNat mvcc.Rev.zero) := by
      unfold mvcc.kiAvail; rw [HcgI, Hgd]
    rw [HcgI, Hcr, Hav, show W64 (((sint.Z gi).toNat : Nat) : Int) = gi by word]
    unfold mvcc.walkPost
    split
    · rename_i hw
      icases Hpost with ⟨Hav, Hm, Hat⟩
      iapply HΦ
      simp only [mvcc.availAdd]
      iframe Hm
      iunfold mvcc.ownKi
      iframe
    · rename_i hw
      icases Hpost with ⟨Hav, Hm, Hat⟩
      iapply HΦ
      simp only [mvcc.availAdd]
      iframe Hm
      iunfold mvcc.ownKi
      iframe

end proof

end EtcdGrove
end Perennial
