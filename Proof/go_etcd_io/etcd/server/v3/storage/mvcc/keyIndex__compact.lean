/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b; the `del` map of
etcd-io/etcd#21951).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__doCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newBucketKey

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

/-- The generations after the first `i`, dropped. -/
theorem mvcc.ownGensL_drop (dq : DFrac) : ∀ (i : Nat) (gvs : List generation) (gens : List mvcc.Gen),
    mvcc.ownGensL (GF := GF) dq gvs gens ⊢ mvcc.ownGensL dq (gvs.drop i) (gens.drop i)
  | 0, gvs, gens => by simp only [List.drop_zero]; exact .rfl
  | _ + 1, [], [] => by simp only [List.drop_nil]; exact .rfl
  | i + 1, _ :: gvs, _ :: gens => by
    simp only [mvcc.ownGensL, List.drop_succ_cons]
    iintro ⟨-, H⟩
    iapply mvcc.ownGensL_drop dq i gvs gens $$ H
  | _ + 1, [], _ :: _ => by simp only [mvcc.ownGensL]; iintro %h; exact h.elim
  | _ + 1, _ :: _, [] => by simp only [mvcc.ownGensL]; iintro %h; exact h.elim

theorem mvcc.delAdd_nil (D : GMap BucketKey Unit) : mvcc.delAdd D [] = D := rfl

theorem mvcc.delAdd_append (D : GMap BucketKey Unit) (L L' : List (mvcc.Rev × Bool)) :
    mvcc.delAdd D (L ++ L') = mvcc.delAdd (mvcc.delAdd D L) L' := by
  unfold mvcc.delAdd; rw [List.foldl_append]

theorem mvcc.delAdd_snoc (D : GMap BucketKey Unit) (L : List (mvcc.Rev × Bool)) (r : mvcc.Rev) (t : Bool) :
    mvcc.delAdd D (L ++ [(r, t)]) = GMap.insert (mvcc.bkVal r t) () (mvcc.delAdd D L) := by
  rw [mvcc.delAdd_append]; rfl

theorem mvcc.genDel_take_succ (g : mvcc.Gen) (n : Nat) (e : mvcc.Rev) (he : g.revs[n]? = some e) :
    (mvcc.genDel g).take (n + 1) = (mvcc.genDel g).take n ++ [(e, decide (n + 1 = g.revs.length))] := by
  rw [List.take_add_one]
  congr 1
  unfold mvcc.genDel
  rw [List.getElem?_map, List.getElem?_zipIdx, he]
  simp

theorem mvcc.genDel_length (g : mvcc.Gen) : (mvcc.genDel g).length = g.revs.length := by
  unfold mvcc.genDel; simp

theorem mvcc.keyIndex.compact.wp_proof
    (h0 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h1 : zap.String.spec (GF := GF) (hG := hG))
    (h2 : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (h3 : mvcc.keyIndex.doCompact.spec (GF := GF) (hG := hG))
    (h4 : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG))
    (h5 : mvcc.newBucketKey.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.compact.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg atRev m A md D Hlg Hok Hne
  wp_start as ⟨Hki, Hm, Hmd⟩
  wp_auto
  wp_apply (h0 p gs ki (DFrac.own 1)) $$ [Hki] as Hki
  · iframe Hki
  rw [Hne]
  wp_pures
  wp_auto
  wp_apply (h3 p gs ki (DFrac.own 1) atRev m A Hok) $$ [Hki Hm] as ⟨Hki, Hm⟩
  · iframe Hki Hm
  obtain ⟨Hgne, Hnonlast⟩ := Hok
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  have Hgilt := mvcc.compactGenIdx_lt atRev ki.gens Hgne
  obtain ⟨gi, Hgi⟩ : ∃ gi, mvcc.compactGenIdx atRev ki.gens = gi := ⟨_, rfl⟩
  rw [Hgi] at Hgilt ⊢
  obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[gi]? = some gm := ⟨_, List.getElem?_eq_getElem Hgilt⟩
  have Hgd : ki.gens.getD gi mvcc.Gen.empty = gm := by simp [List.getD_eq_getElem?_getD, Hgm]
  obtain ⟨ri, Hri⟩ : ∃ ri, mvcc.compactRevIdx atRev ki = ri := ⟨_, rfl⟩
  have Hri' : mvcc.genWalk gm.revs (mvcc.pAbove atRev) = ri := by
    rw [← Hri]; unfold mvcc.compactRevIdx; rw [Hgi, Hgd]
  rw [Hri]
  -- the generation compaction leaves at `gi`
  have Hkc : mvcc.kiCompact atRev ki = { ki with gens := (ki.gens.set gi
      (if gm.revs ≠ [] ∧ ri ≠ -1 then { gm with revs := gm.revs.drop ri.toNat } else gm)).drop gi } := by
    unfold mvcc.kiCompact; simp only []; rw [Hgi, Hgd, Hri']
  have Hgiz : sint.Z (W64 (gi : Int)) = gi := by word
  have Hb : 0 ≤ sint.Z (W64 (gi : Int)) ∧ sint.Z (W64 (gi : Int)) < sint.Z gs.len := by word
  -- `del != nil`: the bucket keys of the dropped revisions
  ihave %Hmdn := ownMap_not_nil _ _ _ $$ Hmd
  rw [decide_eq_false Hmdn]
  wp_auto
  ihave IH : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "Hmd" ∷ md ↦$ mvcc.delAdd D (((ki.gens.take (sint.nat i)).map mvcc.genDel).flatten) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ gi⌝) $$ [i Hmd]
  · iexists W64 0
    iframe i
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.flatten_nil,
      mvcc.delAdd_nil]
    iframe Hmd
    ipureintro; refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · -- generation `i`, before `gi`: every revision, the last a tombstone
    have Hil : (sint.Z i).toNat < ki.gens.length := by word
    obtain ⟨gm0, Hgm0⟩ : ∃ g, ki.gens[(sint.Z i).toNat]? = some g :=
      ⟨_, List.getElem?_eq_getElem Hil⟩
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z gs.len := by word
    simp only [Hbi, _root_.and_self, ↓reduceIte]
    icases mvcc.ownGens_acc_z gs ki.gens (DFrac.own 1) (sint.Z i) gm0 Hi.1 Hgm0 $$ Hgens
      with ⟨%gv0, Hel, Hg, Hback⟩
    icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, %Hnn0⟩
    iunfold mvcc.ownGen at Hg
    icases Hg with ⟨%Hfields, Hrevs, Hcap⟩
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map] at Hrlen
    irename i => Hio
    wp_auto
    ihave IH2 : iprop(∃ (n : w64) (rv : Revision) (jv : w64),
        "i" ∷ i_ptr ↦ n ∗ "r" ∷ r_ptr ↦ rv ∗ "j" ∷ j_ptr ↦ jv ∗
        "Hmd" ∷ md ↦$ mvcc.delAdd D (((ki.gens.take (sint.nat i)).map mvcc.genDel).flatten ++
          (mvcc.genDel gm0).take (sint.nat n)) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ gm0.revs.length⌝) $$ [i r j Hmd]
    · iexists W64 0, _, _
      iframe i r j
      simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
      iframe Hmd
      ipureintro; refine ⟨by word, by word⟩
    wp_for IH2
    wp_if_destruct
    · -- the revision at `n`
      have Hnl : sint.nat n < gm0.revs.length := by word
      obtain ⟨e, He⟩ : ∃ e, gm0.revs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hnl⟩
      have He' : (List.map mvcc.revVal gm0.revs)[(sint.Z n).toNat]? = some (mvcc.revVal e) := by
        rw [List.getElem?_map]; show (gm0.revs[sint.nat n]?).map _ = _; rw [He]; rfl
      have Hbn : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gv0.revs'.len := ⟨Hn.1, Hif⟩
      simp only [Hbn, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index gv0.revs' (sint.Z n) _ (DFrac.own 1) (mvcc.revVal e) Hn.1
        $$ [Hrevs] as Hrevs
      · iframe; ipureintro; exact He'
      wp_apply h5
      wp_apply (wp_mapInsert BucketKey.ty md _ _ (zero_val Unit)) $$ [$Hmd] as Hmd
      wp_for_post
      iframe
      iexists n + W64 1, _, _
      iframe
      have Ht : decide (n = gv0.revs'.len - W64 1) = decide (sint.nat n + 1 = gm0.revs.length) := by
        apply decide_eq_decide.2; constructor <;> intro h <;> word
      have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [Hn1, mvcc.genDel_take_succ gm0 _ e He, ← List.append_assoc, mvcc.delAdd_snoc, ← Ht]
      rw [show mvcc.bkVal e (decide (n = gv0.revs'.len - W64 1)) =
          BucketKey.mk (Revision.mk e.main e.sub) (decide (n = gv0.revs'.len - W64 1)) from rfl,
        show (() : Unit) = zero_val Unit from rfl]
      iframe Hmd
      ipureintro; refine ⟨by word, by word⟩
    · -- the generation done
      have Hnl : sint.nat n = (mvcc.genDel gm0).length := by rw [mvcc.genDel_length]; word
      rw [Hnl, List.take_length]
      wp_for_post
      ihave Hel := mvcc.gen_combine _ gv0 _ Hnn0 $$ [Hver Hcreated Hrevsf]
      · iframe Hver Hcreated Hrevsf
      ihave Hg : iprop(mvcc.ownGen gv0 gm0 (DFrac.own 1)) $$ [Hrevs Hcap]
      · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
      ispecialize Hback $$ %gv0 %gm0 Hel Hg
      rw [mvcc.set_same Hgm0]
      iframe
      iexists i + W64 1
      iframe
      have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [Hi1, List.take_add_one, show ki.gens[sint.nat i]? = some gm0 from Hgm0]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      iframe Hmd
      ipureintro; refine ⟨by word, by word⟩
  -- the loop is done: `i = gi`; then `doCompact`'s generation's revisions before `revIndex`
  have Higi : sint.nat i = gi := by word
  rw [Higi]
  wp_join iprop(ki_ptr ↦ p ∗ del_ptr ↦ md ∗ genIdx_ptr ↦ W64 (gi : Int) ∗ revIndex_ptr ↦ W64 ri ∗
      p.[keyIndex, go!"generations"] ↦ gs ∗ mvcc.ownGens gs ki.gens (DFrac.own 1) ∗
      md ↦$ mvcc.delAdd D (mvcc.kiDel atRev ki)) at next with [ki del genIdx revIndex Hgs Hgens Hmd]
    as ⟨ki, del, genIdx, revIndex, Hgs, Hgens, Hmd⟩
  · have Hkd : mvcc.kiDel atRev ki = ((ki.gens.take gi).map mvcc.genDel).flatten ++
        (mvcc.genCutDel atRev gm).map (fun r => (r, false)) := by
      unfold mvcc.kiDel; rw [Hgi, Hgd]
    have Hcd : mvcc.genCutDel atRev gm =
        if gm.revs ≠ [] ∧ ri ≠ -1 then gm.revs.take ri.toNat else [] := by
      unfold mvcc.genCutDel; rw [Hri']
    have Hrr := mvcc.genWalk_range gm.revs (mvcc.pAbove atRev)
    rw [Hri'] at Hrr
    rw [Hkd, Hcd]
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_auto
    icases mvcc.ownGens_acc_z gs ki.gens (DFrac.own 1) (sint.Z (W64 (gi : Int))) gm Hb.1
      (by rw [Hgiz]; exact Hgm) $$ Hgens with ⟨%gv, Hel, Hg, Hback⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
    wp_apply (h4.2 _ gv gm (DFrac.own 1)) $$ [Hel Hg] as ⟨Hel, Hg⟩
    · iframe; ipureintro; exact Hnn
    rw [Hgiz, show ((gi : Int)).toNat = gi from rfl]
    wp_if_destruct
    · -- an empty generation: nothing more
      ispecialize Hback $$ %gv %gm Hel Hg
      rw [mvcc.set_same Hgm]
      simp only [Hif, ne_eq, not_true_eq_false, false_and, ↓reduceIte, List.map_nil, List.append_nil]
      iframe
    · have Hne' : gm.revs ≠ [] := by simpa using Hif
      iunfold mvcc.ownGen at Hg
      icases Hg with ⟨%Hfields, Hrevs, Hrcap⟩
      ihave %Hrwf := ownSlice_wf _ _ _ $$ Hrevs
      ihave %Hrl := ownSlice_len _ _ _ $$ Hrevs
      rw [List.length_map] at Hrl
      have Hriz : sint.Z (W64 ri) = ri := by word
      wp_if_destruct
      · -- `revIndex > 0`: the revisions before it
        have Hri0 : 0 < ri := by rw [← Hriz]; simpa using Hif
        have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ri) ∧
            sint.Z (W64 ri) ≤ sint.Z gv.revs'.cap := by word
        simp only [Hsb, _root_.and_self, ↓reduceIte]
        have Hsk : 0 ≤ sint.Z (W64 ri) ∧ sint.Z (W64 ri) ≤ sint.Z gv.revs'.len := by word
        icases (ownSlice_split_all (W64 ri) gv.revs' _ _ Hsk).1 $$ Hrevs with ⟨Hpre, Hsuf⟩
        wp_auto
        have Hrn : sint.nat (W64 ri) = ri.toNat := by word
        rw [ite_eq_left (show gm.revs ≠ [] ∧ ri ≠ -1 from ⟨Hne', by omega⟩)]
        rw [Hrn] at *
        ihave IH3 : iprop(∃ (n : w64) (rv : Revision),
            "i" ∷ i_ptr ↦ n ∗ "r" ∷ r_ptr ↦ rv ∗
            "Hmd" ∷ md ↦$ mvcc.delAdd D (((ki.gens.take gi).map mvcc.genDel).flatten ++
              ((gm.revs.take ri.toNat).take (sint.nat n)).map (fun r => (r, false))) ∗
            "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ri.toNat⌝) $$ [i r Hmd]
        · iexists W64 0, _
          iframe i r
          simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
          iframe Hmd
          ipureintro; refine ⟨by word, by word⟩
        wp_for IH3
        wp_if_destruct
        · have Hnl : sint.nat n < ri.toNat := by word
          have Hnl' : sint.nat n < gm.revs.length := by omega
          obtain ⟨e, He⟩ : ∃ e, gm.revs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hnl'⟩
          have He2 : (gm.revs.take ri.toNat)[sint.nat n]? = some e := by
            rw [List.getElem?_take_of_lt Hnl]; exact He
          have He' : (List.take ri.toNat (List.map mvcc.revVal gm.revs))[(sint.Z n).toNat]? =
              some (mvcc.revVal e) := by
            rw [← List.map_take, List.getElem?_map]; show ((gm.revs.take ri.toNat)[sint.nat n]?).map _ = _
            rw [He2]; rfl
          have Hbn : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 ri - W64 0) := ⟨Hn.1, Hif⟩
          simp only [Hbn, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z n) _ (DFrac.own 1) (mvcc.revVal e) Hn.1
            $$ [Hpre] as Hpre
          · iframe; ipureintro; exact He'
          wp_apply h5
          wp_apply (wp_mapInsert BucketKey.ty md _ _ (zero_val Unit)) $$ [$Hmd] as Hmd
          wp_for_post
          iframe
          iexists n + W64 1, _
          iframe
          have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
          rw [Hn1, List.take_add_one, He2]
          simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
          rw [← List.append_assoc, mvcc.delAdd_snoc,
            show mvcc.bkVal e false = BucketKey.mk (Revision.mk e.main e.sub) false from rfl,
            show (() : Unit) = zero_val Unit from rfl]
          iframe Hmd
          ipureintro; refine ⟨by word, by word⟩
        · -- done: the revisions before `revIndex`
          have Hnl : sint.nat n = ri.toNat := by word
          rw [Hnl, List.take_of_length_le (List.length_take_le _ _)]
          ihave Hrevs := (ownSlice_split_all (W64 ri) gv.revs' (DFrac.own 1)
              (gm.revs.map mvcc.revVal) Hsk).2 $$ [Hpre Hsuf]
          · rw [show sint.nat (W64 ri) = ri.toNat by word]; iframe Hpre Hsuf
          ihave Hg : iprop(mvcc.ownGen gv gm (DFrac.own 1)) $$ [Hrevs Hrcap]
          · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
          ispecialize Hback $$ %gv %gm Hel Hg
          rw [mvcc.set_same Hgm]
          iframe
      · -- `revIndex ≤ 0`: none
        have Hnil : (if gm.revs ≠ [] ∧ ri ≠ -1 then List.take ri.toNat gm.revs else []) = [] := by
          have Hr0 : ri.toNat = 0 := by
            have h := Hif
            rw [Hriz] at h
            have : sint.Z (W64 0) = 0 := rfl
            omega
          split
          · rw [Hr0]; rfl
          · rfl
        rw [Hnil, List.map_nil, List.append_nil]
        ihave Hg : iprop(mvcc.ownGen gv gm (DFrac.own 1)) $$ [Hrevs Hrcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        iframe
  simp only [Hb, _root_.and_self, ↓reduceIte]
  wp_auto
  icases mvcc.ownGens_acc_z gs ki.gens (DFrac.own 1) (sint.Z (W64 (gi : Int))) gm Hb.1
    (by rw [Hgiz]; exact Hgm) $$ Hgens with ⟨%gv, Hel, Hg, Hback⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
  wp_apply (h4.2 _ gv gm (DFrac.own 1)) $$ [Hel Hg] as ⟨Hel, Hg⟩
  · iframe; ipureintro; exact Hnn
  rw [Hgiz, show ((gi : Int)).toNat = gi from rfl]
  wp_if_destruct
  rotate_left
  · -- a generation with revisions
    have Hne' : gm.revs ≠ [] := by simpa using Hif
    wp_if_destruct
    rotate_left
    · -- `revIndex != -1`: cut the generation there
      have Hri0 : ri ≠ -1 := by intro h; apply Hif; rw [h]
      have Hrr := mvcc.genWalk_range gm.revs (mvcc.pAbove atRev)
      rw [Hri'] at Hrr
      iunfold mvcc.ownGen at Hg
      icases Hg with ⟨%Hfields, Hrevs, Hrcap⟩
      ihave %Hrwf := ownSlice_wf _ _ _ $$ Hrevs
      ihave %Hrl := ownSlice_len _ _ _ $$ Hrevs
      rw [List.length_map] at Hrl
      have Hrb : 0 ≤ sint.Z (W64 ri) ∧ sint.Z (W64 ri) ≤ sint.Z gv.revs'.len ∧
          sint.Z gv.revs'.len ≤ sint.Z gv.revs'.cap := by
        refine ⟨by word, by word, Hrwf.2⟩
      simp only [Hrb, _root_.and_self, ↓reduceIte]
      wp_auto
      icases (ownSlice_split_all (W64 ri) gv.revs' _ _ ⟨Hrb.1, Hrb.2.1⟩).1 $$ Hrevs with ⟨-, Hrevs⟩
      ihave Hrcap := (ownSliceCap_slice gv.revs' (W64 ri) _ Hrb).1 $$ Hrcap
      ispecialize Hback $$ %_ %{ gm with revs := gm.revs.drop ri.toNat } Hel [Hrevs Hrcap]
      · iunfold mvcc.ownGen
        rw [List.map_drop, show sint.nat (W64 ri) = ri.toNat by word]
        iframe Hrevs Hrcap
        ipureintro; exact Hfields
      irename Hback => Hgens
      have Hc : (if gm.revs ≠ [] ∧ ri ≠ -1 then { gm with revs := gm.revs.drop ri.toNat } else gm) =
          { gm with revs := gm.revs.drop ri.toNat } := by simp [Hne', Hri0]
      rw [Hc] at Hkc
      -- `ki.generations = ki.generations[genIdx:]`
      iunfold mvcc.ownGens at Hgens
      icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
      ihave %Hgwf := ownSlice_wf _ _ _ $$ Hgvs
      ihave %Hgl := ownSlice_len _ _ _ $$ Hgvs
      ihave %HlenL := mvcc.ownGensL_len _ _ _ $$ Hall
      have Hsb : 0 ≤ sint.Z (W64 (gi : Int)) ∧ sint.Z (W64 (gi : Int)) ≤ sint.Z gs.len ∧
          sint.Z gs.len ≤ sint.Z gs.cap := by
        rw [Hgiz]; refine ⟨by omega, ?_, Hgwf.2⟩; have := Hlen.1; word
      simp only [Hsb, _root_.and_self, ↓reduceIte]
      wp_auto
      icases (ownSlice_split_all (W64 (gi : Int)) gs _ gvs ⟨Hsb.1, Hsb.2.1⟩).1 $$ Hgvs with ⟨-, Hgvs⟩
      ihave Hcap := (ownSliceCap_slice gs (W64 (gi : Int)) _ Hsb).1 $$ Hcap
      ihave Hall := mvcc.ownGensL_drop (DFrac.own 1) gi _ _ $$ Hall
      iapply HΦ
      iframe Hm Hmd
      iexists slice.slice gs generation (W64 (gi : Int)) gs.len
      rw [Hkc]
      iunfold mvcc.ownKi
      iframe Hmod Hgs
      iunfold mvcc.ownGens
      iexists gvs.drop gi
      rw [show sint.nat (W64 (gi : Int)) = gi by word]
      iframe Hgvs Hcap Hall
    · -- `revIndex == -1`: nothing to cut
      iunfold mvcc.ownGen at Hg
      icases Hg with ⟨%Hfields, Hrevs, Hrcap⟩
      ihave %Hrl := ownSlice_len _ _ _ $$ Hrevs
      rw [List.length_map] at Hrl
      ihave Hg : iprop(mvcc.ownGen gv gm (DFrac.own 1)) $$ [Hrevs Hrcap]
      · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
      have Hri0 : ri = -1 := by
        have Hrr := mvcc.genWalk_range gm.revs (mvcc.pAbove atRev)
        rw [Hri'] at Hrr
        have h2 := Hif
        word
      ispecialize Hback $$ %gv %gm Hel Hg
      rw [mvcc.set_same Hgm]
      irename Hback => Hgens
      have Hc : (if gm.revs ≠ [] ∧ ri ≠ -1 then { gm with revs := gm.revs.drop ri.toNat } else gm) = gm :=
        by simp [Hri0]
      rw [Hc, mvcc.set_same Hgm] at Hkc
      -- `ki.generations = ki.generations[genIdx:]`
      iunfold mvcc.ownGens at Hgens
      icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
      ihave %Hgwf := ownSlice_wf _ _ _ $$ Hgvs
      ihave %Hgl := ownSlice_len _ _ _ $$ Hgvs
      ihave %HlenL := mvcc.ownGensL_len _ _ _ $$ Hall
      have Hsb : 0 ≤ sint.Z (W64 (gi : Int)) ∧ sint.Z (W64 (gi : Int)) ≤ sint.Z gs.len ∧
          sint.Z gs.len ≤ sint.Z gs.cap := by
        rw [Hgiz]; refine ⟨by omega, ?_, Hgwf.2⟩; have := Hlen.1; word
      simp only [Hsb, _root_.and_self, ↓reduceIte]
      wp_auto
      icases (ownSlice_split_all (W64 (gi : Int)) gs _ gvs ⟨Hsb.1, Hsb.2.1⟩).1 $$ Hgvs with ⟨-, Hgvs⟩
      ihave Hcap := (ownSliceCap_slice gs (W64 (gi : Int)) _ Hsb).1 $$ Hcap
      ihave Hall := mvcc.ownGensL_drop (DFrac.own 1) gi _ _ $$ Hall
      iapply HΦ
      iframe Hm Hmd
      iexists slice.slice gs generation (W64 (gi : Int)) gs.len
      rw [Hkc]
      iunfold mvcc.ownKi
      iframe Hmod Hgs
      iunfold mvcc.ownGens
      iexists gvs.drop gi
      rw [show sint.nat (W64 (gi : Int)) = gi by word]
      iframe Hgvs Hcap Hall
  · -- an empty generation: nothing to cut
    have He' : gm.revs = [] := by simpa using Hif
    ispecialize Hback $$ %gv %gm Hel Hg
    rw [mvcc.set_same Hgm]
    irename Hback => Hgens
    have Hc : (if gm.revs ≠ [] ∧ ri ≠ -1 then { gm with revs := gm.revs.drop ri.toNat } else gm) = gm :=
      by simp [He']
    rw [Hc, mvcc.set_same Hgm] at Hkc
    -- `ki.generations = ki.generations[genIdx:]`
    iunfold mvcc.ownGens at Hgens
    icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
    ihave %Hgwf := ownSlice_wf _ _ _ $$ Hgvs
    ihave %Hgl := ownSlice_len _ _ _ $$ Hgvs
    ihave %HlenL := mvcc.ownGensL_len _ _ _ $$ Hall
    have Hsb : 0 ≤ sint.Z (W64 (gi : Int)) ∧ sint.Z (W64 (gi : Int)) ≤ sint.Z gs.len ∧
        sint.Z gs.len ≤ sint.Z gs.cap := by
      rw [Hgiz]; refine ⟨by omega, ?_, Hgwf.2⟩; have := Hlen.1; word
    simp only [Hsb, _root_.and_self, ↓reduceIte]
    wp_auto
    icases (ownSlice_split_all (W64 (gi : Int)) gs _ gvs ⟨Hsb.1, Hsb.2.1⟩).1 $$ Hgvs with ⟨-, Hgvs⟩
    ihave Hcap := (ownSliceCap_slice gs (W64 (gi : Int)) _ Hsb).1 $$ Hcap
    ihave Hall := mvcc.ownGensL_drop (DFrac.own 1) gi _ _ $$ Hall
    iapply HΦ
    iframe Hm Hmd
    iexists slice.slice gs generation (W64 (gi : Int)) gs.len
    rw [Hkc]
    iunfold mvcc.ownKi
    iframe Hmod Hgs
    iunfold mvcc.ownGens
    iexists gvs.drop gi
    rw [show sint.nat (W64 (gi : Int)) = gi by word]
    iframe Hgvs Hcap Hall

end proof

end EtcdGrove
end Perennial
