/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__keep
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__doCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty

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

theorem mvcc.keyIndex.keep.wp_proof
    (h0 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h1 : mvcc.keyIndex.doCompact.spec (GF := GF) (hG := hG))
    (h2 : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.keep.spec (GF := GF) (hG := hG) := by
  intro p gs ki dq atRev m A Hok
  wp_start as ⟨Hki, Hm⟩
  wp_auto
  wp_apply (h0 p gs ki dq) $$ [Hki] as Hki
  · iframe Hki
  cases Hemp : mvcc.kiIsEmpty ki
  rotate_left
  · -- an empty key index: nothing
    wp_auto
    iapply HΦ
    simp only [mvcc.keepApply, Hemp, ↓reduceIte]
    iframe
  wp_pures
  wp_auto
  wp_apply (h1 p gs ki dq atRev m A Hok) $$ [Hki Hm] as ⟨Hki, Hm⟩
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
  have Hrr := mvcc.genWalk_range gm.revs (mvcc.pAbove atRev)
  rw [Hri'] at Hrr
  have HkA : mvcc.kiAvail atRev ki =
      if ri = -1 then none else some (gm.revs.getD ri.toNat mvcc.Rev.zero) := by
    unfold mvcc.kiAvail; simp only []; rw [Hgi, Hgd, Hri']
  have HkK : mvcc.kiKeep atRev ki =
      if ri = -1 then none
      else if gm.revs ≠ [] ∧ ri = ((gm.revs.length - 1 : Nat) : Int) ∧ gi ≠ ki.gens.length - 1 then none
      else some (gm.revs.getD ri.toNat mvcc.Rev.zero) := by
    unfold mvcc.kiKeep; rw [Hemp]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [Hgi, Hgd, Hri']
  have HkE : mvcc.keepApply A atRev ki = (match mvcc.kiAvail atRev ki with
      | none => A
      | some r => if mvcc.kiKeep atRev ki = some r then GMap.insert (mvcc.revVal r) () A
        else GMap.delete (mvcc.revVal r) (GMap.insert (mvcc.revVal r) () A)) := by
    unfold mvcc.keepApply; rw [Hemp]; rfl
  rw [HkE, HkA, HkK]
  have Hgiz : sint.Z (W64 (gi : Int)) = gi := by word
  have Hb : 0 ≤ sint.Z (W64 (gi : Int)) ∧ sint.Z (W64 (gi : Int)) < sint.Z gs.len := by word
  wp_auto
  simp only [Hb, _root_.and_self, ↓reduceIte]
  wp_auto
  icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z (W64 (gi : Int))) gm Hb.1
    (by rw [Hgiz]; exact Hgm) $$ Hgens with ⟨%gv, Hel, Hg, Hback⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
  wp_apply (h2.2 _ gv gm dq) $$ [Hel Hg] as ⟨Hel, Hg⟩
  · iframe; ipureintro; exact Hnn
  rw [Hgiz, show ((gi : Int)).toNat = gi from rfl]
  rw [Hgiz] at Hnn
  wp_if_destruct
  · -- an empty generation: nothing kept
    have He' : gm.revs = [] := by simpa using Hif
    have Hri0 : ri = -1 := by rw [← Hri', He']; rfl
    ispecialize Hback $$ %gv %gm Hel Hg
    rw [mvcc.set_same Hgm]
    iapply HΦ
    simp only [Hri0, ↓reduceIte, mvcc.availAdd]
    iframe Hm
    iunfold mvcc.ownKi
    iframe
  · -- a generation with revisions
    have Hne' : gm.revs ≠ [] := by simpa using Hif
    iunfold mvcc.ownGen at Hg
    icases Hg with ⟨%Hfields, Hrevs, Hrcap⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map] at Hrl
    have Hlpos := List.length_pos_iff.2 Hne'
    icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, -⟩
    wp_auto
    ihave Hel := mvcc.gen_combine (sliceIndexRef generation (gi : Int) gs) gv dq Hnn
      $$ [Hver Hcreated Hrevsf]
    · iframe Hver Hcreated Hrevsf
    wp_if_destruct
    · -- `revIndex == len(g.revs)-1`: the generation's last revision
      have Hc1 : ri = ((gm.revs.length - 1 : Nat) : Int) := by
        have h := Hif; rw [Hrl.1] at Hrr ⊢; word
      have Hri0 : ri ≠ -1 := by omega
      wp_if_destruct
      · -- the last generation: kept
        have Hc2 : gi = ki.gens.length - 1 := by have h := Hif; word
        have hcond : (gm.revs ≠ [] ∧ ri = ((gm.revs.length - 1 : Nat) : Int) ∧
            gi ≠ ki.gens.length - 1) = False := eq_false (fun h => h.2.2 Hc2)
        simp only [Hri0, ↓reduceIte, mvcc.availAdd, hcond]
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hrcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        iapply HΦ
        iframe Hm
        iunfold mvcc.ownKi
        iframe
      · -- not the last generation: its tombstone is taken back
        have Hc2 : gi ≠ ki.gens.length - 1 := by have h := Hif; intro h'; apply h; rw [h']; word
        obtain ⟨r, Hr⟩ : ∃ r, gm.revs[ri.toNat]? = some r :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have Hrv : (List.map mvcc.revVal gm.revs)[(sint.Z (W64 ri)).toNat]? = some (mvcc.revVal r) := by
          rw [List.getElem?_map, show (sint.Z (W64 ri)).toNat = ri.toNat by word, Hr]; rfl
        have Hrd : gm.revs.getD ri.toNat mvcc.Rev.zero = r := by
          rw [List.getD_eq_getElem?_getD, Hr]; rfl
        have Hbr : 0 ≤ sint.Z (W64 ri) ∧ sint.Z (W64 ri) < sint.Z gv.revs'.len := by
          rw [Hrl.1] at Hrr; word
        icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, -⟩
        wp_auto
        simp only [Hbr, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index gv.revs' (sint.Z (W64 ri)) _ dq (mvcc.revVal r) Hbr.1
          $$ [Hrevs] as Hrevs
        · iframe; ipureintro; exact Hrv
        wp_apply (wp_mapDelete m _ (mvcc.revVal r) Revision.ty (go.StructType [])) $$ [$Hm] as Hm
        ihave Hel := mvcc.gen_combine (sliceIndexRef generation (gi : Int) gs) gv dq Hnn
          $$ [Hver Hcreated Hrevsf]
        · iframe Hver Hcreated Hrevsf
        have hcond : (gm.revs ≠ [] ∧ ri = ((gm.revs.length - 1 : Nat) : Int) ∧
            gi ≠ ki.gens.length - 1) = True := eq_true ⟨Hne', Hc1, Hc2⟩
        simp only [Hri0, ↓reduceIte, mvcc.availAdd, hcond, Hrd, reduceCtorEq]
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hrcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        iapply HΦ
        iframe Hm
        iunfold mvcc.ownKi
        iframe
    · -- not the last revision: kept, if any
      have Hc1 : ri ≠ ((gm.revs.length - 1 : Nat) : Int) := by
        have h := Hif; intro h'; apply h; rw [h', Hrl.1]; word
      by_cases Hri0 : ri = -1
      · simp only [Hri0, ↓reduceIte, mvcc.availAdd]
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hrcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        iapply HΦ
        iframe Hm
        iunfold mvcc.ownKi
        iframe
      · have hcond : (gm.revs ≠ [] ∧ ri = ((gm.revs.length - 1 : Nat) : Int) ∧
            gi ≠ ki.gens.length - 1) = False := eq_false (fun h => Hc1 h.2.1)
        simp only [Hri0, ↓reduceIte, mvcc.availAdd, hcond]
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hrcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hrcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        iapply HΦ
        iframe Hm
        iunfold mvcc.ownKi
        iframe

end proof

end EtcdGrove
end Perennial
