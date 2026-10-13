/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5b).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Panic
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

theorem mvcc.keyIndex.compact.wp_proof
    (h0 : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (h1 : zap.String.spec (GF := GF) (hG := hG))
    (h2 : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (h3 : mvcc.keyIndex.doCompact.spec (GF := GF) (hG := hG))
    (h4 : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.compact.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg atRev m A Hlg Hok Hne
  wp_start as ⟨Hki, Hm⟩
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
  wp_auto
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
      iframe Hm
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
      iframe Hm
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
    iframe Hm
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
