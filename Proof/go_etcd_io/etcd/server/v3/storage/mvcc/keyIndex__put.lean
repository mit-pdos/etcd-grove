/-
Proof of `Spec/.../mvcc/keyIndex__put.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Revision__GreaterThan

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

theorem mvcc.keyIndex.put.wp_proof
    (hGT : mvcc.Revision.GreaterThan.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.put.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg main sub
  wp_start as ⟨%Hlg, %Hlt, Hki⟩
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, ⟨%gg, #Hgauge, #Hgspec⟩, -, -, -, -, -⟩
  iunfold gaugeSpec at Hgspec
  icases Hgspec with ⟨#HInc, -, -⟩
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  wp_auto
  -- `rev.GreaterThan(ki.modified)`: the method value copies `rev`, so the value method
  wp_apply (hGT { Main' := main, Sub' := sub } (mvcc.revVal ki.modified))
  rw [show mvcc.Rev.gt (mvcc.revOf { Main' := main, Sub' := sub })
    (mvcc.revOf (mvcc.revVal ki.modified)) = true from (mvcc.Rev.gt_iff _ _).2 Hlt]
  wp_auto
  -- a first generation if there is none
  wp_join iprop(∃ gs' : GoSlice,
      ki_ptr ↦ p ∗ p.[keyIndex, go!"generations"] ↦ gs' ∗
      mvcc.ownGens gs' (mvcc.gensOrEmpty ki.gens) (DFrac.own 1)) with [ki Hgs Hgens]
    as ⟨%gs', ki, Hgs, Hgens⟩
  · -- no generation yet
    have hnil : ki.gens = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    iunfold mvcc.ownGens at Hgens
    icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
    ihave %Hgl := mvcc.ownGensL_len _ _ _ $$ Hall
    rw [hnil] at Hgl
    have hgvs : gvs = [] := List.eq_nil_of_length_eq_zero Hgl
    subst hgvs
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hgvs $Hcap $Hsl] as %gs1 ⟨Hgvs, Hcap, -⟩
    wp_join_done
    iexists gs1
    iframe ki Hgs
    iunfold mvcc.ownGens
    iexists ([] ++ [zero_val generation])
    iframe Hgvs Hcap
    rw [hnil]
    simp only [List.nil_append, mvcc.gensOrEmpty, ↓reduceIte, mvcc.ownGensL]
    isplitl []
    · iunfold mvcc.ownGen
      rw [show (zero_val generation).revs' = slice.nil from rfl,
        show mvcc.Gen.empty.revs = [] from rfl, List.map_nil]
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    · itrivial
  · -- some generations already
    have hne : ki.gens ≠ [] := by
      intro h; apply Hif; rw [h] at Hlen; simp only [List.length_nil] at Hlen; word
    rw [show mvcc.gensOrEmpty ki.gens = ki.gens by simp [mvcc.gensOrEmpty, hne]]
    iexists gs
    iframe ki Hgs Hgens
  -- `g := &ki.generations[len-1]`
  ihave %Hlen' := mvcc.ownGens_len _ _ _ $$ Hgens
  have Hne := mvcc.gensOrEmpty_ne_nil ki.gens
  have Hb : 0 ≤ sint.Z (gs'.len - W64 1) ∧ sint.Z (gs'.len - W64 1) < sint.Z gs'.len := by
    have := List.length_pos_iff.2 Hne; word
  simp only [Hb, _root_.and_self, ↓reduceIte]
  wp_auto
  have Hidx : (mvcc.gensOrEmpty ki.gens)[(sint.Z (gs'.len - W64 1)).toNat]? =
      some ((mvcc.gensOrEmpty ki.gens).getLastD mvcc.Gen.empty) := by
    rw [show (sint.Z (gs'.len - W64 1)).toNat = (mvcc.gensOrEmpty ki.gens).length - 1 by
      rw [Hlen'.1]; word]
    exact mvcc.getElem?_last _ Hne
  icases mvcc.ownGens_acc_z gs' _ (DFrac.own 1) (sint.Z (gs'.len - W64 1)) _ Hb.1 Hidx $$ Hgens
    with ⟨%gv, Hel, Hg, Hback⟩
  iunfold mvcc.ownGen at Hg
  icases Hg with ⟨%Hfields, Hrevs, Hcap⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
  rw [List.length_map] at Hrlen
  icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, %Hnn⟩
  wp_pures
  wp_load
  wp_auto
  wp_if_destruct
  · -- the generation's first revision: a new key
    have hrevs : ((mvcc.gensOrEmpty ki.gens).getLastD mvcc.Gen.empty).revs = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hrlen.1, Hif]; rfl
    wp_apply HInc
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hrevs $Hcap $Hsl] as %rs' ⟨Hrevs, Hcap, -⟩
    ihave Hel' := mvcc.gen_combine' (sliceIndexRef generation (sint.Z (gs'.len - W64 1)) gs')
      _ _ _ (DFrac.own 1) Hnn $$ [Hver Hcreated Hrevsf]
    · iframe Hver Hcreated Hrevsf
    iapply HΦ
    isplitr
    · ipureintro; trivial
    iexists gs'
    iunfold mvcc.ownKi
    rw [mvcc.kiPut_modified]
    simp only [mvcc.revVal_mk]
    iframe Hmod Hgs
    rw [mvcc.kiPut_gens, ← mvcc.set_last _ _ Hne,
      show (mvcc.gensOrEmpty ki.gens).length - 1 = (sint.Z (gs'.len - W64 1)).toNat by
        rw [Hlen'.1]; word]
    iapply Hback $$ Hel'
    iunfold mvcc.ownGen
    iframe Hcap
    isplitr
    · ipureintro
      simp only [mvcc.genPut]
      exact ⟨by rw [Hfields.1], by rw [ite_eq_left hrevs]; rfl⟩
    simp only [mvcc.genPut, List.map_append, List.map_cons, List.map_nil, mvcc.revVal_mk]
    iexact Hrevs
  · -- another revision of a live key
    have hrevs : ((mvcc.gensOrEmpty ki.gens).getLastD mvcc.Gen.empty).revs ≠ [] := by
      intro h; apply Hif; rw [h] at Hrlen; simp only [List.length_nil] at Hrlen; word
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hrevs $Hcap $Hsl] as %rs' ⟨Hrevs, Hcap, -⟩
    ihave Hel' := mvcc.gen_combine' (sliceIndexRef generation (sint.Z (gs'.len - W64 1)) gs')
      _ _ _ (DFrac.own 1) Hnn $$ [Hver Hcreated Hrevsf]
    · iframe Hver Hcreated Hrevsf
    iapply HΦ
    isplitr
    · ipureintro; trivial
    iexists gs'
    iunfold mvcc.ownKi
    rw [mvcc.kiPut_modified]
    simp only [mvcc.revVal_mk]
    iframe Hmod Hgs
    rw [mvcc.kiPut_gens, ← mvcc.set_last _ _ Hne,
      show (mvcc.gensOrEmpty ki.gens).length - 1 = (sint.Z (gs'.len - W64 1)).toNat by
        rw [Hlen'.1]; word]
    iapply Hback $$ Hel'
    iunfold mvcc.ownGen
    iframe Hcap
    isplitr
    · ipureintro
      simp only [mvcc.genPut]
      exact ⟨by rw [Hfields.1], by rw [ite_eq_right hrevs]; exact Hfields.2⟩
    simp only [mvcc.genPut, List.map_append, List.map_cons, List.map_nil, mvcc.revVal_mk]
    iexact Hrevs

end proof

end EtcdGrove
end Perennial
