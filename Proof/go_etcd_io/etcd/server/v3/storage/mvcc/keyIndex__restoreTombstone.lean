/-
Proof of `Spec/.../mvcc/keyIndex__restoreTombstone.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__restoreTombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__restore

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

theorem mvcc.keyIndex.restoreTombstone.wp_proof
    (hRestore : mvcc.keyIndex.restore.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.restoreTombstone.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg main sub
  wp_start as ⟨%Hlg, Hki⟩
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, ⟨%gg, #Hgauge, #Hgspec⟩, -⟩
  iunfold gaugeSpec at Hgspec
  icases Hgspec with ⟨-, #HDec, -⟩
  wp_auto
  have hR := hRestore p gs ki lg mvcc.Rev.zero ⟨main, sub⟩ (W64 1)
  rw [show mvcc.revVal mvcc.Rev.zero = zero_val Revision from rfl,
    show mvcc.revVal ⟨main, sub⟩ = ({ Main' := main, Sub' := sub } : Revision) from rfl] at hR
  wp_apply hR $$ [Hki] as %r Hr
  · iframe Hki; ipureintro; exact Hlg
  by_cases hnil : ki.gens = []
  rotate_left
  · -- `restore` panicked
    simp only [if_neg hnil]
    icases Hr with ⟨%Hr, Hki⟩
    subst Hr
    wp_auto
    iapply HΦ
    simp only [if_neg hnil]
    iframe Hki
    try (ipureintro; trivial)
  simp only [hnil, ↓reduceIte]
  icases Hr with ⟨%Hr, %gs1, Hki⟩
  subst Hr
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  iunfold mvcc.ownGens at Hgens
  icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hgvs $Hcap $Hsl] as %gs2 ⟨Hgvs, Hcap, -⟩
  (try wp_auto)
  wp_apply HDec
  (try wp_auto)
  iapply HΦ
  simp only [hnil, ↓reduceIte]
  isplitr
  · ipureintro; trivial
  iexists gs2
  iunfold mvcc.ownKi
  simp only [mvcc.kiRestoreTombstone, mvcc.kiRestore]
  iframe Hmod Hgs
  iunfold mvcc.ownGens
  iexists (gvs ++ [zero_val generation])
  iframe Hgvs Hcap
  simp only [mvcc.kiRestore] at *
  ihave %Hgl := mvcc.ownGensL_len _ _ _ $$ Hall
  obtain ⟨gv1, rfl⟩ : ∃ gv1, gvs = [gv1] := by
    match gvs, Hgl with
    | [gv1], _ => exact ⟨gv1, rfl⟩
  simp only [List.cons_append, List.nil_append, mvcc.ownGensL]
  ihave ⟨Hg1, -⟩ : iprop(mvcc.ownGen gv1
      { ver := W64 1, created := W64 0, revs := [⟨main, sub⟩] } (DFrac.own 1) ∗ True) $$ [Hall]
  · iexact Hall
  iframe Hg1
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

end proof

end EtcdGrove
end Perennial
