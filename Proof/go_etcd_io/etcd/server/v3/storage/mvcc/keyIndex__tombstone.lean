/-
Proof of `Spec/.../mvcc/keyIndex__tombstone.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__tombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__put

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

theorem mvcc.keyIndex.tombstone.wp_proof
    (hIE : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (hGE : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG))
    (hPut : mvcc.keyIndex.put.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.tombstone.spec (GF := GF) (hG := hG) := by
  intro p gs ki lg main sub e
  wp_start as ⟨%H, Hki, #Herr⟩
  obtain ⟨Hne, Hemp, Hlt⟩ := H
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, ⟨%gg, #Hgauge, #Hgspec⟩, -, -, -, -, -⟩
  iunfold gaugeSpec at Hgspec
  icases Hgspec with ⟨-, #HDec, -⟩
  wp_auto
  wp_apply (hIE p gs ki (DFrac.own 1)) $$ [Hki] as Hki
  · iframe Hki
  rw [Hemp]
  wp_auto
  -- `ki.generations[len-1].isEmpty()`
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  have Hb : 0 ≤ sint.Z (gs.len - W64 1) ∧ sint.Z (gs.len - W64 1) < sint.Z gs.len := by
    have := List.length_pos_iff.2 Hne; word
  wp_auto
  simp only [Hb, _root_.and_self, ↓reduceIte]
  have Hidx : ki.gens[(sint.Z (gs.len - W64 1)).toNat]? = some (ki.gens.getLastD mvcc.Gen.empty) := by
    rw [show (sint.Z (gs.len - W64 1)).toNat = ki.gens.length - 1 by rw [Hlen.1]; word]
    exact mvcc.getElem?_last _ Hne
  icases mvcc.ownGens_acc_z gs ki.gens (DFrac.own 1) (sint.Z (gs.len - W64 1)) _ Hb.1 Hidx $$ Hgens
    with ⟨%gv, Hel, Hg, Hback⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
  wp_apply (hGE.2 _ gv _ (DFrac.own 1)) $$ [Hel Hg] as ⟨Hel, Hg⟩
  · iframe; ipureintro; exact Hnn
  ispecialize Hback $$ %gv %_ Hel Hg
  rw [mvcc.set_same Hidx]
  wp_if_destruct
  · -- the key is already deleted
    simp only [show mvcc.kiLastEmpty ki = true by unfold mvcc.kiLastEmpty; exact decide_eq_true Hif,
      ↓reduceIte]
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iunfold mvcc.ownKi
    iframe Hmod Hgs Hback
  · -- the tombstone's revision, then a new empty generation
    simp only [show mvcc.kiLastEmpty ki = false by unfold mvcc.kiLastEmpty; exact decide_eq_false Hif,
      Bool.false_eq_true, ↓reduceIte]
    ihave Hki : iprop(mvcc.ownKi p gs ki (DFrac.own 1)) $$ [Hmod Hgs Hback]
    · iunfold mvcc.ownKi; iframe Hmod Hgs Hback
    wp_apply (hPut p gs ki lg main sub) $$ [Hki] as ⟨%gs', Hki⟩
    · iframe Hki; ipureintro; exact Hlt
    iunfold mvcc.ownKi at Hki
    icases Hki with ⟨Hmod, Hgs, Hgens⟩
    iunfold mvcc.ownGens at Hgens
    icases Hgens with ⟨%gvs, Hgvs, Hcap, Hall⟩
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hgvs $Hcap $Hsl] as %gs'' ⟨Hgvs, Hcap, -⟩
    wp_apply HDec
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iexists gs''
    iunfold mvcc.ownKi
    simp only [mvcc.kiTombstone]
    iframe Hmod Hgs
    iunfold mvcc.ownGens
    iexists (gvs ++ [zero_val generation])
    iframe Hgvs Hcap
    iapply mvcc.ownGensL_app
    iframe Hall
    iunfold mvcc.ownGen
    rw [show (zero_val generation).revs' = slice.nil from rfl,
      show mvcc.Gen.empty.revs = [] from rfl, List.map_nil]
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil

end proof

end EtcdGrove
end Perennial
