/-
U7q (`notes/bbolt-proof-plan.md`): **the page tokens after `DeleteBucket`** (`dbk_shape`, for
`Write/DelBktPure.dbk_post`). The child's record out (`txShape_delBkt`) onto `W0`, the records
`delMid` but with the root's cache `R1` (`n` still cached: no token of `n`'s tree moves); the
materializations replayed on `W0` (`matGrow_bm`: a materialization reads no bucket cache); the
leaf's delete of `n` (`txShape_delAt`); then the un-caching of `n` (`txShape_unopen`: no entry `n`
left in the root, `Spill.entryIn_rootEnts` and `cwSame_delRoot`), which gives the final records'
view and buckets (`txShape_congrVB`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.DelBktFlvCov
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsBkt
public import Proof.go_etcd_io.bbolt.Inv.ShapeOpsMat
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneFrame

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section bm
variable [GooseExts]

/-- `Y` is `X` with bucket `bl`'s cache `bm` (and the same view and dead nodes). -/
def bmRel (bl : Loc) (bm : GMap GoString Loc) (X Y : WX) : Prop :=
  ∃ B, X.t.bs !! bl = some B ∧ Y.t.bs = X.t.bs.insert bl { B with bm := bm } ∧ Y.v = X.v ∧
    Y.t.dead = X.t.dead

/-- `nodeAdded`'s records after the step. -/
def matStep (Y : WX) (bl l : Loc) (pgid : w64) (Bn : BRec) : WX :=
  let Z := Y.setBkt bl Bn
  { Z with live := Y.live.insert l (), nloc := Y.nloc.insert l (bl, pgid.toNat) }

theorem nodeAdded_bm {X Z : WX} {bl l : Loc} {pgid : w64} {parent : Loc} (bm : GMap GoString Loc)
    (Y : WX) (h : nodeAdded X Z bl l pgid parent) (hr : bmRel bl bm X Y) :
    ∃ W, nodeAdded Y W bl l pgid parent ∧ bmRel bl bm Z W := by
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp0, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h
  obtain ⟨B0, hB0, hYbs, hYv, hYd⟩ := hr
  rw [hB] at hB0; cases hB0
  subst hX'
  have hYB : Y.t.bs !! bl = some { B with bm := bm } := by rw [hYbs, GMap.lookup_insert]
  have hs : (Y.t.objs !! l).isSome = (X.t.objs !! l).isSome := by
    apply Bool.eq_iff_iff.2
    rw [Spill.objs_isSome_iff, Spill.objs_isSome_iff, hYd]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨b, B', hB', hb⟩
      rw [hYbs] at hB'
      by_cases hbl : b = bl
      · subst hbl; rw [GMap.lookup_insert] at hB'; cases hB'; exact ⟨b, B, hB, hb⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hbl)] at hB'; exact ⟨b, B', hB', hb⟩
    · rintro ⟨b, B', hB', hb⟩
      by_cases hbl : b = bl
      · subst hbl; rw [hB] at hB'; cases hB'
        exact ⟨b, { B with bm := bm }, by rw [hYbs, GMap.lookup_insert], hb⟩
      · exact ⟨b, B', by rw [hYbs, GMap.lookup_insert_ne _ _ (Ne.symm hbl)]; exact hB', hb⟩
  have hlo' : (Y.t.objs !! l).isNone := by
    rw [← Option.not_isSome, hs, Option.not_isSome]; exact hlo
  refine ⟨matStep Y bl l pgid { B with bm := bm, nm := B.nm.insert pgid l, ns := ns', bv := bv' },
    ⟨{ B with bm := bm }, pa, pg, r, ns', bv', hYB, by rw [hYv]; exact hpg, hnm, hl0, hlo', hrb,
      hrp0, hrid, hrleaf, hru, hrs, hrcs, hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase,
      rfl⟩, ?_⟩
  refine ⟨{ B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }, GMap.lookup_insert _ _ _, ?_,
    hYv, hYd⟩
  show (Y.t.bs.insert bl _) = (X.t.bs.insert bl _).insert bl _
  rw [hYbs, GMap.insert_insert, GMap.insert_insert]

theorem matPos_bm {X Y : WX} {bl : Loc} {pgid : w64} {parent : Loc} {bm : GMap GoString Loc}
    (h : matPos X bl pgid parent) (hr : bmRel bl bm X Y) : matPos Y bl pgid parent := by
  obtain ⟨B, hB, hc⟩ := h
  obtain ⟨B0, hB0, hYbs, -, -⟩ := hr
  rw [hB] at hB0; cases hB0
  exact ⟨{ B with bm := bm }, by rw [hYbs, GMap.lookup_insert], hc⟩

/-- **Materializations replayed on another cache of their bucket.** -/
theorem matGrow_bm {X Z : WX} {bl : Loc} (bm : GMap GoString Loc) (h : matGrow X Z bl) :
    ∀ Y, bmRel bl bm X Y → ∃ W, matGrow Y W bl ∧ bmRel bl bm Z W := by
  induction h with
  | refl X bl => intro Y hr; exact ⟨Y, matGrow.refl Y bl, hr⟩
  | step X Y' Z bl l pgid parent hadd hpos _ ih =>
    intro Y hr
    obtain ⟨W1, h1, hr1⟩ := nodeAdded_bm bm Y hadd hr
    obtain ⟨W, h2, hr2⟩ := ih W1 hr1
    exact ⟨W, matGrow.step Y W1 W bl l pgid parent h1 (matPos_bm hpos hr) h2, hr2⟩

theorem bUnopen_restore (B : BRec) (bm0 : GMap GoString Loc) (n : GoString) (ns : GMap Loc NRec)
    (h : B.bm = GMap.delete n bm0) :
    bUnopen { ({ B with bm := bm0 } : BRec) with ns := ns } n = { B with ns := ns } := by
  cases B; simp only at h ⊢; rw [h]

end bm

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- `txShape` reads only the view and the buckets. -/
theorem txShape_congrVB (γ : GName) (X Y : WX) (extra : GMap Nat Unit) (hv : Y.v = X.v)
    (hbs : Y.t.bs = X.t.bs) : txShape (GF := GF) γ X extra ⊢ txShape γ Y extra := by
  unfold txShape; rw [hv, hbs]

/-- **The page tokens after `DeleteBucket`** (see the module doc). -/
theorem dbk_shape (γ : GName) (X1 X6 : WX) (c : Loc) (C R1 : BRec) (n : GoString) (D : BRec)
    (l : Loc) (B6 : BRec) (rl : NRec) (s : GoSlice) (ins : List Inode)
    (hok1 : wOK X1) (hR1 : X1.t.bs !! X1.rl = some R1) (hn : R1.bm !! n = some c)
    (hC : X1.t.bs !! c = some C) (hwr1 : wrFacts X1) (hdo1 : objsDisj X1.t)
    (hpx : pagesExt X1.v.pages) (hmg : matGrow (delMid X1 c C R1 n D) X6 X1.rl) (hok6 : wOK X6)
    (hB6 : X6.t.bs !! X1.rl = some B6) (hrl : B6.ns !! l = some rl) (hlf : leafFor X6 X1.rl n l)
    (hok7 : wOK (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)))
    (hwr7 : wrFacts (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)))
    (extra : GMap Nat Unit) :
    txShape (GF := GF) γ X1 extra ⊢
      txShape γ (X6.setNode X1.rl l (rl.withEntsU s ins (wsDelAt rl.ws n) true)) extra := by
  have hcr : c ≠ X1.rl := hwr1.2.2 R1 hR1 n c hn
  have hX5rl : (delMid X1 c C R1 n D).t.bs !! X1.rl = some (bUnopen R1 n) := by
    rw [delMid_bs, if_neg hcr, if_pos rfl]
  -- the child out, the root's cache kept
  let W0 := (delMid X1 c C R1 n D).setBkt X1.rl R1
  have hW0bs : W0.t.bs = GMap.delete c X1.t.bs := by
    apply GMap.ext; intro k
    show ((delMid X1 c C R1 n D).t.bs.insert X1.rl R1) !! k = _
    rw [GMap.lookup_delete_iff]
    by_cases hk : k = X1.rl
    · subst hk; rw [GMap.lookup_insert, if_neg hcr, hR1]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), delMid_bs, if_neg hk]
  have s1 := txShape_delBkt (GF := GF) γ X1 W0 c extra hW0bs rfl
  have hloc0 : bktLocalOK W0 X1.rl := by
    obtain ⟨hlb, R1', hR1', hcl, hk, htp, hnsl, hvw⟩ := PubW.bktLocalOK_of_wOK X1 hok1 X1.rl R1 hR1
    rw [hR1] at hR1'; cases hR1'
    refine ⟨(delMid_liveB X1 c C R1 n D X1.rl).2 ⟨Ne.symm hcr, hlb⟩, R1,
      by show ((delMid X1 c C R1 n D).t.bs.insert X1.rl R1) !! X1.rl = _; rw [GMap.lookup_insert],
      hcl, hk, htp, fun l' r' hr' => ?_, hvw⟩
    refine (delMid_live X1 c C R1 n D l').2 ⟨hnsl l' r' hr', ?_⟩
    exact hdo1 X1.rl R1 hR1 l' (by rw [hr']; rfl) c C hC hcr
  have hrel0 : bmRel X1.rl R1.bm (delMid X1 c C R1 n D) W0 := ⟨bUnopen R1 n, hX5rl, rfl, rfl, rfl⟩
  obtain ⟨W6, hmgW, hrel6⟩ := matGrow_bm R1.bm hmg W0 hrel0
  have s2 := txShape_matGrow (GF := GF) γ W0 W6 X1.rl extra hloc0 hmgW
  obtain ⟨B6', hB6', hW6bs, hW6v, -⟩ := hrel6
  rw [hB6] at hB6'; cases hB6'
  have hW6rl : W6.t.bs !! X1.rl = some { B6 with bm := R1.bm } := by
    rw [hW6bs, GMap.lookup_insert]
  -- the leaf's delete
  generalize hr' : rl.withEntsU s ins (wsDelAt rl.ws n) true = r' at hok7 hwr7 ⊢
  have s3 := txShape_delAt (GF := GF) γ W6 X1.rl l { B6 with bm := R1.bm } rl s ins n true extra
    hW6rl hrl
  rw [hr'] at s3
  let B7 : BRec := { ({ B6 with bm := R1.bm } : BRec) with ns := B6.ns.insert l r' }
  have hW7 : W6.setNode X1.rl l r' = W6.setBkt X1.rl B7 := by unfold WX.setNode; rw [hW6rl]
  have hB7 : (W6.setNode X1.rl l r').t.bs !! X1.rl = some B7 := by
    rw [hW7]; show (W6.t.bs.insert X1.rl B7) !! X1.rl = _; rw [GMap.lookup_insert]
  -- no entry `n` left in the root
  obtain ⟨-, k2, k3, -, -, -, -, k8⟩ := matGrow_keepW hmg
  have h6rl : X6.rl = X1.rl := k2
  have hbm6 : B6.bm = GMap.delete n R1.bm := by
    obtain ⟨B, hB, e⟩ := k8 X1.rl B6 hB6
    rw [hX5rl] at hB; cases hB; exact e
  have hX7 : X6.setNode X1.rl l r' = X6.setBkt X1.rl { B6 with ns := B6.ns.insert l r' } := by
    unfold WX.setNode; rw [hB6]
  have hno : ∀ v, ¬ entryIn (W6.setNode X1.rl l r').v B7 n v := by
    intro v hent
    have hent' : entryIn (X6.setNode X1.rl l r').v { B6 with ns := B6.ns.insert l r' } n v := by
      rw [hW7] at hent; rw [hX7]; show entryIn X6.v _ n v
      rw [← hW6v]; exact hent
    rw [← h6rl] at hB6 hlf hX7 hok7 hwr7 hent'
    have hrl7 : (X6.setNode X6.rl l r').rl = X6.rl := by rw [hX7]; rfl
    have hB7' : (X6.setNode X6.rl l r').t.bs !! (X6.setNode X6.rl l r').rl =
        some { B6 with ns := B6.ns.insert l r' } := by
      rw [hrl7, hX7]; show (X6.t.bs.insert X6.rl _) !! X6.rl = _; rw [GMap.lookup_insert]
    have hvw := hok7.2.2.2.2.2.2.2
    have h0R : B6.ib.root' ≠ W64 0 := hok7.1.2.1.2.2.2.2 { B6 with ns := B6.ns.insert l r' } hB7'
    have hrt := rtOK_init _ _ hok7 hvw (by rw [hB7']; rfl)
    have hpx : ∀ p pg, (X6.setNode X6.rl l r').v.pages !! p = some pg → p < 2 ^ 64 := by
      intro p pg hp
      rw [hX7] at hp
      change X6.v.pages !! p = some pg at hp
      rw [k3] at hp
      have := hpx p pg hp; omega
    obtain ⟨-, -, -, -, hmem⟩ := Spill.entryIn_rootEnts (wOK_wOKR _ hok7) hwr7.1 hB7' h0R hrt hpx
      hent'
    rw [← hr'] at hmem
    exact (cwSame_delRoot X6 c n l B6 rl s ins hok6 hB6 hrl hlf).2 v hmem
  have s4 := txShape_unopen (GF := GF) γ (W6.setNode X1.rl l r') X1.rl B7 n extra hB7 hno
  refine s1.trans (s2.trans (s3.trans (s4.trans (txShape_congrVB γ _ _ extra ?_ ?_))))
  · rw [hX7]; show X6.v = ((W6.setNode X1.rl l r').setBkt X1.rl (bUnopen B7 n)).v
    rw [hW7]; exact hW6v.symm
  · rw [hX7, hW7]
    show X6.t.bs.insert X1.rl _ = ((W6.t.bs.insert X1.rl B7).insert X1.rl (bUnopen B7 n))
    rw [hW6bs, GMap.insert_insert, GMap.insert_insert, bUnopen_restore B6 R1.bm n _ hbm6]

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
