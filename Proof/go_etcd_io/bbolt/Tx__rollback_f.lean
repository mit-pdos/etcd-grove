/-
The proof of `Tx.rollback_f.spec` (`Proof/go_etcd_io/bbolt/Commit/RollbackFSpec.lean`; maintainer 11):
`Tx.rollback.wp_proof`'s proof (`Tx__rollback.lean`) over `wtxEnd' fr`: the writer's `fbTok` goes
to `store_rollback`, whose returned bytes of the freed synced freelist page are the recorded ones
(`wdb_rollback_f`, `Commit/RollbackFlag`); with the flag the writer has not published. Also
`Tx.rollback.spec_of_f` (`Tx.rollback.spec` from it, at `fr = false`). The helpers are
`Tx__rollback.lean`'s, renamed (`rb…`), so that that module may import this one.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFSpec
public import Proof.go_etcd_io.bbolt.Commit.RollbackFlag
public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Commit.RollbackReload
public import Spec.go_etcd_io.bbolt.Tx__close_w
public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.DB__freepages
public import Spec.go_etcd_io.bbolt.DB__page
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Rollback
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Reload
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__NoSyncReload
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
/-- The writer's fields `rollback` reads (`tx.db`, `tx.writable`, `tx.meta` and the meta), out of
its records, mapped or lost, and back. -/
theorem rbWtxEL_fields (K : BC) (tx : Loc) (r : TxReg) (X : WX) :
    (wtxW (GF := GF) K tx r false X ∨ wtxLost K tx r false X) ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ ⌜r.db = K.db⌝ ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗
      tx.[Tx, go!"writable"] ↦ X.t.t.writable' ∗ tx.[Tx, go!"meta"] ↦ X.t.t.meta' ∗
      X.t.t.meta' ↦ X.t.mv ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗
        tx.[Tx, go!"writable"] ↦ X.t.t.writable' -∗ tx.[Tx, go!"meta"] ↦ X.t.t.meta' -∗
        X.t.t.meta' ↦ X.t.mv -∗ (wtxW K tx r false X ∨ wtxLost K tx r false X)) := by
  unfold wtxW wtxLost wtxCore wtxHeap txFields
  iintro (⟨⟨#Hpkg, #Hkc, %Hc, #Hreg, ⟨%Hhok, ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, Hmv, Hpm, Hbufs⟩,
      Hrf, Hobj, Hbobj⟩, Hfills, Hbk, Hnl, Hdb, Hvo, Hstok⟩, Hvc, Hmf⟩ |
    ⟨⟨#Hpkg, #Hkc, %Hc, #Hreg, ⟨%Hhok, ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, Hmv, Hpm, Hbufs⟩,
      Hrf, Hobj, Hbobj⟩, Hfills, Hbk, Hnl, Hdb, Hvo, Hstok⟩, Hmf⟩)
  · iframe Hdb Hwr Hme Hmv
    iframe #
    isplitr
    · ipureintro; exact Hc.1
    iintro Hdb Hwr Hme Hmv
    ileft
    iframe
    iframe #
    ipureintro; exact ⟨Hc, Hhok⟩
  · iframe Hdb Hwr Hme Hmv
    iframe #
    isplitr
    · ipureintro; exact Hc.1
    iintro Hdb Hwr Hme Hmv
    iright
    iframe
    iframe #
    ipureintro; exact ⟨Hc, Hhok⟩

/-- The mapping's data pointer (`nil` unmapped). -/
def rbDataOf : MapSt → Loc
  | some (b, _) => b
  | none => null

omit package_sem hos in
/-- `db.data` out of the mapping fields, and back. -/
theorem rbMapFields_data (db : Loc) (dq : DFrac) (ms : MapSt) :
    mapFields (GF := GF) db dq ms ⊢ db.[DB, go!"data"] ↦{dq} rbDataOf ms ∗
      ⌜∀ b l, ms = some (b, l) → 0 < b.addr⌝ ∗
      (db.[DB, go!"data"] ↦{dq} rbDataOf ms -∗ mapFields db dq ms) := by
  rcases ms with _ | ⟨b, l⟩
  · simp only [mapFields, rbDataOf]
    iintro ⟨Hr, Hd, H0, H1⟩
    iframe Hd
    isplitr
    · ipureintro; intro b l h; cases h
    iintro Hd; iframe
  · simp only [mapFields, rbDataOf]
    iintro ⟨Hr, Hd, H0, H1, %h⟩
    iframe Hd
    isplitr
    · ipureintro; intro b' l' e; cases e; exact h.2.1
    iintro Hd; iframe; ipureintro; exact h

omit package_sem hos in
theorem rbMetaCellsQ_some (q : Qp) (b : Loc) (l : Nat) (C : CommitSt) :
    metaCellsQ (GF := GF) q (some (b, l) : MapSt) C =
      iprop(bytesPointsto b (DFrac.own q) C.m0 ∗ bytesPointsto (b +ₗ (4096 : Int)) (DFrac.own q) C.m1) :=
  rfl

/-- **`db.meta().Txid()`** (as `DB.hasSyncedFreelist`'s proof): the current meta's txid. -/
theorem rbWp_meta_Txid (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
        metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) @!! go.GoType.PointerType Meta.ty
        @!! go!"Txid")) (Val #()))
    {{ RET #(W64 (C.txid : Int)); metaCellsQ q (some (b, l) : MapSt) C }} := by
  iintro %Φ ⟨#Hpkc, Hmc⟩ HΦ
  obtain ⟨hl0, hl1, -, -, -, -, ⟨htx, -, -, -⟩, -⟩ := hok
  have htx' : ∀ v : Meta, v.txid'.toNat = C.txid → v.txid' = W64 (C.txid : Int) := by
    intro v hv; apply BitVec.eq_of_toNat_eq; rw [← hv]; simp
  simp only [metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at htx
    simp only [hT, ↓reduceIte] at htx
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    rw [← htx' _ htx]
    generalize metaOf C.m0 = v0
    wp_apply wp_Txid _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at htx
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at htx
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    rw [← htx' _ htx]
    generalize metaOf C.m1 = v1
    wp_apply wp_Txid _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

theorem Tx.rollback_f.wp_proof
    (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_Freelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (wp_FlRollback : internal.freelist.Interface.Rollback.spec (GF := GF) (hG := hG))
    (wp_hasSynced : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (wp_freepages : DB.freepages.spec (GF := GF) (hG := hG))
    (wp_NSR : internal.freelist.Interface.NoSyncReload.spec (GF := GF) (hG := hG))
    (wp_Reload : internal.freelist.Interface.Reload.spec (GF := GF) (hG := hG))
    (wp_page : DB.page.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_w.spec (GF := GF) (hG := hG)) :
    Tx.rollback_f.spec (GF := GF) (hG := hG) := by
  intro _ fr K tx r X ws w hrb hpbf
  obtain ⟨v, wt, pb, wl, rfl, htid, hwl, hwlv, hpbms⟩ := hrb
  wp_start as Hend
  iunfold wtxEnd' at Hend
  icases Hend with ⟨#Hfull, Hw, Hlive, Hrwl, Hcls, Hv, Hst, %Hok, %F, Htok, %hF⟩
  obtain ⟨hwok, hwr, hrl⟩ := Hok
  icases rbWtxEL_fields K tx r X $$ Hw with ⟨#Hpkg, #Hkc, %hdb, Hdb, Hwr, Hme, Hmv, Hback⟩
  rw [hdb]
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  iunfold wdbLive at Hlive
  icases Hlive with ⟨Hcg, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, Hrwtx, Hfile, Hpath,
    Hdsz, Hmfw, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩
  imod store_cfacts K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms _
    $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hcf⟩
  · iframe; iframe #
  obtain ⟨hmok, htok, hhwm, hwf, hbl, hwt⟩ := Hcf
  have hwt' := hwt wt rfl
  simp only at hwt'
  wp_auto
  rw [decide_eq_false Ht0.2.1]
  wp_auto
  rw [hwr]
  wp_auto
  icases rbMapFields_data K.db _ w.ms $$ Hmfw with ⟨Hdata, %Hbpos, Hmfw⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  have h64 : w.C.txid + 1 < 2 ^ 64 := hbl.2.2.2.1
  by_cases hms : w.ms = none
  · -- the mapping lost: not published, nothing lent
    have hpb : pb = false := by
      cases pb
      · rfl
      · exact absurd hms (hpbms rfl)
    have hwl0 : wl = false := by
      cases wl
      · rfl
      · exact absurd hms (hwl.1 rfl)
    subst hpb hwl0
    simp only [Bool.false_eq_true, ↓reduceIte] at hwt'
    rw [show rbDataOf w.ms = null by rw [hms]; rfl]
    wp_auto
    wp_apply wp_Txid $$ [Hmv] as Hmv
    · iframe
    subst hwt'
    rw [htid]
    simp only at hbl
    wp_apply wp_FlRollback w.fli w.fl _ (flBelow_rollback_pre w.fl w.C hbl h64) $$ [Hflo] as Hflo
    · iframe
    imod store_rollback K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms
      (some v, some (w.C.txid + 1), false, false) (w.C.txid + 1) F rfl rfl
      $$ [Hpi Hcur Hgfl Hgmap Hgwv Htok]
      with ⟨%S, %bs, Hcur, Hgfl, Hgmap, Hgwv, Hso, %HS, %Hbs, %Hrec⟩
    · iframe; iframe #
    icases wdb_rollback_f K.p fr w _ S bs F hwok hF rfl HS (pendSlots_two _ hwf) Hbs Hrec
      $$ [Hwc Hwb Hso] with ⟨%w', %Hw', Hwc, Hwb⟩
    · iframe
    obtain ⟨hC', hfl', hms', hm', hfli', hjunk', hf', hfd', hok'⟩ := Hw'
    ihave Hw := Hback $$ Hdb Hwr Hme Hmv
    ihave Hmfw := Hmfw $$ Hdata
    rw [show (null : Loc) = rbDataOf w.ms by rw [hms]; rfl] at *
    have hms2 : w'.ms = none := hms'.trans hms
    rw [← hfl']
    rw [← hC', ← hms', ← hm', ← hfli', ← hjunk', ← hf', ← hfd'] at *
    wp_apply wp_close K tx r X _ w'
      ⟨v, w'.C.txid + 1, false, false, rfl,
        Or.inr (by rw [hfl', hC']; exact FLPg.rollback_pending_none _ _),
        Iff.intro (fun h => by cases h) (fun h => absurd hms2 h), fun h => by cases h⟩
      $$ [Hw Hfull Hrwl Hcls Hv Hst Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile
        Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt] as Hdone
    · iunfold wtxEnd
      iframe Hfull Hw Hrwl Hcls Hv Hst
      isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd
        Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt]
      · unfold wdbLive wdbCoreG
        iframe
      ipureintro; exact ⟨hok', hwr, hrl⟩
    iapply HΦ; iexact Hdone
  · obtain ⟨b, l, hbl'⟩ : ∃ b l, w.ms = some (b, l) := by
      rcases h : w.ms with _ | ⟨b, l⟩
      · exact absurd h hms
      · exact ⟨b, l, rfl⟩
    have hb0 : 0 < b.addr := Hbpos b l hbl'
    have hbn : b ≠ null := by intro h; rw [h] at hb0; exact absurd hb0 (by decide)
    rw [show rbDataOf w.ms = b by rw [hbl']; rfl]
    wp_auto
    rw [decide_eq_false hbn]
    ihave Hmfw := Hmfw $$ Hdata
    ihave Hmf2 : mapFields K.db (DFrac.own (1 : Qp).half.half) (some (b, l) : MapSt) $$ [Hmfw]
    · rw [← hbl']; iexact Hmfw
    ihave Hmc2 : metaCellsQ (1 : Qp).half.half (some (b, l) : MapSt) w.C $$ [Hmc]
    · rw [← hbl']; iexact Hmc
    wp_auto
    wp_apply wp_meta K.db b l w.C _ _ hmok $$ [Hmf2 Hmc2] as ⟨Hmf2, Hmc2⟩
    · iframe
    wp_apply rbWp_meta_Txid wp_Txid b l w.C _ hmok $$ [Hmc2] as Hmc2
    · iframe
    wp_apply wp_Txid $$ [Hmv] as Hmv
    · iframe
    rw [htid]
    cases pb
    · -- not published: roll back
      simp only [Bool.false_eq_true, ↓reduceIte] at hwt'
      subst hwt'
      have hne : W64 (w.C.txid : Int) ≠ W64 ((w.C.txid + 1 : Nat) : Int) := by
        intro e
        have := congrArg BitVec.toNat e
        rw [toNat_W64_of_lt _ (by omega), toNat_W64_of_lt _ h64] at this
        omega
      rw [decide_eq_false hne]
      wp_auto
      wp_apply wp_Txid $$ [Hmv] as Hmv
      · iframe
      rw [htid]
      simp only at hbl
      wp_apply wp_FlRollback w.fli w.fl _ (flBelow_rollback_pre w.fl w.C hbl h64) $$ [Hflo] as Hflo
      · iframe
      imod store_rollback K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms
        (some v, some (w.C.txid + 1), false, wl) (w.C.txid + 1) F rfl rfl
        $$ [Hpi Hcur Hgfl Hgmap Hgwv Htok]
        with ⟨%S, %bs, Hcur, Hgfl, Hgmap, Hgwv, Hso, %HS, %Hbs, %Hrec⟩
      · iframe; iframe #
      icases wdb_rollback_f K.p fr w _ S bs F hwok hF rfl HS (pendSlots_two _ hwf) Hbs Hrec
        $$ [Hwc Hwb Hso] with ⟨%w', %Hw', Hwc, Hwb⟩
      · iframe
      obtain ⟨hC', hfl', hms', hm', hfli', hjunk', hf', hfd', hok'⟩ := Hw'
      imod store_cfacts K.B K.N K.p ⊤ CoPset.subseteq_top w.C _ w.ms _
        $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hcf2⟩
      · iframe; iframe #
      obtain ⟨-, -, -, hwf2, hbl2, -⟩ := Hcf2
      -- `db.data` again: mapped
      icases rbMapFields_data K.db _ _ $$ Hmf2 with ⟨Hdata, -, Hmf2⟩
      rw [show rbDataOf (some (b, l)) = b from rfl]
      wp_auto
      rw [decide_eq_false hbn]
      ihave Hmf2 := Hmf2 $$ Hdata
      wp_auto
      wp_apply wp_hasSynced K.db b l w.C _ _ hmok $$ [Hmf2 Hmc2] as ⟨Hmf2, Hmc2⟩
      · iframe
      obtain ⟨-, -, -, -, c5, -, -, -, -, -, -, c12, -, -, -⟩ := id hok'
      have hfree : ∀ x ∈ (w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int))).free,
          ¬ coversSlot w.C.pages x.toNat ∧ x.toNat < w.C.hwm := by
        intro x hx
        rw [← hfl'] at hx
        refine ⟨fun hc => c5 x hx ?_, ?_⟩
        · rw [hC']; exact (mem_pagesSlots_iff _ _).2 hc
        · have := c12 x hx; rw [hC'] at this; exact this
      rcases hfp : w.C.flpg with _ | f
      · -- no synced freelist page: `NoSyncReload(db.freepages())`
        rw [show (! (! decide (none = (none : Option Nat)))) = true from rfl]
        wp_auto
        ihave Hgmap2 : ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) $$ [Hgmap]
        · rw [← hbl']; iexact Hgmap
        wp_apply wp_freepages K w.C b l hmok htok hhwm $$ [Hpair Hcur Hgmap2 Hmc2 Hop]
          as %s ⟨Hs, -, %Hfacts, Hpair, Hcur, Hgmap2, Hmc2, Hop⟩
        · iframe; iframe #
        have hnsr := nsr_premises w.C _ hhwm hwf2 hbl2.2.2.2.2.2 hfree
        wp_apply wp_NSR w.fli _ s (freeIdsOf w.C) _ Hfacts.1 Hfacts.2.1 hnsr.1 hnsr.2
          $$ [Hflo Hs] as ⟨Hflo, -⟩
        · iframe
        obtain ⟨hids, hnd⟩ := nsr_store_ids w.C (w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int))) hhwm
        imod store_reload K.B K.N K.p ⊤ CoPset.subseteq_top w.C _ _ hids hnd $$ [Hpi Hcur Hgfl]
          with ⟨Hcur, Hgfl⟩
        · iframe; iframe #
        ihave Hw := Hback $$ Hdb Hwr Hme Hmv
        ihave Hmfw : mapFields K.db (DFrac.own (1 : Qp).half.half) w.ms $$ [Hmf2]
        · rw [hbl']; iexact Hmf2
        ihave Hmc : metaCellsQ (1 : Qp).half.half w.ms w.C $$ [Hmc2]
        · rw [hbl']; iexact Hmc2
        ihave Hgmap : ghostVar K.B.map (1 : Qp).half w.ms $$ [Hgmap2]
        · rw [hbl']; iexact Hgmap2
        have hok'' := wdbOK_reload w' (freeIdsOf w.C) hok' (by rw [hC']; exact hfp)
          (fun x hx => by
            rw [hC']
            have := (mem_freeIdsOf w.C (by omega) x).1 hx
            exact ⟨this.2.1, this.2.2⟩)
        rw [← hfl']
        rw [← hC', ← hms', ← hm', ← hfli', ← hjunk', ← hf', ← hfd']
        wp_apply wp_close K tx r X _ { w' with fl := w'.fl.reload (freeIdsOf w'.C) }
          ⟨v, w'.C.txid + 1, false, wl, rfl,
            Or.inr (by simp only; rw [hfl', hC']; exact FLPg.rollback_pending_none _ _),
            by simp only; rw [hms']; exact hwl, hwlv⟩
          $$ [Hw Hfull Hrwl Hcls Hv Hst Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile
            Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt] as Hdone
        · iunfold wtxEnd
          iframe Hfull Hw Hrwl Hcls Hv Hst
          isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd
            Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt]
          · unfold wdbLive wdbCoreG
            iframe
          rw [← hC'] at hok''
          ipureintro; exact ⟨hok'', hwr, hrl⟩
        iapply HΦ; iexact Hdone
      · -- a synced freelist page: `Reload(db.page(db.meta().Freelist()))`
        rw [show (! (! decide (some f = (none : Option Nat)))) = false by simp]
        wp_auto
        have hfp' : w'.C.flpg = some f := by rw [hC']; exact hfp
        obtain ⟨hpf, hsz, hcnt, hnd, h2, hlen, hne, hext⟩ :=
          reload_premises w' f hok' hfp' (by rw [hC']; exact hhwm) (by rw [hfl']; exact hwf2)
        have hextW := ext_in_W w' f hok' hfp'
        have hl9 : w.C.hwm * 4096 ≤ l := hwok.2.2.2.2.2.2.2.2.1 b l hbl'
        have hfw : (W64 (f : Int)).toNat = f := by
          rw [hC'] at hext
          rw [toNat_W64_of_lt _ (by omega)]
        wp_apply wp_meta K.db b l w.C _ _ hmok $$ [Hmf2 Hmc2] as ⟨Hmf2, Hmc2⟩
        · iframe
        wp_apply wp_meta_Freelist wp_Freelist b l w.C _ hmok f hfp $$ [Hmc2] as Hmc2
        · iframe
        simp only [mapFields]
        icases Hmf2 with ⟨Hdr, Hdata, Hm0, Hm1, %hmfp⟩
        unfold dbFixed
        icases Hfix with ⟨#HpgSz, -⟩
        wp_apply wp_page K.db b (W64 (f : Int)) _ hb0 (by rw [hfw]; rw [hC'] at hext; omega)
          $$ [Hdata] as Hdata
        · iframe; iexact HpgSz
        rw [hfw, show f * 4096 = 4096 * f by omega]
        -- the extent's cells and bytes, read against each other
        have hnd' : (List.range' f (1 + pageOverflow (w'.wb f))).Nodup := List.nodup_range'
        ihave Hwc : wCells (GF := GF) (some (b, l)) w'.W $$ [Hwc]
        · rw [← hbl', ← hms']; iexact Hwc
        icases wCells_ext b l w'.W _ hnd' (fun s hs => (hextW s hs).1)
          (fun s hs => (hextW s hs).2.2.1 b l (by rw [hms']; exact hbl')) $$ Hwc with ⟨Hec, Hwc⟩
        icases wBytes_ext K.p w'.W _ w'.wb w'.m.size hnd' (fun s hs => (hextW s hs).1)
          (fun s hs => (hextW s hs).2.1) $$ Hwb with ⟨Heb, Hwb⟩
        have hmaps : w.m.maps !! b = some l := by rw [hwok.1 b l hbl']; simp
        ihave Hosm : osMeta K.p (DFrac.own 1) (some w'.m) $$ [Hosm]
        · rw [hm']; iexact Hosm
        rw [← hm'] at hmaps
        iapply ext_agree _ rfl K.p (DFrac.own 1) w'.m b l hmaps (by simp) _ w'.wb
          (1 + pageOverflow (w'.wb f)) f (fun s h1 h2 => by
            have := hextW s (List.mem_range'_1.2 ⟨h1, h2⟩)
            exact ⟨this.2.2.1 b l (by rw [hms']; exact hbl'), this.2.2.2⟩) $$ Hos Hosm Heb Hec
        iintro Hosm Heb Hpg
        ihave Hpg : bytesPointsto (b +ₗ ((4096 * f : Nat) : Int)) (DFrac.own (1 : Qp).half)
            (extentBytes w'.wb f) $$ [Hpg]
        · unfold extentBytes; iexact Hpg
        have hpgne : extentBytes w'.wb f ≠ [] := by
          intro h
          have := congrArg List.length h
          have hf4 := (hextW f (List.mem_range'_1.2 ⟨Nat.le_refl _, by omega⟩)).2.2.2
          simp only [extentBytes, List.length_nil] at this
          rw [show 1 + pageOverflow (w'.wb f) = pageOverflow (w'.wb f) + 1 by omega,
            List.range'_succ, List.flatMap_cons, List.length_append, hf4] at this
          omega
        ihave %Hbd := internal.common.bytesPointsto_in_bounds _ _ _ hpgne $$ Hpg
        ihave Hflo : flPgOwn w.fli w'.fl $$ [Hflo]
        · rw [hfl']; iexact Hflo
        wp_apply wp_Reload w.fli w'.fl _ (extentBytes w'.wb f) _ hpf hsz hcnt Hbd.1 Hbd.2 hnd h2
          hlen hne $$ [Hflo Hpg] as ⟨Hflo, Hpg⟩
        · iframe
        -- the cells back
        ihave Hpg : bytesPointsto (b +ₗ ((4096 * f : Nat) : Int)) (DFrac.own (1 : Qp).half)
            ((List.range' f (1 + pageOverflow (w'.wb f))).flatMap w'.wb) $$ [Hpg]
        · unfold extentBytes; iexact Hpg
        ihave Hec := ext_cells_back b w'.wb _ f
          (fun s h1 h2 => (hextW s (List.mem_range'_1.2 ⟨h1, h2⟩)).2.2.2) $$ Hpg
        ihave Hwc := Hwc $$ Hec
        ihave Hwb := Hwb $$ Heb
        have hids := reload_store_ids w' f hok' hfp' (by rw [hC']; exact hhwm)
        rw [hC', hfl'] at hids
        imod store_reload K.B K.N K.p ⊤ CoPset.subseteq_top w.C _ _ hids hnd $$ [Hpi Hcur Hgfl]
          with ⟨Hcur, Hgfl⟩
        · iframe; iframe #
        ihave Hw := Hback $$ Hdb Hwr Hme Hmv
        ihave Hmfw : mapFields K.db (DFrac.own (1 : Qp).half.half) w.ms $$ [Hdr Hdata Hm0 Hm1]
        · rw [hbl']; simp only [mapFields]; iframe; ipureintro; exact hmfp
        ihave Hmc : metaCellsQ (1 : Qp).half.half w.ms w.C $$ [Hmc2]
        · rw [hbl']; iexact Hmc2
        ihave Hwc : wCells (GF := GF) w'.ms w'.W $$ [Hwc]
        · rw [hms', hbl']; iexact Hwc
        have hok'' := wdbOK_reload_synced w' f hok' hfp'
        rw [← hfl']
        rw [← hC', ← hms', ← hfli', ← hjunk', ← hf', ← hfd']
        wp_auto
        wp_apply wp_close K tx r X _ { w' with fl := w'.fl.reload (flIds (extentBytes w'.wb f)) }
          ⟨v, w'.C.txid + 1, false, wl, rfl,
            Or.inr (by simp only; rw [hfl', hC']; exact FLPg.rollback_pending_none _ _),
            by simp only; rw [hms']; exact hwl, hwlv⟩
          $$ [Hw Hfull Hrwl Hcls Hv Hst Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile
            Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt] as Hdone
        · iunfold wtxEnd
          iframe Hfull Hw Hrwl Hcls Hv Hst
          isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd
            Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt]
          · unfold wdbLive wdbCoreG
            iframe
          ipureintro; exact ⟨hok'', hwr, hrl⟩
        iapply HΦ; iexact Hdone
    · -- published (the commit point passed): only close
      have hfr : fr = false := by
        cases fr
        · rfl
        · exact absurd (hpbf rfl) (by simp)
      subst hfr
      have hwok : wdbOK w := (wdbOK'_false w).1 hwok
      simp only [↓reduceIte, Nat.add_zero] at hwt'
      subst hwt'
      rw [decide_eq_true rfl]
      wp_auto
      ihave Hw := Hback $$ Hdb Hwr Hme Hmv
      ihave Hmfw : mapFields K.db (DFrac.own (1 : Qp).half.half) w.ms $$ [Hmf2]
      · rw [hbl']; iexact Hmf2
      ihave Hmc : metaCellsQ (1 : Qp).half.half w.ms w.C $$ [Hmc2]
      · rw [hbl']; iexact Hmc2
      wp_apply wp_close K tx r X _ w ⟨v, w.C.txid, true, wl, rfl, Or.inl rfl, hwl, hwlv⟩
        $$ [Hw Hfull Hrwl Hcls Hv Hst Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile
          Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt] as Hdone
      · iunfold wtxEnd
        iframe Hfull Hw Hrwl Hcls Hv Hst
        isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd
          Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt]
        · unfold wdbLive wdbCoreG
          iframe
        ipureintro; exact ⟨hwok, hwr, hrl⟩
      iapply HΦ; iexact Hdone

omit hos package_sem in
/-- **`Tx.rollback.spec` from the flagged one** (at `fr = false`). -/
theorem Tx.rollback.spec_of_f (h : Tx.rollback_f.spec (GF := GF) (hG := hG)) :
    Tx.rollback.spec (GF := GF) (hG := hG) := by
  intro _ K tx r X ws w hrb
  iintro %Φ Hend HΦ
  ihave Hend := wtxEnd_wtxEnd' false K tx r X ws w $$ Hend
  wp_apply h false K tx r X ws w hrb (fun h => absurd h (by simp)) $$ [Hend] as Hdone
  · iexact Hend
  iapply HΦ; iexact Hdone

end proof

end bbolt
end EtcdGrove
end Perennial
