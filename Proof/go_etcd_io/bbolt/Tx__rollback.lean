/-
The proof of `Tx.rollback.spec` (`Proof/go_etcd_io/bbolt/Commit/RollbackSpec.lean`; U10d of
`notes/bbolt-proof-plan.md`, design §3.11 "Commit's error paths"): a published writer only closes;
otherwise the freelist is rolled back (`freelist.Rollback`, `store_rollback`, `wdb_rollback'`),
reloaded while mapped (`NoSyncReload(db.freepages())`, `store_reload`, `wdbOK_reload`; or `Reload`
of the synced freelist page), and the writer closes (`Tx.close_w.spec`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackSpec
public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
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
theorem wtxEL_fields (K : BC) (tx : Loc) (r : TxReg) (X : WX) :
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
def dataOf : MapSt → Loc
  | some (b, _) => b
  | none => null

omit package_sem hos in
/-- `db.data` out of the mapping fields, and back. -/
theorem mapFields_data (db : Loc) (dq : DFrac) (ms : MapSt) :
    mapFields (GF := GF) db dq ms ⊢ db.[DB, go!"data"] ↦{dq} dataOf ms ∗
      ⌜∀ b l, ms = some (b, l) → 0 < b.addr⌝ ∗
      (db.[DB, go!"data"] ↦{dq} dataOf ms -∗ mapFields db dq ms) := by
  rcases ms with _ | ⟨b, l⟩
  · simp only [mapFields, dataOf]
    iintro ⟨Hr, Hd, H0, H1⟩
    iframe Hd
    isplitr
    · ipureintro; intro b l h; cases h
    iintro Hd; iframe
  · simp only [mapFields, dataOf]
    iintro ⟨Hr, Hd, H0, H1, %h⟩
    iframe Hd
    isplitr
    · ipureintro; intro b' l' e; cases e; exact h.2.1
    iintro Hd; iframe; ipureintro; exact h

omit package_sem hos in
theorem metaCellsQ_some (q : Qp) (b : Loc) (l : Nat) (C : CommitSt) :
    metaCellsQ (GF := GF) q (some (b, l) : MapSt) C =
      iprop(bytesPointsto b (DFrac.own q) C.m0 ∗ bytesPointsto (b +ₗ (4096 : Int)) (DFrac.own q) C.m1) :=
  rfl

/-- **`db.meta().Txid()`** (as `DB.hasSyncedFreelist`'s proof): the current meta's txid. -/
theorem wp_meta_Txid (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
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

theorem Tx.rollback.wp_proof
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
    Tx.rollback.spec (GF := GF) (hG := hG) := by
  intro _ K tx r X ws w hrb
  obtain ⟨v, wt, pb, wl, rfl, htid, hwl, hwlv, hpbms⟩ := hrb
  wp_start as Hend
  iunfold wtxEnd at Hend
  icases Hend with ⟨#Hfull, Hw, Hlive, Hrwl, Hcls, Hshape, Hv, Hst, %Hok⟩
  obtain ⟨hwok, hwr, hrl⟩ := Hok
  icases wtxEL_fields K tx r X $$ Hw with ⟨#Hpkg, #Hkc, %hdb, Hdb, Hwr, Hme, Hmv, Hback⟩
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
  icases mapFields_data K.db _ w.ms $$ Hmfw with ⟨Hdata, %Hbpos, Hmfw⟩
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
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hwt'
    rw [show dataOf w.ms = null by rw [hms]; rfl]
    wp_auto
    wp_apply wp_Txid $$ [Hmv] as Hmv
    · iframe
    subst hwt'
    rw [htid]
    simp only at hbl
    wp_apply wp_FlRollback w.fli w.fl _ (flBelow_rollback_pre w.fl w.C hbl h64) $$ [Hflo] as Hflo
    · iframe
    imod store_rollback K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms
      (some v, some (w.C.txid + 1), false, false) (w.C.txid + 1) rfl rfl $$ [Hpi Hcur Hgfl Hgmap Hgwv]
      with ⟨%S, %bs, Hcur, Hgfl, Hgmap, Hgwv, Hso, %HS, %Hbs⟩
    · iframe; iframe #
    icases wdb_rollback' K.p w _ S bs hwok rfl HS (pendSlots_two _ hwf) Hbs
      $$ [Hwc Hwb Hso] with ⟨%w', %Hw', Hwc, Hwb⟩
    · iframe
    obtain ⟨hC', hfl', hms', hm', hfli', hjunk', hf', hfd', hok'⟩ := Hw'
    ihave Hw := Hback $$ Hdb Hwr Hme Hmv
    ihave Hmfw := Hmfw $$ Hdata
    rw [show (null : Loc) = dataOf w.ms by rw [hms]; rfl] at *
    have hms2 : w'.ms = none := hms'.trans hms
    rw [← hfl']
    rw [← hC', ← hms', ← hm', ← hfli', ← hjunk', ← hf', ← hfd'] at *
    wp_apply wp_close K tx r X _ w'
      ⟨v, w'.C.txid + 1, false, false, rfl,
        Or.inr (by rw [hfl', hC']; exact FLPg.rollback_pending_none _ _),
        Iff.intro (fun h => by cases h) (fun h => absurd hms2 h), fun h => by cases h⟩
      $$ [Hw Hfull Hrwl Hcls Hshape Hv Hst Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile
        Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt] as Hdone
    · iunfold wtxEnd
      iframe Hfull Hw Hrwl Hcls Hshape Hv Hst
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
    sorry

end proof

end bbolt
end EtcdGrove
end Perennial
