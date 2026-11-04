/-
`Commit`'s meta step (U10k of `notes/bbolt-proof-plan.md`): `tx.writeMeta()` over the writer's
working state `wtxW` and its database side `wdbLive` (`wLive`), with the commit point
`commitStep_commit`: the new tree's slots `S` (`slotsOwn`), the data's writer quarter and the
client's update go in; out comes either the published writer side at `C'` (the store's writer
state's publish flag set, a receipt more, the quarter at `Dn`, the update's `Q`), or, with an
error, everything as it was.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailAcc
public import Proof.go_etcd_io.bbolt.Commit.Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The writer side at the committed state `C`. -/
def WDb.withC (w : WDb) (C : CommitSt) : WDb := { w with C := C }

proj_simps WDb.withC

/-- The committed state the commit publishes: the meta `mv` (summed) over the new tree's pages. -/
abbrev pubC (C : CommitSt) (mv : Meta) (pages : Pages) : CommitSt :=
  C.publish (metaBuf mv) (metaSummed mv) pages

/-- **`commitStep_commit`'s premises** for the committed state `C`, the writer's freelist `fl`,
the mapping `(b, l)`, the meta `mv` and the new tree's `pages` (the data `Dn`), the new slots `S`
holding `bs`. -/
def cpOK (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (mv : Meta) (pages : Pages) (Dn : Data)
    (S : List Nat) (bs : Nat → List w8) : Prop :=
  mv.txid'.toNat = C.txid + 1 ∧ metaValid (metaSummed mv) ∧
  (metaSummed mv).pageSize'.toNat = 4096 ∧ treeData (pubC C mv pages) = Dn ∧
  treeOK (pubC C mv pages) ∧ (pubC C mv pages).hwm ≤ 2 ^ 62 ∧
  (∀ s ∈ treeSlots C, s ∉ treeSlots (pubC C mv pages) → s ∈ pendSlots fl) ∧
  (∀ s, s ∈ S ↔ s ∈ treeSlots (pubC C mv pages) ∧ s ∉ slotsOf C fl) ∧
  (∀ id pg, (pubC C mv pages).pages !! id = some pg → C.pages !! id = some pg ∨
    ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
      pg = (List.range' id (1 + pageOverflow pg)).flatMap bs)) ∧
  flBelow fl (pubC C mv pages) (some (C.txid + 1)) ∧
  (∀ s ∈ treeSlots (pubC C mv pages), s ∉ pendSlots fl) ∧
  (∀ s ∈ S, (bs s).length = 4096 ∧ W64 (s : Int) ∉ fl.free ∧
    (∀ b' l', (some (b, l) : MapSt) = some (b', l') → s < l' / 4096) ∧ 2 ≤ s)

omit [GooseExts] in
theorem txDbQ_quarter : txDbQ 1 + (1 : Qp).half.half = 1 := by
  apply Subtype.ext
  simp only [txDbQ, QpMul, Qp.val_add]
  show (1 : Rat) * (1 / 2) + 1 * (1 / 2 / 2) + 1 / 2 / 2 = 1
  grind

omit [GooseExts] in
theorem txDbQ_quarter_op :
    DFrac.own (txDbQ 1) • DFrac.own (1 : Qp).half.half = DFrac.own (1 : Qp) := by
  show DFrac.own (txDbQ 1 + (1 : Qp).half.half) = _
  rw [txDbQ_quarter]

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseSemantics] go_gctx hos sem in
/-- A receipt more, for the next txid. -/
theorem receipt_succ_sub (a t0 : Nat) :
    receipt (GF := GF) (a - t0) ∗ receipt 1 ⊢ receipt (a + 1 - t0) := by
  iintro H
  ihave H := (receipt_add (GF := GF) (a - t0) 1).2 $$ H
  have e : a - t0 + 1 = (a + 1 - t0) + (a - t0 + 1 - (a + 1 - t0)) := by omega
  rw [e]
  icases (receipt_add (GF := GF) _ _).1 $$ H with ⟨H, -⟩
  iexact H

/-- **`tx.writeMeta()`'s part of the working state**: the core, the registration, the statistics
token, `tx.db`, `tx.meta` (at `tx.db`'s fraction; its last quarter kept) and the meta copy; back
with any meta. -/
theorem cm_wmeta_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m 1 ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗
      tx.[Tx, go!"meta"] ↦{DFrac.own (txDbQ 1)} X.t.t.meta' ∗ X.t.t.meta' ↦ X.t.mv ∗
      ⌜X.t.t.meta' ≠ null⌝ ∗
      (∀ mv : Meta, statsTok r m 1 -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗
        tx.[Tx, go!"meta"] ↦{DFrac.own (txDbQ 1)} X.t.t.meta' -∗ X.t.t.meta' ↦ mv -∗
        wtxW K tx r m (X.withMv mv)) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, ⟨%Hh, ⟨Hwr, Hmg, Hme, Hpg, Hch, Hwf, Hmv, Hpm, Hbufs⟩,
    Hrf, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  have hdb : r.db = K.db := Hc.1
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db $$ [Hdb]
  · rw [← hdb]; iexact Hdb
  icases typedPointsto_not_null_dup _ _ _ $$ Hmv with ⟨Hmv, %Hmvn⟩
  ihave Hme : tx.[Tx, go!"meta"] ↦{DFrac.own (txDbQ 1) • DFrac.own (1 : Qp).half.half}
      X.t.t.meta' $$ [Hme]
  · rw [txDbQ_quarter_op]
    iexact Hme
  icases (dfractional (Φ := fun dq => typedPointsto (GF := GF) (tx.[Tx, go!"meta"]) X.t.t.meta' dq)
    _ _).1 $$ Hme with ⟨Hme, Hme4⟩
  iframe Hcore Hreg Hst Hdb Hme Hmv
  isplitr
  · ipureintro; exact Hmvn
  iintro %mv Hst Hdb Hme Hmv
  ihave Hme : tx.[Tx, go!"meta"] ↦{DFrac.own (txDbQ 1) • DFrac.own (1 : Qp).half.half}
      X.t.t.meta' $$ [Hme Hme4]
  · iapply (dfractional (Φ := fun dq => typedPointsto (GF := GF) (tx.[Tx, go!"meta"]) X.t.t.meta' dq)
      _ _).2
    iframe
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db $$ [Hdb]
  · rw [hdb]; iexact Hdb
  rw [txDbQ_quarter_op]
  unfold WX.withMv
  iframe
  iframe #
  ipureintro; exact ⟨Hc, Hh⟩

end res

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`Commit`'s meta step** (see the file header), for the writer side `w` mapped once at `b`
(`l` bytes), the store's writer state `wLive v w.C`, publishing `pubC w.C X.t.mv pages`. -/
theorem cm_meta_step (wp_writeMeta : Tx.writeMeta.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (X : WX) (v : View) (w : WDb) (b : Loc) (l : Nat)
    (N' : Namespace) (S : List Nat) (bs : Nat → List w8) (pages : Pages) (Dn : Data) (Q : IProp GF)
    (Fb : GMap Nat (List w8)) (hms : w.ms = some (b, l)) (hmaps : w.m.maps = GMap.singleton b l)
    (hroot : uint.Z X.t.mv.root'.root' < uint.Z X.t.mv.pgid')
    (hflp : uint.Z X.t.mv.freelist' < uint.Z X.t.mv.pgid' ∨
      X.t.mv.freelist'.toNat = pgidNoFreelist)
    (haddr : 0 < X.t.t.meta'.addr) (hsz : 8192 ≤ w.m.size) (hl : 8192 ≤ l)
    (hcp : cpOK w.C w.fl b l X.t.mv pages Dn S bs) :
    {{ wtxW (GF := GF) K tx r false X ∗ wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) w ∗
        ghostVar K.B.st (1 : Qp).half.half (treeData w.C) ∗
        slotsOwn (some (b, l) : MapSt) K.p S bs ∗ commitAU K N' (treeData w.C) Dn Q ∗
        fbTok K.B w.C w.fl ((some v, some (w.C.txid + 1), false, true) : WSt) Fb }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"writeMeta")) (Val #()))
    {{ (err : GoInterface), RET #err; ∃ m' : OsMeta, ⌜m'.size = w.m.size ∧ m'.maps = w.m.maps⌝ ∗
        wtxW K tx r false (X.withMv (metaSummed X.t.mv)) ∗
        (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err) ∗
        ((wdbLive K.B K.db K.p K.sp K.t0 tx ((some v, some (w.C.txid + 1), true, true) : WSt)
            ((w.reslot m' w.W w.wb).withC (pubC w.C X.t.mv pages)) ∗
          ghostVar K.B.st (1 : Qp).half.half Dn ∗ Q) ∨
         (⌜err ≠ interface.nil⌝ ∗
          wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) (w.reslot m' w.W w.wb) ∗
          ghostVar K.B.st (1 : Qp).half.half (treeData w.C) ∗
          slotsOwn (some (b, l) : MapSt) K.p S bs ∗ commitAU K N' (treeData w.C) Dn Q ∗
          fbTok K.B w.C w.fl ((some v, some (w.C.txid + 1), false, true) : WSt) Fb)) }} := by
  wp_start_folded as ⟨Hw, Hd, Hstq, HS, Hau, Hfb⟩
  obtain ⟨htx, hval, hps, hDn, htree, hhwm, hdrop, hS, hbytes, hfl, hnp, hSb⟩ := hcp
  icases cm_wmeta_acc K tx r false X $$ Hw with ⟨#Hcore, #Hreg, Hst, Hdb, Hme, Hmv, %Hmvn, Hwb⟩
  unfold wdbLive wdbCoreG
  icases Hd with ⟨⟨Hcur, Hfl, Hmap, Hout, Hwv, Hfli, Hopn, Hwa, Hrw, Hfile, Hpath, Hdsz, Hmf, Hom,
    Hfo, Hfd, Hmc, Hmb, Hwc, Hwbs, Hjk⟩, Hflo, Hsp, Hrc⟩
  ihave Hres : cpRes K w.C w.fl b l v (w.C.txid + 1) false true (treeData w.C)
      $$ [Hout Hcur Hfl Hmap Hwv Hopn Hmc Hmb Hstq]
  · unfold cpRes; rw [← hms]; iframe
  ihave Hcp := commitStep_commit K N' w.C w.fl b l v true S bs Fb X.t.mv pages Dn Q htx hval hps
    hDn htree hhwm hdrop hS hbytes hfl hnp hSb $$ [Hres HS Hfb Hau]
  · iframe; iframe #
  wp_apply wp_writeMeta K tx r false 1 (DFrac.own (txDbQ 1)) X.t.t.meta' X.t.mv w.f w.fd w.m b l
    (DFrac.own 1) (DFrac.own (1 : Qp).half) _ hroot hflp haddr hsz hmaps hl
    $$ [Hst Hdb Hme Hmv Hfile Hwa Hfo Hfd Hom Hcp]
    as %err ⟨Hst, Hdb, Hme, Hmv, Hfile, Hwa, Hfo, Hfd, ⟨%om', Hom, %Hom'⟩, %j, Hpost, %Hj, Herr⟩
  · iframe; iframe #
  ihave Hw := Hwb $$ %(metaSummed X.t.mv) Hst Hdb Hme Hmv
  iapply HΦ
  iexists om'
  isplitr
  · ipureintro; exact Hom'
  iframe Hw Herr
  unfold cpPost
  icases Hpost with (⟨%hj, Hres, Hrc1, HQ⟩ | ⟨%hj, Hres, HS, Hfb, Hau⟩)
  · ileft
    unfold cpRes
    icases Hres with ⟨Hout, Hcur, Hfl, Hmap, Hwv, Hopn, Hmc, Hmb, Hstq⟩
    iframe Hstq HQ
    have hC'tx : (pubC w.C X.t.mv pages).txid = w.C.txid + 1 := by
      simp only [pubC, CommitSt.publish, metaSummed_txid]; exact htx
    ihave Hrc := receipt_succ_sub (GF := GF) w.C.txid K.t0 $$ [Hrc Hrc1]
    · iframe
    simp only [WDb.withC, WDb.reslot]
    rw [hC'tx, hms, Hom'.1]
    iframe
  · iright
    isplitr
    · ipureintro
      intro he
      have := (Hj.2 he)
      omega
    unfold cpRes
    icases Hres with ⟨Hout, Hcur, Hfl, Hmap, Hwv, Hopn, Hmc, Hmb, Hstq⟩
    iframe Hstq HS Hau Hfb
    simp only [WDb.reslot]
    rw [hms, Hom'.1]
    iframe

end step

end bbolt
end EtcdGrove
end Perennial
