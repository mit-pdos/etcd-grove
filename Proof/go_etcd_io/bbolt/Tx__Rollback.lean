/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Rollback.lean` (U5, `notes/bbolt-proof-plan.md`): a reader
is `Tx.Rollback_r` on its `rdTxK` (a pool loan: its `threadTok` back); a writer takes its
exclusive part out, rolls the freelist back (`Interface.Rollback`, `store_rollback`) and closes
(`Tx.close_w.spec`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Rollback
public import Spec.go_etcd_io.bbolt.Tx__Rollback_r
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Tx__close_w
public import Proof.go_etcd_io.bbolt.Txn.WRoll
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Rollback
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A reader's `Rollback`** (the public triple's read case): its `rdTxK` with a pool loan. -/
theorem Tx.Rollback.wp_reader [HasExt osFsExt]
    (wp_Rollback_r : Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (T : TxView) (hro : T.rw = false) :
    {{ boltTx (GF := GF) tx γ 1 T }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
    {{ RET #GoInterface.nil; txDone tx ∗ (if T.rw then emp else threadTok) }} := by
  iintro %Φ Ht HΦ
  unfold boltTx
  ihave Ht := (boltTx_rdTx _ _ tx 1 T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, -⟩
  ihave Hr := (rdTx_rdTxK _ _ tx .loan 1 T).1 $$ Hr
  icases Hr with ⟨%K, %v, -, Hr⟩
  iapply wp_Rollback_r K tx .loan T v $$ [Hr]
  · iexact Hr
  inext
  iintro %err ⟨%Herr, Hd, Hb⟩
  subst Herr
  iapply HΦ
  simp only [hro, Bool.false_eq_true, ↓reduceIte]
  unfold txDone pairBack
  iframe

/-- **What a writer's `Rollback` needs of its exclusive part** (U5c's finding; batch 34 gave
`txExcl`'s writer branch the missing parts, `txExclWGap_holds`): with the agreed state's half, the
whole agreed state, the `done` half, `rwlock`'s token, the writer side's half of the closed flag,
and the writer side as `Commit` sees it (`wdbW`), with its page tokens and `flViewU`. -/
def TxExclWGap : Prop :=
  ∀ [HasExt osFsExt] (K : BC) (tx : Loc) (r : TxReg) (X : WX) (c : TxViewC), r.db = K.db →
    txExcl (GF := GF) K.B K.p K.sp K.t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ⊢
      ghostVar r.n.v 1 (c, TxX.wr X) ∗ ghostVar r.n.done (1 : Qp).half false ∗
      sync.ownMutex K.db.[DB, go!"rwlock"] ∗ ghostVar K.B.cls (1 : Qp).half false ∗
      ∃ (w : WDb) (extra : GMap Nat Unit), wdbW K tx X.v w ∗ txShape r.n.pg X extra ∗
        ⌜flViewU X w.fl⌝

private instance BC_full_persistent_rb [HasExt osFsExt] (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance viewOf_persistent_rb [HasExt osFsExt] (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

private instance BC_core_persistent_rb [HasExt osFsExt] (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

/-- **A writer's `Rollback`** (the public triple's write case), given `TxExclWGap`. -/
theorem Tx.Rollback.wp_writer [HasExt osFsExt] (hgap : TxExclWGap (GF := GF))
    (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_FlRollback : internal.freelist.Interface.Rollback.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_w.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (T : TxView) (hrw : T.rw = true) :
    {{ boltTx (GF := GF) tx γ 1 T }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
    {{ RET #GoInterface.nil; txDone tx ∗ (if T.rw then emp else threadTok) }} := by
  wp_start as Ht
  unfold boltTx
  icases (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hB, hN, hT⟩ := HK
  rw [← hB]
  iunfold wtxW at Hw
  icases Hw with ⟨Hcore, Hvc, %l, Hmf, %Hl⟩
  iunfold wtxCore at Hcore
  icases Hcore with ⟨#Hpkg, #Hkc, %Hc, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, #Hvo, Hstok⟩
  obtain ⟨hdb, hrwr, htxn, hmg, hrootn⟩ := Hc
  simp only [statsTok, ↓reduceIte]
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  imod txExcl_take K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hstok] with Hx
  · iframe; iframe #
  iunfold wtxHeap at Hh
  icases Hh with ⟨%Hhok, Hf, Hrf, Hobj, Hbobj⟩
  iunfold txFields at Hf
  icases Hf with ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, Hmv, Hpm, Hbufs⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  rw [hmg, hdb]
  wp_auto
  wp_apply wp_Assert
  rw [decide_eq_false Ht0.2]
  wp_auto
  -- the exclusive part, as `Commit` sees it
  ihave Hg := hgap K tx r X c hdb $$ [Hx Hv]
  · iframe
  icases Hg with ⟨Hv, Hd, Hrwl, Hcls, Hg⟩
  icases Hg with ⟨%w, %extra, Hwdb, Hshape, %Hflv⟩
  iunfold wdbW at Hwdb
  icases Hwdb with ⟨Hlive, %Hwok⟩
  obtain ⟨hwok, hwms, hwv⟩ := Hwok
  iunfold wdbLive at Hlive
  icases Hlive with ⟨Hcg, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨%wa, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, Hrwtx, Hfile, Hpath,
    Hdsz, Hmfw, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩
  have hwr : X.t.t.writable' = true := Hf.1.1.1
  have hvtx : X.v.txid = w.C.txid := by rw [hwv]; rfl
  have h64 : w.C.txid + 1 < 2 ^ 64 := hwok.2.2.2.2.2.2.1
  have htid : X.t.mv.txid' = W64 ((w.C.txid + 1 : Nat) : Int) := by
    apply BitVec.eq_of_toNat_eq
    rw [← Hf.1.1.2.2.2.1, hvtx]; simp; omega
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  imod store_wfacts K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms (wLive X.v w.C)
    $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hwf⟩
  · iframe; iframe #
  obtain ⟨hbl, hpend⟩ := Hwf
  wp_method_call; wp_call
  wp_auto
  rw [decide_eq_false Ht0.2, hwr]
  wp_auto
  wp_apply wp_Txid $$ [Hmv] as Hmv
  · iframe
  rw [htid]
  wp_apply wp_FlRollback w.fli w.fl _ (flBelow_rollback_pre w.fl w.C hbl h64) $$ [Hflo] as Hflo
  · iframe
  -- the store's freelist rolled back; the slots leaving the store join the `W` slots
  imod store_rollback K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms (wLive X.v w.C)
    (w.C.txid + 1) rfl rfl $$ [Hpi Hcur Hgfl Hgmap Hgwv]
    with ⟨%S, %bs, Hcur, Hgfl, Hgmap, Hgwv, Hso, %HS⟩
  · iframe; iframe #
  icases wdb_rollback K.p w _ S bs hwok rfl HS hpend $$ [Hwc Hwb Hso] with ⟨%w', %Hw', Hwc, Hwb⟩
  · iframe
  obtain ⟨hC', hfl', hms', hm', hfli', hjunk', hf', hfd', hok'⟩ := Hw'
  have hvd : X.v.data = treeData w.C := by
    have e : X.v.data = (View.ofC X.v.base w.C).data := congrArg View.data hwv
    rw [e]; rfl
  have hbase : T.base = treeData w'.C := by rw [Hf.2.2.1, hvd, hC']
  have hms2 : w'.ms ≠ none := by rw [hms', hwms]; simp
  rw [← hfl', hbase]
  rw [← hC', ← hms', ← hm', ← hfli', ← hjunk', ← hf', ← hfd'] at *
  wp_apply wp_close K tx r X (wLive X.v w'.C) w'
    ⟨X.v, w'.C.txid + 1, false, true, rfl,
      Or.inr (by rw [hfl']; exact FLPg.rollback_pending_none _ _), ⟨fun _ => hms2, fun _ => rfl⟩,
      fun _ => rfl⟩
    $$ [Hcls Hfull Hvc Hmf Hpkg Hkc Hreg Hfills Hbk Hnl Hdb Hvo Hd Hrwl Hshape Hv Hst Hcur Hgfl
      Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk
      Hflo Hpair Hrcpt Hrf Hobj Hbobj Hwr Hmg Hme Hpgs Hch Hwfl Hmv Hpm Hbufs] as Hdone
  · iunfold wtxEnd
    iframe Hfull Hrwl Hst Hcls
    isplitl [Hvc Hmf Hpkg Hkc Hreg Hfills Hbk Hnl Hdb Hvo Hd Hrf Hobj Hbobj Hwr Hmg Hme Hpgs Hch
      Hwfl Hmv Hpm Hbufs]
    · ileft
      unfold wtxW wtxCore statsTok wtxHeap txFields
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hdb, hmg, hwr]
      iframe
      iframe #
      ipureintro
      exact ⟨⟨⟨rfl, hrwr, htxn, rfl, hrootn⟩, Hhok⟩, Hl⟩
    isplitl [Hcur Hgfl Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmfw Hosm Hfo Hfd Hmc
      Hmob Hwc Hwb Hjunk Hflo Hpair Hrcpt]
    · unfold wdbLive wdbCoreG
      iframe
    isplitl [Hshape]
    · iexists extra; iexact Hshape
    isplitl [Hv]
    · iexists c; iexact Hv
    ipureintro; exact ⟨hok', hwr, Hf.1.1.2.2.2.2.1⟩
  iapply HΦ
  simp only [hrw, ↓reduceIte]
  unfold txDone
  iframe

/-- **`Tx.Rollback`**, given `TxExclWGap` (the writer's exclusive part as `Commit` sees it). -/
theorem Tx.Rollback.wp_proof' (hgap : TxExclWGap (GF := GF))
    (wp_Rollback_r : ∀ [HasExt osFsExt], Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_FlRollback : internal.freelist.Interface.Rollback.spec (GF := GF) (hG := hG))
    (wp_close : ∀ [HasExt osFsExt], Tx.close_w.spec (GF := GF) (hG := hG)) :
    Tx.Rollback.spec (GF := GF) (hG := hG) := by
  intro _ tx γ T
  by_cases hrw : T.rw = true
  · exact Tx.Rollback.wp_writer hgap wp_Assert wp_Txid wp_FlRollback wp_close tx γ T hrw
  · exact Tx.Rollback.wp_reader wp_Rollback_r tx γ T (Bool.eq_false_iff.2 hrw)

/-- **`TxExclWGap` holds** (batch 34: `txExcl`'s writer branch carries the closed flag's half,
`ws = wLive X.v w.C`, `wdbOK w`, the mapping at the view's base and the view `w.C`'s). -/
theorem txExclWGap_holds : TxExclWGap (GF := GF) := by
  intro _ K tx r X c hdb
  iintro ⟨Hx, Hv⟩
  iunfold txExcl at Hx
  icases Hx with ⟨%c', %x, Hv', Hd, Hx⟩
  icombine Hv' Hv gives % ⟨_, hx⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  icases Hx with ⟨Hrwl, Hcls, %w, %extra, Hlive, Hshape, %Hok⟩
  ihave Hv := (ghostVar_split_half r.n.v 1 _).2 $$ [Hv' Hv]
  · iframe
  rw [← hdb]
  iframe Hv Hd Hrwl Hcls
  iexists w, extra
  iframe Hshape
  isplitl [Hlive]
  · unfold wdbW
    rw [hdb]
    rw [hdb] at *
    iframe
    ipureintro; exact ⟨Hok.1, Hok.2.1, Hok.2.2.1⟩
  ipureintro; exact Hok.2.2.2

theorem Tx.Rollback.wp_proof (wp_Rollback_r : ∀ [HasExt osFsExt], Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_FlRollback : internal.freelist.Interface.Rollback.spec (GF := GF) (hG := hG))
    (wp_close : ∀ [HasExt osFsExt], Tx.close_w.spec (GF := GF) (hG := hG)) :
    Tx.Rollback.spec (GF := GF) (hG := hG) :=
  Tx.Rollback.wp_proof' txExclWGap_holds wp_Rollback_r wp_Assert wp_Txid wp_FlRollback wp_close

end proof

end bbolt
end EtcdGrove
end Perennial
