/-
The proof of `Spec/go_etcd_io/bbolt/Tx__close_w.lean` (U5, `notes/bbolt-proof-plan.md`; design
§4.2 "writer `Tx.close`"): the freelist's counts read, `db.rwtx` cleared, the store's writer
state idle (`store_wclose`), `rwlock` unlocked with the writer side idle (`rwR`), the statistics
merged under `statlock` once the transaction is done (`txs_close`), the fields cleared.

Batch 34 gave `Tx.close_w.spec` what U5c found missing: the closed flag's writer half, the records'
`writable` flag and root bucket (`wtxEnd`), and the lent view the records' (`wl = true → v = X.v`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__close_w
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__FreeCount
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__PendingCount
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__EstimatedWritePageSize
public import Proof.go_etcd_io.bbolt.Txn.StatsAdd
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The database's statistics after a writer's `close`: the freelist's counts and the merged
transaction statistics `ts`. -/
def closeStats (st : Stats) (ts : TxStats) (fl : FLPg) : Stats :=
  { st with
    TxStats' := ts
    FreePageN' := W64 (fl.free.length : Int)
    PendingPageN' := W64 (fl.pendingIds.length : Int)
    FreeAlloc' := (W64 (fl.free.length : Int) + W64 (fl.pendingIds.length : Int)) * W64 4096
    FreelistInuse' := W64 ((16 + 8 * (fl.allIds.length +
      (if 0xFFFF ≤ fl.allIds.length then 1 else 0)) : Nat) : Int) }

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
private theorem txDbQ_one_quarter_w : (1 : Qp).half.half + txDbQ 1 = 1 :=
  Subtype.ext (by simp only [txDbQ, QpMul, Qp.val_add, Qp.val_half, Qp.val_one]; grind)

private instance BC_full_persistent_cw (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance BC_core_persistent_cw (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

omit package_sem in
/-- Two shares of the mapping fields agree on the state, and add up. -/
theorem mapFields_combine (db : Loc) (a b : Qp) (ms1 ms2 : MapSt) :
    mapFields (GF := GF) db (DFrac.own a) ms1 ∗ mapFields db (DFrac.own b) ms2 ⊢
      ⌜ms1 = ms2⌝ ∗ mapFields db (DFrac.own (a + b)) ms1 := by
  have hd : ∀ ms, DFractional (fun dq => mapFields (GF := GF) db dq ms) := by
    intro ms; rcases ms with _ | ⟨b, l⟩ <;> simp only [mapFields] <;> infer_instance
  have heq : mapFields (GF := GF) db (DFrac.own a) ms1 ∗ mapFields db (DFrac.own b) ms2 ⊢
      ⌜ms1 = ms2⌝ := by
    rcases ms1 with _ | ⟨b1, l1⟩ <;> rcases ms2 with _ | ⟨b2, l2⟩ <;> simp only [mapFields]
    · iintro -; ipureintro; trivial
    · iintro ⟨⟨-, H1, -⟩, ⟨-, H2, -, -, %Hb⟩⟩
      icombine H1 H2 gives %h
      subst h; exact absurd Hb.2.1 (Int.lt_irrefl 0)
    · iintro ⟨⟨-, H1, -, -, %Hb⟩, ⟨-, H2, -⟩⟩
      icombine H1 H2 gives %h
      subst h; exact absurd Hb.2.1 (Int.lt_irrefl 0)
    · iintro ⟨⟨H1, -, -, -, %Hb1⟩, ⟨H2, -, -, -, %Hb2⟩⟩
      icombine H1 H2 gives %h
      ipureintro
      simp only [GoSlice.mk.injEq] at h
      obtain ⟨rfl, hl, -⟩ := h
      have h1 : l1 < 2 ^ 64 := by have := Hb1.1; omega
      have h2 : l2 < 2 ^ 64 := by have := Hb2.1; omega
      have := congrArg BitVec.toNat hl
      simp only [BitVec.toNat_ofInt] at this
      rw [Int.toNat_emod (by omega) (by omega)] at this
      congr 2
      simp at this
      omega
  refine (and_intro heq .rfl).trans (pure_elim_left fun h => ?_)
  subst h
  iintro H
  ihave H := ((fractional_of_dfractional (h := hd ms1) _).fractional a b).2 $$ H
  iframe
  ipureintro; rfl

omit package_sem in
/-- **The writer's heap, taken apart for `close`**: its fields, the root bucket's `FillPercent`,
and the root bucket's fields (whole: its `tx` field is the transaction's own, `heapOK`). -/
theorem wtxHeap_root_out (tx : Loc) (X : WX) (B : BRec) (hb : X.t.bs !! X.rl = some B) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ⊢ txFields tx (DFrac.own 1) X ∗ rootFill tx (DFrac.own 1) ∗
      ⌜X.rl = txRoot (GF := GF) tx ∧ B.bv.tx' = tx⌝ ∗
      X.rl.[Bucket, go!"InBucket"] ↦ B.bv.InBucket' ∗ X.rl.[Bucket, go!"tx"] ↦ B.bv.tx' ∗
      X.rl.[Bucket, go!"buckets"] ↦ B.bv.buckets' ∗ X.rl.[Bucket, go!"page"] ↦ B.bv.page' ∗
      X.rl.[Bucket, go!"rootNode"] ↦ B.bv.rootNode' ∗ X.rl.[Bucket, go!"nodes"] ↦ B.bv.nodes' := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, -, Hbk⟩
  have Ho := bobjs_bkt X.t X.rl B hb
  have htx : B.bv.tx' = tx := Hok.2.2.1 X.rl B hb
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hbk with ⟨Hb, -⟩
  iframe Hf Hrf
  isplitr
  · ipureintro; exact ⟨Hok.1, htx⟩
  unfold objOwn
  have hrl : X.rl = B.bv.tx'.[Tx, go!"root"] := by rw [htx, Hok.1]; rfl
  simp only [hrl, ↓reduceIte]
  icases Hb with ⟨H1, H2, H3, H4, H5, H6, -⟩
  iframe

theorem Tx.close_w.wp_proof
    (wp_FreeCount : internal.freelist.Interface.FreeCount.spec (GF := GF) (hG := hG))
    (wp_PendingCount : internal.freelist.Interface.PendingCount.spec (GF := GF) (hG := hG))
    (wp_EWPS : internal.freelist.Interface.EstimatedWritePageSize.spec (GF := GF) (hG := hG)) :
    Tx.close_w.spec (GF := GF) (hG := hG) := by
  intro K tx r X ws w hws
  obtain ⟨v, wt, pb, wl, rfl, hp, hwl, hv⟩ := hws
  wp_start as Hend
  iunfold wtxEnd at Hend
  icases Hend with ⟨#Hfull, Hw, Hlive, Hrwl, Hcls, -, -, Hst, %Hwok'⟩
  obtain ⟨Hwok, hwr, hrl⟩ := Hwok'
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hrl
  -- the writer's records, mapped or lost: their core, the mapping fields' quarter, the cells
  ihave Hw : wtxCore K tx r false X ∗
      ∃ ms' : MapSt, mapFields r.db (DFrac.own (1 : Qp).half.half) ms' ∗
        (⌜ms' = none⌝ ∨ (⌜∃ l, ms' = some (X.v.base, l)⌝ ∗ viewCells wq X.v)) $$ [Hw]
  · unfold wtxW wtxLost
    icases Hw with (⟨Hc, Hvc, %l, Hmf, -⟩ | ⟨Hc, Hmf⟩)
    · iframe Hc; iexists _; iframe Hmf; iright; iframe; ipureintro; exact ⟨l, rfl⟩
    · iframe Hc; iexists _; iframe Hmf; ileft; ipureintro; rfl
  icases Hw with ⟨Hcore, %ms', Hmf', Hcells⟩
  iunfold wtxCore at Hcore
  icases Hcore with ⟨#Hpkg, #Hkc, %Hc, #Hreg, Hh, -, -, -, Hdb, -, Hstok⟩
  obtain ⟨hdb, -, htxn, -, hrootn⟩ := Hc
  rw [hdb]
  iunfold wdbLive at Hlive
  icases Hlive with ⟨Hcg, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨%wa, Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hop, Hwa, Hrwtx, Hfile, Hpath,
    Hdsz, Hmf, Hosm, Hfo, Hfd, Hmc, Hmob, Hwc, Hwb, Hjunk⟩
  icases mapFields_combine K.db _ _ _ _ $$ [Hmf Hmf'] with ⟨%hms, Hmf⟩
  · iframe
  subst hms
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  ihave #Hrw : sync.isMutex K.db.[DB, go!"rwlock"] (rwR K.B K.db K.p K.sp K.t0) $$ []
  · unfold BC.full isBoltP; icases Hfull with ⟨-, $, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpkf : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  icases wtxHeap_root_out tx X B hB $$ Hh with ⟨Hf, Hrf, %Hrt, Hib, Htx, Hbk, Hpg, Hrn, Hnd⟩
  iunfold rootFill at Hrf
  icases Hrf with ⟨%f, %Hfn, Hfp⟩
  iunfold txFields at Hf
  icases Hf with ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, -⟩
  rw [hwr]
  wp_auto
  rw [decide_eq_false Ht0.2]
  wp_auto
  -- the freelist's counts
  wp_apply wp_FreeCount w.fli w.fl $$ [Hflo] as Hflo
  · iframe
  wp_apply wp_PendingCount w.fli w.fl $$ [Hflo] as Hflo
  · iframe
  wp_apply wp_EWPS w.fli w.fl $$ [Hflo] as Hflo
  · iframe
  -- the store's writer state idle, its view's cells back
  ihave Hvc : (if wl then viewCells wq v else emp) $$ [Hcells]
  · cases wl
    · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
    · simp only [↓reduceIte]
      rw [hv rfl]
      icases Hcells with (%h | ⟨-, H⟩)
      · exact absurd h (hwl.1 rfl)
      · iexact H
  imod store_wclose K.B K.N K.p ⊤ CoPset.subseteq_top v wt pb wl w.fl hp $$ [Hpi Hgwv Hvc Hgfl]
    with ⟨Hgwv, Hgfl⟩
  · iframe; iframe #
  -- `rwlock` unlocked: the writer side idle
  rw [Qp.half_add_half] at *
  wp_apply sync.Mutex.wp_Unlock _ (rwR K.B K.db K.p K.sp K.t0) $$ [$Hsync $Hrw $Hrwl Hcls Hcur Hgfl
    Hgmap Hgout Hgwv Hfli Hop Hwa Hrwtx Hfile Hpath Hdsz Hmf Hosm Hfo Hfd Hmc Hmob Hwc Hwb Hjunk Hst
    Hflo Hpair Hrcpt]
  · iunfold rwR
    ileft
    iexists w
    iframe Hcls
    unfold wdbOwn wdbCore wdbCoreG
    iframe
    try (ipureintro; exact Hwok)
  -- the transaction done: its statistics persisted, the invariant's quarter of `tx.db` out
  iunfold statsTok at Hstok
  simp only [Bool.false_eq_true, ↓reduceIte] at *
  imod txs_close K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hstok]
    with ⟨Hdb4, ⟨%s, #Hsts⟩, -⟩
  · iframe; iframe #
  rw [hdb]
  iunfold dbFixed at Hfix
  icases Hfix with ⟨#Hps, #Hsp, -⟩
  wp_auto
  -- the fields cleared: all of `tx.db`, the root bucket whole
  ihave Hdb := (typedPointsto_frac_add _ _ _ _).2 $$ [Hdb Hdb4]
  · iframe
  rw [txDbQ_one_quarter_w]
  obtain ⟨hrlE, htx⟩ := Hrt
  rw [hrlE, htx] at *
  ihave Hroot : (txRoot tx) ↦ ({ B.bv with tx' := tx, FillPercent' := f } : go_etcd_io.bbolt.Bucket) $$
    [Hib Htx Hbk Hpg Hrn Hnd Hfp]
  · iapply typedPointsto_combine _ _ _ hrootn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  by_cases hsp : K.sp = null
  · rw [decide_eq_true hsp]
    wp_auto
    unfold txRoot
    wp_auto
    iapply HΦ
    iunfold txDoneDef; iexists s; iexact Hsts
  · rw [decide_eq_false hsp]
    wp_auto
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hsl] as ⟨Hsw, HPs⟩
    iunfold Ps at HPs
    simp only [hsp, ↓reduceIte]
    icases HPs with ⟨%st, Hs⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hs with ⟨Hs, %Hspn⟩
    iStructNamed Hs
    wp_auto
    wp_apply wp_TxStats_add _ _ _ _ DFrac.discard $$ [TxStats Hsts] as ⟨⟨%ts, Hts⟩, -⟩
    · iframe; iframe #
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hsw Hts FreePageN PendingPageN FreeAlloc
      FreelistInuse TxN OpenTxN]
    · iunfold Ps; simp only [hsp, ↓reduceIte]
      iexists closeStats st ts w.fl
      iapply typedPointsto_combine _ _ _ Hspn
      simp only [TypedPointsto.typedPointstoDef, closeStats]
      iframe
    unfold txRoot
    wp_auto
    iapply HΦ
    iunfold txDoneDef; iexists s; iexact Hsts

end proof

end bbolt
end EtcdGrove
end Perennial
