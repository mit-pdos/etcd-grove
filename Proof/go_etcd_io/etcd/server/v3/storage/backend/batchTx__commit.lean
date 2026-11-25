/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__commit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.time.Duration__Seconds
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RegLemmas
public import Spec.go_etcd_io.bbolt.Tx__Commit
public import Spec.go_etcd_io.bbolt.Tx__Stats

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Commit_kv`). (backend-snapshot B1/B2, 2026-11-20) The commit point: bbolt's update is
fired through the backend's commit invariant (`cmtInv`), which holds the committed data's other
half and the snapshots' registrations; the batch lock's quarter of the open flag rules out its stopped
case. An ordinary commit arms every registration there with the batch lock's inputs at the new
committed data `S` (`obsIn`, given back; `regs_arm`), the commit counter up by one (`cntLb`). A
stopping commit (paid with the rest of the open flag, `stopPay`) stops the backend there and takes the
invariant's half out (`dbHalf`, for `Close`), leaving `bStopped` in its place. -/
private theorem bbolt.kvGlue_Tx__Commit_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Commit.spec (GF := GF) (hG := hG)) :
  ∀ (db tx : Loc) (γ : BNames) (P : BParams) (W Pk : IProp GF) (path : GoString) (stop : Bool)
    (D S : backend.Data) (n : Nat) (F : IProp GF),
  armStep γ P W Pk γ.db.ns F S n →
  γ.db.ns = dbNs path →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ.db D ∗ backend.txDB tx γ.db db ∗
      ownWTx tx γ.db D S ∗ cmtInv γ P W Pk ∗ fkRd γ P (S, ⟨∅, W64 0⟩) ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      (if stop then stopPay γ else iprop(F ∗ cntLb γ n)) }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err; backend.txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ ownDB db γ.db S ∗ wrTok γ.db ∗
        (if stop then iprop(bStopped γ ∗ dbHalf γ.db S)
         else iprop(dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ F ∗
           cntLb γ (n + 1)))) ∨
        ⌜err ≠ GoInterface.nil⌝) }} := by
  intro db tx γ P W Pk path stop D S n F hA hns
  have hE : (↑cmtN : CoPset) ⊆ ⊤ \ ↑γ.db.ns := by rw [hns]; exact cmtN_dbNs path
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.dbHalf, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx,
      backend.ownWTxG, backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq,
      backend.bktEnts_eq, backend.seekIdx_eq, onFs_some hfs]
    iintro %Φ ⟨-, ⟨#Hdb, Hs, Hrest⟩, #Hd, ⟨%G, Hl⟩, #Hinv, #Hfk, Hopn, Hsp⟩ HΦ
    cases stop
    · -- an ordinary commit: the invariant's half moves to `S`, every registration armed there
      simp only [Bool.false_eq_true, ↓reduceIte]
      ihave Hau : AU <{ ∃∃ (D' : backend.Data), bbolt.boltState γ.db 1 D' }> @ ⊤ \ ↑γ.db.ns, ∅
          <{ ⌜D' = D⌝ ∗ bbolt.boltState γ.db 1 S,
             COMM bbolt.boltState γ.db (1 : Qp).half S ∗
               dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ F ∗
               cntLb γ (n + 1) }> $$ [Hs Hopn Hsp]
      · iauintro
        unfold atomic_acc
        iunfold cmtInv at Hinv
        iinv Hinv with Hb Hclose <;> try exact hE
        iunfold cmtBody at Hb
        icases Hb with (⟨%Dc, >Hh, #Hfk0, Hregs⟩ | >#Hst)
        rotate_left
        · unfold bStopped
          icombine Hopn Hst gives %Hcb
          exact absurd Hcb.2 (by decide)
        isimp only [backend.dbHalf, onFs_some hfs] at Hh
        ihave %HD := bbolt.boltState_agree γ.db _ _ D Dc $$ [Hs Hh]
        · iframe Hs Hh
        subst HD
        ihave Hw := (backend.boltState_halves γ.db D).2 $$ [Hs Hh]
        · iframe Hs Hh
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hcl
        isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
        iexists D
        iframe Hw
        isplit
        · iintro Hw
          imod Hcl with -
          icases (backend.boltState_halves γ.db D).1 $$ Hw with ⟨Hs, Hh⟩
          imod Hclose $$ [Hh Hregs] with -
          · inext
            iunfold cmtBody
            ileft
            iexists D
            isimp only [backend.dbHalf, onFs_some hfs]
            iframe Hh Hregs
            iframe #
          imodintro
          iframe Hs Hopn Hsp
        · iintro ⟨-, Hw⟩
          imod Hcl with -
          icases Hsp with ⟨Hi, #Hlb⟩
          imod (hA D) $$ [$Hi $Hregs $Hlb] with ⟨Hi, Hregs, #Hlb'⟩
          icases (backend.boltState_halves γ.db S).1 $$ Hw with ⟨Hs, Hh⟩
          imod Hclose $$ [Hh Hregs] with -
          · inext
            iunfold cmtBody
            ileft
            iexists S
            isimp only [backend.dbHalf, onFs_some hfs]
            iframe Hh Hregs
            iframe #
          imodintro
          iframe Hs Hopn Hi Hlb'
      have h' := h tx γ.db (wView D S G)
        (iprop(bbolt.boltState γ.db (1 : Qp).half S ∗
          dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗ F ∗ cntLb γ (n + 1)))
      try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
      wp_apply h' $$ [$Hl $Hau] as %err ⟨#Hdn, Hr⟩
      all_goals try (ipureintro; first | trivial | rfl)
      iapply HΦ; iframe Hdn
      icases Hr with (⟨%He, Hs, Hopn, Hi, #Hlb'⟩ | ⟨%He, -⟩)
      · ileft; isplitr; · ipureintro; exact He
        iframe Hs Hdb Hrest Hopn Hi Hlb'
        unfold wrTok; itrivial
      · iright; ipureintro; exact He
    · -- the stop's commit: the backend stopped there, the invariant's half taken out
      simp only [↓reduceIte]
      ihave Hau : AU <{ ∃∃ (D' : backend.Data), bbolt.boltState γ.db 1 D' }> @ ⊤ \ ↑γ.db.ns, ∅
          <{ ⌜D' = D⌝ ∗ bbolt.boltState γ.db 1 S,
             COMM bbolt.boltState γ.db 1 S ∗ bStopped γ }> $$ [Hs Hopn Hsp]
      · iauintro
        unfold atomic_acc
        iunfold cmtInv at Hinv
        iinv Hinv with Hb Hclose <;> try exact hE
        iunfold cmtBody at Hb
        icases Hb with (⟨%Dc, >Hh, #Hfk0, Hregs⟩ | >#Hst)
        rotate_left
        · unfold bStopped
          icombine Hopn Hst gives %Hcb
          exact absurd Hcb.2 (by decide)
        isimp only [backend.dbHalf, onFs_some hfs] at Hh
        ihave %HD := bbolt.boltState_agree γ.db _ _ D Dc $$ [Hs Hh]
        · iframe Hs Hh
        subst HD
        ihave Hw := (backend.boltState_halves γ.db D).2 $$ [Hs Hh]
        · iframe Hs Hh
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hcl
        isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
        iexists D
        iframe Hw
        isplit
        · iintro Hw
          imod Hcl with -
          icases (backend.boltState_halves γ.db D).1 $$ Hw with ⟨Hs, Hh⟩
          imod Hclose $$ [Hh Hregs] with -
          · inext
            iunfold cmtBody
            ileft
            iexists D
            isimp only [backend.dbHalf, onFs_some hfs]
            iframe Hh Hregs
            iframe #
          imodintro
          iframe Hs Hopn Hsp
        · iintro ⟨-, Hw⟩
          imod Hcl with -
          imod opn_stop_cmt γ $$ [$Hopn $Hsp] with #Hbs
          imod Hclose $$ [] with -
          · inext
            iunfold cmtBody
            iright
            iexact Hbs
          imodintro
          iframe Hw Hbs
      have h' := h tx γ.db (wView D S G) (iprop(bbolt.boltState γ.db 1 S ∗ bStopped γ))
      try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
      wp_apply h' $$ [$Hl $Hau] as %err ⟨#Hdn, Hr⟩
      all_goals try (ipureintro; first | trivial | rfl)
      iapply HΦ; iframe Hdn
      icases Hr with (⟨%He, Hw, #Hbs⟩ | ⟨%He, -⟩)
      · ileft; isplitr; · ipureintro; exact He
        icases (backend.boltState_halves γ.db S).1 $$ Hw with ⟨Hs, Hh⟩
        iframe Hs Hh Hdb Hrest Hbs
        unfold wrTok; itrivial
      · iright; ipureintro; exact He

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Stats_kv`). -/
private theorem bbolt.kvGlue_Tx__Stats_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Stats.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ backend.txDone tx }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Stats")) (Val #()))
  {{ (s : TxStats), RET #s; True }} := by
  intro tx
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, H⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hd⟩ HΦ
    have h' := h tx
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hd] as %s -
    iapply HΦ; itrivial

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (backend-snapshot B2) **A no-op commit arms the registrations**: nothing pending, the writer's
contents are the committed data `C` (`sessWf`), so the batch lock's inputs at it arm every
registration there, the counter up by one (as at a commit point, without bbolt). -/
private theorem cmt_arm_noop (γ : BNames) (P : BParams) (W Pk : IProp GF) (db : Loc) (path : GoString)
    (C : backend.Data) (n : Nat) (F : IProp GF) (hA : armStep γ P W Pk γ.db.ns F C n)
    (hns : γ.db.ns = dbNs path) :
    cmtInv γ P W Pk ∗ ownDB db γ.db C ∗ dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      F ∗ cntLb γ n ⊢
    |={⊤}=> ownDB db γ.db C ∗ dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      F ∗ cntLb γ (n + 1) := by
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, onFs_none hfs]
    iintro ⟨-, H, -⟩
    iexfalso; iexact H
  · simp only [backend.ownDB, onFs_some hfs]
    iintro ⟨#Hinv, ⟨#Hdb, Hs, Hrest⟩, Hopn, Hi, #Hlb⟩
    iunfold cmtInv at Hinv
    iinv Hinv with Hb Hclose
    iunfold cmtBody at Hb
    icases Hb with (⟨%Dc, >Hh, #Hfk0, Hregs⟩ | >#Hst)
    rotate_left
    · unfold bStopped
      icombine Hopn Hst gives %Hcb
      exact absurd Hcb.2 (by decide)
    isimp only [backend.dbHalf, onFs_some hfs] at Hh
    ihave %HD := bbolt.boltState_agree γ.db _ _ C Dc $$ [Hs Hh]
    · iframe Hs Hh
    subst HD
    have hsub : cmtMask γ.db.ns ⊆ ⊤ \ ↑cmtN := by
      intro x hx
      rw [Iris.Std.LawfulSet.mem_diff] at hx ⊢
      exact ⟨CoPset.mem_full, hx.2⟩
    imod ((hA C).trans (fupd_mask_mono hsub)) $$ [$Hi $Hregs $Hlb] with ⟨Hi, Hregs, #Hlb'⟩
    imod Hclose $$ [Hh Hregs] with -
    · inext
      iunfold cmtBody
      ileft
      iexists C
      isimp only [backend.dbHalf, onFs_some hfs]
      iframe Hh Hregs
      iframe #
    imodintro
    iframe Hdb Hs Hrest Hopn Hi Hlb'

theorem backend.batchTx.commit.wp_proof
    (hCommit : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Commit.spec (GF := GF) (hG := hG))
    (hStats : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Stats.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.batchTx.commit.spec (GF := GF) (hG := hG) := by
  replace hCommit := bbolt.kvGlue_Tx__Commit_kv hCommit
  replace hStats := bbolt.kvGlue_Tx__Stats_kv hStats
  intro γ P W Pk b t db st stop n F hArm
  wp_start as ⟨#Hb, #Ht, Hw, Hown, #Htxdb, Hmu, Hopn, Hsp, #HfkS, %hSC⟩
  icases isBackend_cmtInv γ P W Pk b $$ Hb with ⟨#Hcmt, %path, %hns⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db1, %lg', #-, #-, #-, #-, #Hmi, #-⟩
  ihave #Hbc := isBackend_beginCtx γ P W Pk b $$ Hb
  ihave Hi : (backendInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨⟨%h1, #Hg1, #Hs1⟩, ⟨%h2, #Hg2, #Hs2⟩, ⟨%h3, #Hg3, #Hs3⟩, ⟨%h4, #Hg4, #Hs4⟩, -⟩
  unfold histSpec
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  icases ownWTx_live st.tx γ.db st.C st.S $$ Hwtx with ⟨%Tw, Hlive, Hback⟩
  icases persistent_entails_right (txLive_nonnull st.tx γ.db 1 Tw) $$ Hlive with ⟨%Hnn, Hlive⟩
  ihave Hwtx := Hback $$ Hlive
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  by_cases hA : st.pend = W64 0 ∧ stop = false
  · obtain ⟨hA1, rfl⟩ := hA
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hsp with ⟨Hi, #Hlb⟩
    have hSC' := hSC hA1
    rw [hSC']
    imod cmt_arm_noop γ P W Pk db path st.C n F (by rw [← hSC']; exact hArm) hns $$ [$Hcmt $Hown $Hopn $Hi $Hlb] with ⟨Hown, Hopn, Hi, #Hlb'⟩
    rw [hA1]
    wp_auto
    iapply HΦ
    iframe Hmu
    ileft
    iframe
    iframe #
    ipureintro
    first | exact ⟨rfl, rfl⟩ | exact ⟨hA1, rfl⟩ | simp [hA1]
  have Hnot := hA
  wp_if_destruct
  · cases stop
    · exact absurd ⟨Hif, rfl⟩ hA
    try wp_auto
    wp_apply time.wp_Now as %start -
    wp_apply (hCommit db st.tx γ P W Pk path true st.C st.S n F hArm hns) $$ [$Hown $Htxdb $Hwtx $Hcmt $HfkS $Hopn $Hsp]
      as %err ⟨#Hdone, Hr⟩
    wp_apply (hStats st.tx) $$ [$Hdone] as %s1 -
    wp_apply hSeconds as %f1 -
    wp_apply Hs1
    wp_apply (hStats st.tx) $$ [$Hdone] as %s2 -
    wp_apply hSeconds as %f2 -
    wp_apply Hs2
    wp_apply (hStats st.tx) $$ [$Hdone] as %s3 -
    wp_apply hSeconds as %f3 -
    wp_apply Hs3
    wp_apply time.wp_Since as %d -
    wp_apply hSeconds as %f4 -
    wp_apply Hs4
    wp_apply (wp_commitsAdd b (W64 1)) $$ [$Hmi] as %nc -
    icases Hr with (⟨%Herr, Hown, Hwr, Hx⟩ | %Herr)
    · subst Herr
      wp_auto
      try wp_auto
      iapply HΦ
      iframe Hmu
      iright
      iframe Hown Hpend
      isplitr
      · ipureintro; exact Hnot
      iexists _
      iframe Htxf
      simp only [↓reduceIte]
      iexact Hx
    · rcases err with ei | _
      · wp_auto
        wp_apply hError as %f -
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        wp_apply hFatal lg $$ [] as %v Hf
        · iexact Hlgn
        iexfalso
        iexact Hf
      · exact absurd rfl Herr
  · try wp_auto
    wp_apply time.wp_Now as %start -
    wp_apply (hCommit db st.tx γ P W Pk path stop st.C st.S n F hArm hns) $$ [$Hown $Htxdb $Hwtx $Hcmt $HfkS $Hopn $Hsp]
      as %err ⟨#Hdone, Hr⟩
    wp_apply (hStats st.tx) $$ [$Hdone] as %s1 -
    wp_apply hSeconds as %f1 -
    wp_apply Hs1
    wp_apply (hStats st.tx) $$ [$Hdone] as %s2 -
    wp_apply hSeconds as %f2 -
    wp_apply Hs2
    wp_apply (hStats st.tx) $$ [$Hdone] as %s3 -
    wp_apply hSeconds as %f3 -
    wp_apply Hs3
    wp_apply time.wp_Since as %d -
    wp_apply hSeconds as %f4 -
    wp_apply Hs4
    wp_apply (wp_commitsAdd b (W64 1)) $$ [$Hmi] as %nc -
    icases Hr with (⟨%Herr, Hown, Hwr, Hx⟩ | %Herr)
    · subst Herr
      wp_auto
      cases stop
      · try wp_auto
        wp_apply (hBegin γ.db b db st.S true) $$ [$Hmu $Hown Hwr] as %tx' ⟨Hmu, Hown, #Htxdb', Hwtx'⟩
        · iframe #
          simp only [↓reduceIte]
          iexact Hwr
        iapply HΦ
        iframe Hmu
        iright
        iframe Hown Hpend
        isplitr
        · ipureintro; exact Hnot
        iexists _
        iframe Htxf
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        iframe #
      · try wp_auto
        iapply HΦ
        iframe Hmu
        iright
        iframe Hown Hpend
        isplitr
        · ipureintro; exact Hnot
        iexists _
        iframe Htxf
        simp only [↓reduceIte]
        iexact Hx
    · rcases err with ei | _
      · wp_auto
        wp_apply hError as %f -
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        wp_apply hFatal lg $$ [] as %v Hf
        · iexact Hlgn
        iexfalso
        iexact Hf
      · exact absurd rfl Herr

end proof

end EtcdGrove
end Perennial
