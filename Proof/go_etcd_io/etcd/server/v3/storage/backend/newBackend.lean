/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/newBackend.lean`: bbolt's options through
`BboltOptions.lean`'s laws, `Open`, the backend's structure and the invariants
`newBatchTxBuffered` needs (`b.mu`'s guard, the metrics, `readTx.mu` initialized), then the rest
(`backend_init`), then `run` forked. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBatchTxBuffered
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.BackendConfig__mmapSize
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__run
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Panic
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.NewAlloc
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MutexLit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions
public import Perennial.ProgramLogic.Bounds
public import Spec.go_etcd_io.bbolt.Open_sharedNoErrH

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

open Fs in
/-- **The claim after `Open`'s create names the file it opened** (`crOut`/`crIno`, `OpenFileS.lean`):
a whole claim on `b` whose entry is the file `i`. -/
private theorem crOut_file [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.Assumptions] (j : Ino) (b : GoString) (h : NamesH) (dq : DFrac)
    (oc : Option (Nat × Nat × Ino)) (i : Ino) (hi : crIno b h oc i) :
    crOut (GF := GF) j b h dq oc ⊢ ∃ h' : NamesH, osNames j (.only [b]) dq h' ∗
      ⌜h'.cur !! b = some (.file i)⌝ := by
  rcases oc with _ | ⟨x, s, i0⟩
  · simp only [crOut]
    iintro H
    iexists h
    iframe H
    ipureintro; exact hi
  · simp only [crOut]
    iintro ⟨-, -, H⟩
    iexists _
    iframe H
    ipureintro
    simp only [crIno] at hi
    subst hi
    simp only [NamesH.log]
    exact GMap.lookup_insert _ _ _

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Open_kv`). -/
private theorem bbolt.kvGlue_Open_kv :
  ∀ [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)]
    (path : GoString) (mode : w32) (opts : Loc) (dq : DFrac) (o : backend.OptsM) (D : backend.Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ backend.fileHolds path D ∗ backend.optsAt opts dq o ∗
      ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ backend.boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); backend.optsAt opts dq o ∗
      ⌜err = GoInterface.nil⌝ ∗ ∃ γ : DBNames, ownDB db γ D ∗ wrTok γ ∗ isDB db γ ∗
          -- (2026-11-04, R2b-3c, the user's approval) which file it is (`DB.Close_kv` gives it back)
          dbFile db γ path }} := by
  intro hT hR path mode opts dq o D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.fileHolds, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · haveI := fax; haveI := fsax
    have h := bbolt.Open_sharedNoErrH.pendingS3d (GF := GF) (hG := hG)
    simp only [backend.fileHolds, backend.ownDB, backend.isDB, backend.boltLogger, hfs,
      onFs_some hfs]
    obtain ⟨Sio, hino, hpath, hs1, hs2⟩ := nex.ok
    iintro %Φ ⟨#Hpkg, Hf, Hbo, %Hok, #Hlog⟩ HΦ
    unfold fileHoldsF
    icases Hf with ⟨%R, %d, %b, %dqp, %j, %qc, %hn, %hpb, #Hinv, #Hsh, Hpath, Hcp, Hnm, Hnh⟩
    obtain ⟨hp, hb⟩ := hpb
    subst hp
    icases optsAt_bolt opts dq o Hok $$ Hbo with ⟨%f, %Hok', Hbo, Hback⟩
    ihave #Hlog' : ⌜(o.toBolt false f).logger = GoInterface.nil⌝ ∨
        bbolt.boltLogger (o.toBolt false f).logger $$ []
    · icases Hlog with (%Hl | #Hl)
      · ileft; ipureintro; exact Hl
      · iright
        rw [show (o.toBolt false f).logger = o.logger from rfl]
        iexact Hl
    wp_apply (h Sio hino hpath (dbNs (child d b)) R d b dqp j qc hn mode opts dq (o.toBolt false f) D hb)
      $$ [$Hpkg $Hinv $Hsh $Hpath $Hcp $Hnm $Hnh $Hbo $Hlog']
      as %db %err ⟨Hbo, Hpath, Hcp, %He, %oc, %γ, %i, Hcr, %hnc, #Hdb, #Hino, Hst, Hcl⟩
    · iframe %Hok'
      ipureintro; exact dbNs_osN _
    obtain ⟨hns, hci⟩ := hnc
    icases crOut_file j b hn (DFrac.own 1) oc i hci $$ Hcr with ⟨%h', Hnm, %hh'⟩
    ihave Hbo := Hback $$ Hbo
    iapply HΦ
    iframe Hbo
    isplitr
    · ipureintro; exact He
    iexists γ
    iframe Hdb Hst
    isplitl [Hpath Hcp Hnm Hcl]
    · unfold dbRestF
      iexists R, d, b, dqp, j, qc, h', i
      iframe Hinv Hsh Hpath Hcp Hnm Hino Hcl
      ipureintro; exact ⟨hns, hb, hh'⟩
    unfold wrTok dbFile
    isplitr
    · itrivial
    ipureintro; exact hns

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem backend.newBackend.wp_proof
    (hLog : backend.newBoltLoggerZap.spec (GF := GF) (hG := hG))
    (hMmap : backend.BackendConfig.mmapSize.spec (GF := GF) (hG := hG))
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hPanic : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (hNew : backend.newBatchTxBuffered.spec (GF := GF) (hG := hG))
    (hRun : backend.backend.run.spec (GF := GF) (hG := hG)) :
    backend.newBackend.spec (GF := GF) (hG := hG) := by
  have hOpen := @bbolt.kvGlue_Open_kv
  intro _ _ cfg P D W Pk K
  wp_start as ⟨#Hzl, Hfile, %HP, #Hhk, #Hvoff, Hmk, Htok⟩
  -- `boltOpenOptions`: the backend's package fact (item 8)
  ihave #Hboo : (boltOpenOptionsOk : IProp GF) $$ []
  · ihave Hbi : (go_etcd_io.etcd.server.v3.storage.backend.backendInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hbi with ⟨-, -, -, -, #H, -⟩
    iexact H
  iunfold boltOpenOptionsOk at Hboo
  icases Hboo with ⟨%p, #Hgp, #Hpo⟩
  -- `&bolt.Options{}`: `wp_auto` runs the literal and the allocation (the type is translated,
  -- 2026-11-17), and `optsAt_zero` reads the zero value as `optsZero`
  wp_auto
  obtain ⟨bo, rfl⟩ : ∃ bo, bo = «$r0_ptr» := ⟨_, rfl⟩
  ihave Hbo := optsAt_zero bo $$ «$r0»
  -- `*bopts = *boltOpenOptions` when that is not nil
  wp_join iprop(bopts_ptr ↦ bo ∗ ∃ o : OptsM, optsAt bo (DFrac.own 1) o ∗ ⌜o.ok⌝) with [Hbo bopts]
    as ⟨bopts, %o, Hbo, %Hok⟩
  · iframe
    ipureintro; exact optsZero_ok
  · icases Hpo with (%Hn | ⟨%o0, #Ho0, %Hok0⟩)
    · exfalso; simp_all
    wp_apply (wp_optsLoad p DFrac.discard o0) as %v1 ⟨-, %hv1⟩
    · iexact Ho0
    wp_apply_core (wp_optsStore bo optsZero o0 v1 hv1) $$ [$Hbo]
    iintro Hbo
    wp_auto
    isplitr
    · ipureintro; rfl
    iframe bopts
    iexists o0
    iframe
    ipureintro; exact Hok0
  -- `bcfg.Logger = zap.NewNop()` when nil
  wp_join iprop(∃ lg : Loc, bcfg_ptr ↦ ({ cfg with Logger' := lg } : BackendConfig) ∗
    zapLoggerOk lg) with [bcfg] as ⟨%lg, bcfg, #Hlz⟩
  · wp_apply hNop as %l #Hlz
    isplitr
    · ipureintro; rfl
    iexists l
    iframe
    iexact Hlz
  · ihave #Hok := zapLoggerOrNil_ok _ (by simp_all) $$ Hzl
    iexists cfg.Logger'
    iframe
    iexact Hok
  -- the options' fields
  wp_apply (hMmap bcfg_ptr _) $$ [$bcfg] as bcfg
  icases optsAt_int bo o go!"InitialMmapSize" (by simp) $$ Hbo with ⟨%x1, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  icases optsAt_freelist bo o $$ Hbo with ⟨%x2, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  icases optsAt_bool bo o go!"NoSync" (by simp) $$ Hbo with ⟨%x3, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  icases optsAt_bool bo o go!"NoGrowSync" (by simp) $$ Hbo with ⟨%x4, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  icases optsAt_mlock bo o $$ Hbo with ⟨%x5, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ [Hf]
  · simp only [HP.2.2]; iexact Hf
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlz
  wp_apply (hLog _) as %l ⟨#Hl, %Hlty⟩
  · iexact Hlz
  icases optsAt_logger bo o $$ Hbo with ⟨Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  icases optsAt_timeout bo _ $$ Hbo with ⟨%x6, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  -- `bolt.Open`
  wp_apply (hOpen cfg.Path' (W32 384) bo (DFrac.own 1) _ D) $$ [$Hfile $Hbo]
    as %db %err ⟨Hbo, Hres⟩
  · iframe #
    ipureintro
    obtain ⟨lc, rfl⟩ := Hlty
    exact OptsM.ok_withLogger o _ Hok ⟨_, lc, rfl, rfl⟩
  icases Hres with ⟨%Herr, %γd, Hown, Hwr, #Hdb, #Hdbfile⟩
  subst Herr
  wp_auto
  -- the backend's structure
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %m Hm
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %cm Hcm
  wp_apply wp_mutexLit
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hscc, %-, Hsco⟩
  wp_apply chan.wp_make1 (V := Unit) as %dc %γdc ⟨#Hdcc, %-, Hdco⟩
  iStructNamed «$r0»
  iStructNamedPrefix «$v5» "r"
  iStructNamedPrefix rbaseReadTx "r"
  iStructNamedPrefix rbuf "b"
  iStructNamedPrefix txReadBufferCache "c"
  ipersist readTx
  ipersist batchLimit
  ipersist lg
  ipersist batchInterval
  ipersist stopc
  ipersist donec
  ipersist rtxMu
  -- the metrics
  imod inv_alloc (bN.@"metrics") ⊤ iprop(∃ (a c d e : w64), bF go!"size" «$r0_ptr» ↦ a ∗
      bF go!"sizeInUse" «$r0_ptr» ↦ c ∗ bF go!"commits" «$r0_ptr» ↦ d ∗
      bF go!"openReadTxN" «$r0_ptr» ↦ e) $$ [size sizeInUse commits openReadTxN] with #Hmi
  · inext
    iexists _, _, _, _
    iframe
  ihave #Hmi' : metricsInv «$r0_ptr» $$ []
  · unfold metricsInv; iexact Hmi
  -- `b.mu`'s guard and a reader's slot
  imod sync.init_RWMutex (fun q => bF go!"db" «$r0_ptr» ↦{DFrac.own q} db) (E := ⊤)
    (bF go!"mu" «$r0_ptr») (HPfrac := ptOwn_fractional _ _) $$ [db] mu with Hmus
  · inext; iexact db
  icases rep_guard _ actualMaxReaders_pos' _ _ $$ Hmus with ⟨Hmus, #Hmug⟩
  ihave Hmu1 := rep_one _ actualMaxReaders_pos' _ $$ Hmus
  -- `b.safeRangeDeleteMu`: a reader's slot of it (`srSlot`, Q5-2)
  imod sync.init_RWMutex (fun _ => iprop(True)) (E := ⊤)
    (bF go!"safeRangeDeleteMu" «$r0_ptr») $$ [] safeRangeDeleteMu with Hsrs
  · inext; itrivial
  ihave Hsr1 : srSlot «$r0_ptr» $$ [Hsrs]
  · unfold srSlot; iapply rep_one _ actualMaxReaders_pos' _ $$ Hsrs
  -- `readTx.mu`, at the protocol level
  imod sync.rwmutex.init_RWMutex (E := ⊤) (nroot.@"rw") (rmuOf (baseOf «$v5_ptr»)) $$ rmu
    with ⟨%γrw, #Hrw, Hst, Hrtoks⟩
  ihave #Hbc : beginCtx «$r0_ptr» $$ []
  · unfold beginCtx
    iexists lg
    iframe #
  -- `b.batchTx = newBatchTxBuffered(b)`
  wp_apply (hNew «$r0_ptr» «$v5_ptr» db cfg.BatchLimit' γrw γd D) $$ [hooks rtx Hst Hmu1 Hown Hwr Htok]
    as %t ⟨%wtx, %rtx, Hmx, Htxf, Hpend, Hdel, Hwb, #Hbe, hooks, rtx, Hst, Hmu1, Hown, Hwtx, #Hwdb,
      Hlive, #Hrdb⟩
  · iframe
    iframe #
    ipureintro
    rw [← HP.2.1]; exact HP.1.2.1
  try wp_auto
  ipersist batchTx
  ipersist hooks
  -- the backend's invariants
  imod backend_init P W Pk K cfg.Hooks' «$r0_ptr» t «$v5_ptr» «$v3_ptr» «$v2_ptr» db lg wtx rtx m cm γd
    cfg.Path'
    γrw D sc dc γsc γdc HP.1 $$ [Hmk Hmu1 Hmx Htxf Hpend Hdel Hwb txPostLockInsideApplyHook Hown
      Hwtx Hst Hrtoks rtx Hlive rtxWg «$v2» btxBuffer bbufVersion Hm rbuckets Hcm «$v3» cmu
      cbuf cbufVersion Hsco Hdco Hsr1]
    with ⟨%γ, %Hγd, #Hbfile, Hpost, #Hstop, Hdcp, Hrtok, Hopnr, Husedr⟩
  · rw [HP.2.1]
    iframe
    iframe #
  iunfold newPostK at Hpost
  icases Hpost with ⟨#Hb, Hpost⟩
  -- `go b.run()`
  -- (2026-11-06, `notes/begin-tok-plan.md`) the fork's fresh token comes back to the creator; `run`
  -- exits with one (`CommitAndStop`'s)
  wp_apply wp_fork_tok_self $$ [Hdcp Hrtok Hopnr Husedr] as Htok
  · wp_apply (hRun γ P (W γ) (Pk γ) «$r0_ptr» sc dc γsc γdc 0 cfg.BatchInterval') $$
      [Hdcp Hrtok Hopnr Husedr] as Htok
    · iframe
      iframe #
    iframe Htok
    itrivial
  iapply HΦ
  ileft
  iexists «$r0_ptr», γ
  isplitr
  · ipureintro; rfl
  isplitl [Hpost]
  · unfold newPostK
    iframe Hb
    iexact Hpost
  iframe Hbfile Htok
  unfold hooksAt
  iexact hooks

end proof

end EtcdGrove
end Perennial
