/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/newBackend.lean`: bbolt's options through
`BboltOptions.lean`'s trust boundary, `Open`, the backend's structure and the invariants
`newBatchTxBuffered` needs (`b.mu`'s guard, the metrics, `readTx.mu` initialized), then the rest
(`backend_init`), then `run` forked. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBatchTxBuffered
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.BackendConfig__mmapSize
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__run
public import Spec.go_etcd_io.bbolt.Open_kv
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Panic
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.NewAlloc
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MutexLit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `Options`' representation from the package's type assumptions, preferred to the one through
its generated `IntoValTypedUnderlying` instance (`sorry -- axiomatized type`), which the
`StructFieldRef` steps on `bopts` would otherwise use. -/
local instance (priority := high) optsTypeRepr :
    go.TypeReprUnderlying go_etcd_io.bbolt.Options.underlying go_etcd_io.bbolt.Options :=
  go_etcd_io.bbolt.Options.TypeAssumptions.type_repr

local instance (priority := high) optsTypeReprU :
    TypeRepr go_etcd_io.bbolt.Options.underlying go_etcd_io.bbolt.Options :=
  go.type_repr_underlying (u := go_etcd_io.bbolt.Options.underlying)

local instance (priority := high) optsTypeRepr' :
    TypeRepr go_etcd_io.bbolt.Options.ty go_etcd_io.bbolt.Options :=
  go.type_repr_underlying (u := go_etcd_io.bbolt.Options.underlying)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem backend.newBackend.wp_proof
    (hOpen : bbolt.Open_kv.spec (GF := GF) (hG := hG))
    (hLog : backend.newBoltLoggerZap.spec (GF := GF) (hG := hG))
    (hMmap : backend.BackendConfig.mmapSize.spec (GF := GF) (hG := hG))
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hPanic : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (hNew : backend.newBatchTxBuffered.spec (GF := GF) (hG := hG))
    (hRun : backend.backend.run.spec (GF := GF) (hG := hG)) :
    backend.newBackend.spec (GF := GF) (hG := hG) := by
  intro cfg P D W Pk
  wp_start as ⟨#Hboo, Hfile, %HP, #Hhk, Hmk⟩
  iunfold boltOpenOptionsOk at Hboo
  icases Hboo with ⟨%p, #Hgp, #Hpo⟩
  wp_auto
  -- the `Options` value through `BboltOptions.lean` only (`wp_apply_core`: no `wp_auto` on
  -- an `Options` allocation, which would use the type's generated instance, `sorry`)
  wp_apply_core wp_optsLit
  iintro %v0 %hv0
  wp_apply_core (wp_optsAlloc v0 optsZero hv0)
  iintro %bo Hbo
  wp_auto
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
    ⌜lg ≠ Loc.null⌝) with [bcfg] as ⟨%lg, bcfg, %Hlg⟩
  · wp_apply hNop as %l %Hl
    iframe
    ipureintro; exact ⟨rfl, Hl⟩
  · iframe
    ipureintro; simp_all
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
  icases optsAt_bool bo o go!"Mlock" (by simp) $$ Hbo with ⟨%x5, Hf, Hback⟩
  wp_auto
  ihave Hbo := Hback $$ Hf
  wp_apply (hLog _) as %l #Hl
  · ipureintro; exact Hlg
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
    ipureintro; exact Hok
  icases Hres with (%Herr | ⟨%Herr, %γd, Hown, Hwr, #Hdb⟩)
  · -- `Open` failed: `lg.Panic`
    rcases err with ei | _
    · wp_auto
      wp_apply hStr as %f1 -
      wp_apply hErr as %f2 -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hPanic lg $$ [] as %v %Hv
      · ipureintro; exact Hlg
      subst Hv
      wp_auto
      iapply HΦ
      iright
      ipureintro
      exact ⟨_, rfl⟩
    · exact absurd rfl Herr
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
  -- `readTx.mu`, at the protocol level
  imod sync.rwmutex.init_RWMutex (E := ⊤) (nroot.@"rw") (rmuOf (baseOf «$v5_ptr»)) $$ rmu
    with ⟨%γrw, #Hrw, Hst, Hrtoks⟩
  ihave #Hbc : beginCtx «$r0_ptr» $$ []
  · unfold beginCtx
    iexists lg
    iframe #
    ipureintro; exact Hlg
  -- `b.batchTx = newBatchTxBuffered(b)`
  wp_apply (hNew «$r0_ptr» «$v5_ptr» db cfg.BatchLimit' γrw γd D) $$ [hooks rtx Hst Hmu1 Hown Hwr]
    as %t ⟨%wtx, %rtx, Hmx, Htxf, Hpend, Hdel, Hwb, #Hbe, hooks, rtx, Hst, Hmu1, Hown, Hwtx, #Hwdb,
      Hlive, #Hsnap, Hstats, #Hrdb⟩
  · iframe
    iframe #
    ipureintro
    rw [← HP.2]; exact HP.1.2.1
  try wp_auto
  ipersist batchTx
  ipersist hooks
  -- the backend's invariants
  imod backend_init P W Pk cfg.Hooks' «$r0_ptr» t «$v5_ptr» «$v3_ptr» «$v2_ptr» db lg wtx rtx m cm γd
    γrw D sc dc γsc γdc HP.1 Hlg $$ [Hmk Hmu1 Hmx Htxf Hpend Hdel Hwb txPostLockInsideApplyHook Hown
      Hwtx Hst Hrtoks rtx Hlive Hstats rtxWg «$v2» btxBuffer bbufVersion Hm rbuckets Hcm «$v3» cmu
      cbuf cbufVersion Hsco Hdco]
    with ⟨%γ, %Hγd, Hpost, #Hstop, Hdcp, Hrtok, Hopnr, Husedr⟩
  · rw [HP.2]
    iframe
    iframe #
  iunfold newPost at Hpost
  icases Hpost with ⟨#Hb, Hpost⟩
  -- `go b.run()`
  wp_apply wp_fork $$ [Hdcp Hrtok Hopnr Husedr]
  · wp_apply (hRun γ P (W γ) (Pk γ) «$r0_ptr» sc dc γsc γdc 0 cfg.BatchInterval') $$
      [Hdcp Hrtok Hopnr Husedr]
    · iframe
      iframe #
    itrivial
  iapply HΦ
  ileft
  iexists «$r0_ptr», γ
  isplitr
  · ipureintro; rfl
  unfold newPost
  iframe Hb
  iexact Hpost

end proof

end EtcdGrove
end Perennial
