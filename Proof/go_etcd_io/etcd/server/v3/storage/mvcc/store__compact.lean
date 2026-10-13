/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compact
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.context.Err
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactBarrier
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompaction
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `context.TODO()` (its body: a `todoCtx{}` as a `Context`) returns `todoCtxV`, proved from
its translation (no axiom: the barrier after a failed pass runs at it). -/
theorem mvcc.wp_context_TODO_body :
    {{ (True : IProp GF) }}
      (App (Val #(functions _root_.Perennial.context.TODO [])) (Val #()))
    {{ RET #(GoInterface.ok mvcc.todoCtxV); True }} := by
  wp_start
  iapply HΦ
  itrivial

theorem mvcc.store.compact.wp_proof
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : context.Err.spec (GF := GF) (hG := hG))
    (h2 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.scheduleCompaction.spec (GF := GF) (hG := hG))
    (h4 : zap.Error.spec (GF := GF) (hG := hG))
    (h5 : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h6 : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG))
    (h7 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h8 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h9 : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    mvcc.store.compact.spec (GF := GF) (hG := hG) := by
  intro s γ trace rev prev pcc Htr
  wp_start as ⟨#Hjob, Hq⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %ch %γc ⟨#Hc, %Hcap, Hown⟩
  imod alloc_broadcast_chan (E := ⊤) (mvcc.compactDone s γ (sint.Z rev)) γc ch $$ Hc Hown with Hcl
  ihave #Hrcv := ownBroadcastChan_Unknown _ _ _ _ $$ Hcl
  (try wp_auto)
  -- the queue: the last tracked job's `Post` `Q`, with `R` the token's
  iunfold mvcc.compactQueue at Hq
  icases Hq with ⟨%Ps, %p, %Q, %R, Hq, #Hp, HR, Hw⟩
  imod (schedule.savedProp_alloc (mvcc.compactTok γ (sint.Z rev))) with ⟨%post, #Hpost⟩
  ipersist s
  ipersist rev
  ipersist prevCompactRev
  ipersist prevCompactionCompleted
  ipersist ch
  ihave #Hjob' := Hjob
  iunfold mvcc.compactJobPre at Hjob'
  icases Hjob' with ⟨#Hs, #Hstop, %Hcmp, #Hlb, #Hcert⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  wp_func_lits
  (try wp_auto)
  wp_apply (h0 γ.sch _ _
      iprop(mvcc.compactCloser ch (mvcc.compactDone s γ (sint.Z rev)) ∗ R ∗
        (Q ∗ R -∗ mvcc.compactTok γ (sint.Z rev)))
      Q (mvcc.compactTok γ (sint.Z rev))) $$ [] as %j #Hj
  · iframe #
    iunfold schedule.jobFnSpec
    iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨Hcl, HR, Hw⟩, HQ, #Hctx⟩ HΦj
    wp_auto
    ihave #HErrU := h1 ctx cd Broadcast.Unknown $$ Hctx
    wp_apply HErrU as %err Hm #HcS
    cases err with
    | ok e =>
      simp only [reduceCtorEq, ↓reduceIte]
      icases Hm with ⟨-, #Hclosed⟩
      wp_auto
      wp_apply (h2 s γ ctx cd ch (mvcc.compactDone s γ (sint.Z rev))) $$ [$Hcl]
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx; iright; iexact Hctx
        iunfold mvcc.compactDone; iright; iright; iexists cd; iexact Hclosed
      (try wp_auto)
      iapply HΦj
      iframe Hrun
      iapply Hw; iframe HQ HR
    | nil =>
    simp only [↓reduceIte]
    wp_auto
    ihave Htok := Hw $$ [HQ HR]
    · iframe HQ HR
    wp_apply (h3 s γ rev prev) $$ [$Htok] as %h %err ⟨Hidx, Hres⟩
    · iframe #
    ihave Htok : mvcc.compactTok γ (sint.Z rev) $$ [Hidx]
    · iunfold mvcc.compactTok; iexists (sint.Z rev); iframe Hidx; ipureintro; exact Int.le_refl _
    icases Hres with (⟨%Herr, #Hdone⟩ | ⟨Herr, #Hstopped⟩)
    · subst Herr
      wp_auto
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_join with [hash]
      · (try wp_auto)
        wp_apply (h7 lg) $$ []
        · iframe #; ipureintro; exact Hlgnn
        wp_join_done
      · (try wp_auto)
        wp_apply (h6 shs h)
        wp_join_done
      iunfold mvcc.compactCloser at Hcl
      icases Hcl with ⟨%γc', Hcl⟩
      wp_apply wp_broadcast_chan_close $$ [$Hcl] as -
      · iunfold mvcc.compactDone; ileft; iexact Hdone
      (try wp_auto)
      iapply HΦj
      iframe Hrun Htok
    · iunfold mvcc.errorfIs at Herr
      icases Herr with ⟨%x, %Hx, -⟩
      subst Hx
      wp_auto
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_apply h4 as %fld -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %flds -
      (try wp_auto)
      wp_apply (h5 lg) $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_apply mvcc.wp_context_TODO_body
      (try wp_auto)
      wp_apply (h2 s γ mvcc.todoCtxV cd ch (mvcc.compactDone s γ (sint.Z rev))) $$ [$Hcl]
      · iframe #
        isplitl []
        · iunfold mvcc.barrierCtx; ileft; ipureintro; rfl
        iunfold mvcc.compactDone; iright; ileft; iexact Hstopped
      (try wp_auto)
      iapply HΦj
      iframe Hrun Htok
  (try wp_auto)
  -- `s.fifoSched.Schedule(j)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
  ihave #HisSched' := HisSched
  iunfold schedule.isScheduler at HisSched'
  icases HisSched' with ⟨#Hfifo, -⟩
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  cases ssched with
  | nil => exact absurd rfl Hnn
  | ok fi =>
  (try wp_auto)
  wp_apply (h8 fi γ.sch j
      iprop(mvcc.compactCloser ch (mvcc.compactDone s γ (sint.Z rev)) ∗ R ∗
        (Q ∗ R -∗ mvcc.compactTok γ (sint.Z rev)))
      Q (mvcc.compactTok γ (sint.Z rev)) (some (Ps, p, post))) $$ [Hcl HR Hw Hq] as Hq
  · iframe #
    simp only [schedule.schedPre]
    iframe Hq HR Hw Hp Hpost
    iunfold mvcc.compactCloser
    iexists γc; iexact Hcl
  simp only [schedule.schedPost]
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (h9 trace _ _) $$ []
  · iframe #; ipureintro; exact Htr
  (try wp_auto)
  iapply HΦ
  isplitr
  · iunfold mvcc.compactChan; iexists γc; iexact Hrcv
  iunfold mvcc.compactQueue
  iexists Ps ++ [p], post, mvcc.compactTok γ (sint.Z rev), iprop(True)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  iframe Hq Hpost
  isplitr
  · itrivial
  iintro ⟨H, -⟩
  iexact H

end proof

end EtcdGrove
end Perennial
