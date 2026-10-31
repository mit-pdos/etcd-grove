/-
`schedule.NewFIFOScheduler` (`schedule.go`), proved since 2026-10-22, when the scheduler was translated
with its body (the trust boundary until then). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- `schedule.NewFIFOScheduler(lg)`, with a non-nil logger (`verify.Assert` otherwise), returns a
scheduler (`isFifo`, persistent: a `Scheduler` interface value with its names; its goroutine holds
the run token, `schedRunning`, which it lends each job it runs), the stop token, and the queue (the stop
token's name `n`, then the tracked jobs' `Post`s' names, here the initial one, `True`) (the request path's unit
4c: the FIFO chain; mvcc's store gives up the stop token, `schedLive_of_stopTok`, for
`isScheduler`); and (M2, the storage side, 2026-10-30: review round 3's F2) with the payload
`Pay` the caller fixes (`schedPayIs γ Pay`: the scheduler's context is done with it, so `Stop`
presents it and a job finding the context cancelled learns it). -/
abbrev schedule.NewFIFOScheduler.spec : Prop :=
  ∀ (lg : Loc) (Pay : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ ⌜lg ≠ null⌝ }}
    (App (Val (@! schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; ∃ (γ : schedule.SchedNames) (n p₀ : GName),
      schedule.isFifo sc γ ∗ schedule.schedStopTok γ ∗ schedule.schedQueue γ [n, p₀] ∗
      schedule.savedProp p₀ iprop(True) ∗ schedule.schedPayIs γ Pay }}

end spec

end EtcdGrove
end Perennial
