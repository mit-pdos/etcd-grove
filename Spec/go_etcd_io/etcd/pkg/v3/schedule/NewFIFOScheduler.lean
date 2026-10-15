/-
`schedule.NewFIFOScheduler`: the trust boundary (`pkg/v3/schedule` is names-only). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `schedule.NewFIFOScheduler(lg)`, with a non-nil logger (`verify.Assert` otherwise), returns a
scheduler (`isFifo`, persistent: a `Scheduler` interface value with its names; its goroutine holds
the run token, `schedRunning`, which it lends each job it runs), the stop token, and the queue (the stop
token's name `n`, then the tracked jobs' `Post`s' names, here the initial one, `True`) (the request path's unit
4c: the FIFO chain; mvcc's store gives up the stop token, `schedLive_of_stopTok`, for
`isScheduler`). -/
abbrev schedule.NewFIFOScheduler.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ ⌜lg ≠ null⌝ }}
    (App (Val (@! schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; ∃ (γ : schedule.SchedNames) (n p₀ : GName),
      schedule.isFifo sc γ ∗ schedule.schedStopTok γ ∗ schedule.schedQueue γ [n, p₀] ∗
      schedule.savedProp p₀ iprop(True) }}

end spec

end EtcdGrove
end Perennial
