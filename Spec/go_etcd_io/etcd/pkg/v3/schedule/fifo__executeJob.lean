/-
`(*fifo).executeJob` (`schedule.go`). Lean-first (2026-10-22, the scheduler translated with its
body).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- What `executeJob(todo, false)` takes besides the job's: the worker's half of the state,
running the job (untracked: its `Post` is `True`; tracked, with its `prev` at index `k`: its `post`
at index `k + 1`), which its deferred function, under the lock, sets back to idle, depositing the
job's `Post` as the baton (`pendings[1:]` drops the job). -/
def schedule.finishPre (γ : schedule.SchedNames) (F : schedule.FifoNames) (Post : IProp GF) :
    IProp GF :=
  iprop(∃ rs : schedule.RunSt, dghostVar F.w (DFrac.own (1 : Qp).half) rs ∗
    match rs with
    | .runU => ⌜Post = iprop(True)⌝
    | .runT k => ∃ ps : GName, monoListIdxOwn γ.jobs (k + 1) ps ∗ schedule.savedProp ps Post
    | _ => iprop(False))

/-- **`f.executeJob(todo, upd)`**: runs the job (its `Do`, with the run token, `Pre` and `Prev`,
with `f.ctx`); with `upd = false` (the worker's loop) its deferred function, under the lock, counts
it finished and drops it from `f.pendings`, the worker idle again (`finishPre`); with `upd = true`
(the jobs taken after `Stop`) only the job runs, its `Post` returned. -/
abbrev schedule.fifo.executeJob.spec : Prop :=
  ∀ (l : Loc) (γ : schedule.SchedNames) (F : schedule.FifoNames) (j : GoInterface)
    (Pre Prev Post : IProp GF) (upd : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.fifoIs l γ F ∗ schedule.schedRunning γ ∗ schedule.jobIs γ j Pre Prev Post ∗ Pre ∗
      Prev ∗ (if upd then iprop(True) else schedule.finishPre γ F Post) }}
    (App (App (Val (l @!! go.GoType.PointerType schedule.fifo.ty @!! go!"executeJob")) (Val #j))
      (Val #upd))
  {{ RET #(); schedule.schedRunning γ ∗
      (if upd then Post else dghostVar F.w (DFrac.own (1 : Qp).half) schedule.RunSt.idle) }}

end spec

end EtcdGrove
end Perennial
