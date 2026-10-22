/-
`(*fifo).Schedule` (`schedule.go`). Lean-first (2026-10-22, the scheduler translated with its
body; `Proof/go_etcd_io/etcd/pkg/v3/schedule/Defs.lean`, "The `fifo` scheduler").
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

/-- **`f.Schedule(j)`** on the `*fifo` `l`: `Scheduler.Schedule`'s contract (the job and its
`Pre` go to the pending jobs under the lock; tracked, its `post` appended to the queue). -/
abbrev schedule.fifo.Schedule.spec : Prop :=
  ∀ (l : Loc) (γ : schedule.SchedNames) (F : schedule.FifoNames) (j : GoInterface)
    (Pre Prev Post : IProp GF) (tr : Option (List GName × GName × GName)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.fifoIs l γ F ∗ schedule.jobIs γ j Pre Prev Post ∗ Pre ∗
      schedule.schedPre γ tr Prev Post }}
    (App (Val (l @!! go.GoType.PointerType schedule.fifo.ty @!! go!"Schedule")) (Val #j))
  {{ RET #(); schedule.schedPost γ tr }}

end spec

end EtcdGrove
end Perennial
