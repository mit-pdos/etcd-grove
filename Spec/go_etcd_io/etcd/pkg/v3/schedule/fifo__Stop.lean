/-
`(*fifo).Stop` (`schedule.go`). Lean-first (2026-10-22, the scheduler translated with its body).
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

/-- **`f.Stop()`** on the `*fifo` `l`, with the stop token and the queue: it cancels the
context (the scheduler now stopped) and waits for the worker to exit. -/
abbrev schedule.fifo.Stop.spec : Prop :=
  ∀ (l : Loc) (γ : schedule.SchedNames) (F : schedule.FifoNames) (Ps : List GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.fifoIs l γ F ∗ schedule.schedStopTok γ ∗ schedule.schedQueue γ Ps }}
    (App (Val (l @!! go.GoType.PointerType schedule.fifo.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
