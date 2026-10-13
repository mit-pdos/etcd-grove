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

/-- `schedule.NewFIFOScheduler(lg)` returns a scheduler (`isScheduler`, persistent: a
`Scheduler` interface value with its names; its goroutine holds the run token, `schedRunning`,
which it lends each job it runs; the store keeps it for the compaction's jobs). -/
abbrev schedule.NewFIFOScheduler.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule }}
    (App (Val (@! schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; ∃ γ : schedule.SchedNames, schedule.isScheduler sc γ }}

end spec

end EtcdGrove
end Perennial
