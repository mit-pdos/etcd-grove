/-
`schedule.NewJob` (`pkg/schedule/schedule.go`), translated with its body. Lean-first (2026-10-13,
mvcc's compaction, unit 5a).
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

/-- `NewJob(name, do)` of a closure `do` with a job's triple (`jobFnSpec`: with the run token,
`Pre` and `Prev`, for any context, returns the token and `Post`): a job (`jobIs`: the
`job{name, do}` struct as a `Job` interface value, whose `Do` calls `do`). -/
abbrev schedule.NewJob.spec : Prop :=
  ∀ (γ : schedule.SchedNames) (name : GoString) (f : GoFunc) (Pre Prev Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ schedule.jobFnSpec γ f Pre Prev Post }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.schedule.NewJob)) (Val #name)) (Val #f))
  {{ (j : GoInterface), RET #j; schedule.jobIs γ j Pre Prev Post }}

end spec

end EtcdGrove
end Perennial
