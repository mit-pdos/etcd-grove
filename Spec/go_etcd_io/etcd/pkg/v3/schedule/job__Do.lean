/-
`job.Do` (`pkg/schedule/schedule.go`), translated with its body. Lean-first (2026-10-13, mvcc's
compaction, unit 5a).
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

/-- `j.Do(ctx)` of a `job` value whose closure has a job's triple: the closure's. -/
abbrev schedule.job.Do.spec : Prop :=
  ∀ (γ : schedule.SchedNames) (jv : go_etcd_io.etcd.pkg.v3.schedule.job) (ctx : GoInterfaceOk)
    (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (Pre Prev Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ schedule.jobFnSpec γ jv.do' Pre Prev Post ∗ schedule.schedRunning γ ∗ Pre ∗ Prev ∗
      _root_.Perennial.context.isContext ctx cd }}
    (App (Val (jv @!! go_etcd_io.etcd.pkg.v3.schedule.job.ty @!! go!"Do")) (Val #(GoInterface.ok ctx)))
  {{ RET #(); schedule.schedRunning γ ∗ Post }}

end spec

end EtcdGrove
end Perennial
