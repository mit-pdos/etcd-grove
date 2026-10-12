/-
`txn.RangeSecObserve`: the trust boundary (`metrics.go` is names-only: a prometheus histogram,
a float division). Lean-first. It records a range's latency: no effect here.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `RangeSecObserve(success, latency)` returns. -/
abbrev txn.RangeSecObserve.spec : Prop :=
  ∀ (success : Bool) (latency : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (Val (@! txn.RangeSecObserve)) (Val #success)) (Val #latency))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
