/-
`txn.ApplySecObserve`: the trust boundary (`metrics.go` is names-only: a prometheus histogram,
a float division). Lean-first. It records an apply's latency (the apply package calls it): no
effect here.
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

/-- `ApplySecObserve(version, op, success, latency)` returns. -/
abbrev txn.ApplySecObserve.spec : Prop :=
  ∀ (ver op : GoString) (success : Bool) (latency : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (App (App (Val (@! txn.ApplySecObserve)) (Val #ver)) (Val #op)) (Val #success))
      (Val #latency))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
