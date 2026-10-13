/-
`read.isStopped(err)` (read.go). Lean-first (no Rocq counterpart); the request path's unit 4a, see
`Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Inv.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.read

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `isStopped(err)` of an error `errors.Is` can take (`applyErrIs`): whether it is raft's or the
server's `ErrStopped` (the result is not specified: the loop returns on it, safely). -/
abbrev read.isStopped.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      applyErrIs err }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.read.isStopped)) (Val #err))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
