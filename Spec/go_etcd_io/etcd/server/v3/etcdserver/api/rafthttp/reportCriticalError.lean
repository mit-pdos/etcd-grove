/-
`reportCriticalError(err, errc)` (`util.go`; rafthttp stage 5e-3). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ReaderRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`reportCriticalError(err, errc)`**: `err` (an error whose `Error()` returns) offered to the
critical-error channel without blocking (`errcOk`): sent, or dropped if no receiver is ready. -/
abbrev rafthttp.reportCriticalError.spec : Prop :=
  ∀ (err : GoInterface) (ec : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ errcOk ec ∗ http.errStrOk err }}
    (App (App (Val (@! rafthttp.reportCriticalError)) (Val #err)) (Val #ec))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
