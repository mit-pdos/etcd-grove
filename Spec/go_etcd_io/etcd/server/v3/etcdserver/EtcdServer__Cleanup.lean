/-
`(*EtcdServer).Cleanup()` (`server.go`): the trust boundary (names-only; the last step of `run`'s
shutdown before `close(s.done)`). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Cleanup()` returns (names-only: it closes the backend and the WAL). -/
abbrev EtcdServer.Cleanup.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
