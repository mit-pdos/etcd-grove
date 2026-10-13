/-
`(*EtcdServer).publishV3(timeout)` (`server.go`): names-only, one of the goroutines `Start` attaches. Lean-first (the request path's unit 4c).
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

/-- `s.publishV3(timeout)` returns (names-only: it publishes the member's attributes through raft
until it succeeds or `stopping` is closed). -/
abbrev EtcdServer.publishV3.spec : Prop :=
  ∀ (s : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"publishV3")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
