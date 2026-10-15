/-
`(*EtcdServer).purgeFile()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
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

/-- `s.purgeFile()` returns (names-only: it purges old snapshot and WAL files until `stopping` is closed). -/
abbrev EtcdServer.purgeFile.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"purgeFile")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
