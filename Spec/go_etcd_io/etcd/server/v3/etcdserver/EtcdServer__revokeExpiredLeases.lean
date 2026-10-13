/-
`(*EtcdServer).revokeExpiredLeases(leases)` (`server.go`): the trust boundary (names-only; the
server's `run` calls it with the lessor's expired leases). Lean-first (the request path's unit 4c).
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

/-- `s.revokeExpiredLeases(leases)` returns (names-only: it `GoAttach`es a goroutine that revokes
the leases through raft if the member is the leader). -/
abbrev EtcdServer.revokeExpiredLeases.spec : Prop :=
  ∀ (s : Loc) (l : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"revokeExpiredLeases")) (Val #l))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
