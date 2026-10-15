/-
`(*v2stats.ServerStats).BecomeLeader()`: the trust boundary (v2stats is names-only; the
server's ready handler calls it when it becomes the leader). Lean-first (the request path's unit 4c).
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

/-- `st.BecomeLeader()` on a non-nil `*ServerStats` returns. -/
abbrev v2stats.ServerStats.BecomeLeader.spec : Prop :=
  ∀ (st : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜st ≠ null⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"BecomeLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
