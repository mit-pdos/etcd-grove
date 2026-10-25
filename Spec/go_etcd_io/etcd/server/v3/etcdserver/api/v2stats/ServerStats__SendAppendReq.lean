/-
`(*v2stats.ServerStats).SendAppendReq(reqSize)`: the trust boundary (v2stats is names-only;
`Transport.Send` calls it for each `MsgApp` it hands to a peer; rafthttp stage 6c, as
`RecvAppendReq`'s). Lean-first.
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

/-- `st.SendAppendReq(n)` on a non-nil `*ServerStats` returns.

Why it is true of the Go code (`v2stats/server.go:114-129`, `queue.go` at the etcd pin): it takes
the stats' mutex, becomes leader (`becomeLeader`: the state and the start time, if not leader
already), inserts a fresh `RequestStats` into its 200-slot ring (`statsQueue.Insert`, under the
queue's own `RWMutex`; the total size an `int` that wraps, no panic), counts the request and
unlocks; it only touches the stats' own fields, which only its methods read, under the same
locks. -/
abbrev v2stats.ServerStats.SendAppendReq.spec : Prop :=
  ∀ (st : Loc) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜st ≠ null⌝ }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"SendAppendReq")) (Val #n))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
