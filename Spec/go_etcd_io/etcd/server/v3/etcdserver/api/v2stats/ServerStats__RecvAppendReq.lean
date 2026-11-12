/-
`(*v2stats.ServerStats).RecvAppendReq(leader, reqSize)`: the trust boundary (v2stats is names-only;
`EtcdServer.Process` calls it for each received `MsgApp`). Lean-first (D21 M2, 2026-10-19, the
user's D21h (A)).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `st.RecvAppendReq(leader, n)` on a non-nil `*ServerStats` returns.

Why it is true of the Go code (`v2stats/server.go:91-110`, `queue.go` at the etcd pin): it takes the
stats' mutex, sets the state to follower and the leader's name and start time (`time.Now()`),
inserts a fresh `RequestStats` into its 200-slot ring (`statsQueue.Insert`, under the queue's own
`RWMutex`; the total size an `int` that wraps, no panic), counts the request and unlocks; it only
touches the stats' own fields, which only its methods read, under the same locks. -/
abbrev v2stats.ServerStats.RecvAppendReq.spec : Prop :=
  ∀ (st : Loc) (leader : GoString) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗ ⌜st ≠ null⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats.ty @!! go!"RecvAppendReq")) (Val #leader)) (Val #n))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
