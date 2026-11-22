/-
`(*v2stats.statsQueue).Insert(p)` (`queue.go`; `ServerStats`' `RecvAppendReq` and
`SendAppendReq` call it under the stats' mutex). Lean-first (prove-ps2-v2stats, 2026-11-21).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Defs

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

/-- `q.Insert(p)` on a rate queue (`v2stats.isStatsQueue`) of a `RequestStats` `p` (persistently:
the queue keeps it) returns: under the queue's write lock, `p` stored in the 200-slot ring (the
oldest dropped when it is full, its `Size` read) and its `Size` added (an `int`, wrapping). -/
abbrev v2stats.statsQueue.Insert.spec : Prop :=
  ∀ (q p : Loc) (rs : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.RequestStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats ∗
      v2stats.isStatsQueue q ∗ p ↦□ rs }}
    (App (Val (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.statsQueue.ty @!! go!"Insert")) (Val #p))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
