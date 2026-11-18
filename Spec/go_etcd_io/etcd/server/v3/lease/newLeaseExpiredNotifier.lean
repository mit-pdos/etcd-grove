/-
`newLeaseExpiredNotifier()` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart);
translated with its body for `Demote` (the lessor-noax stage, 2026-11-18).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `newLeaseExpiredNotifier()`: a fresh notifier, its map and queue empty. -/
abbrev lease.newLeaseExpiredNotifier.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (Val (@! newLeaseExpiredNotifier)) (Val #()))
  {{ (np : Loc), RET #np; notifierAt np 1 }}

end spec

end EtcdGrove
end Perennial
