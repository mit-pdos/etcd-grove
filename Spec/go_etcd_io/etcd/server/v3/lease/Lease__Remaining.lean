/-
`(*Lease).Remaining` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); the lease-read plan
(`notes/lease-read-plan.md`, 2026-10-31).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `l.Remaining()` (read-locks `l.expiryMu`), on any goroutine, with a thread token, with which it
borrows a reader slot of `l.expiryMu` from the lease's pool (at most `2^30 - 1` live threads): some
duration (the time until the expiry, read off the clock, or `MaxInt64` if the expiry is unset); no
claim on it (it changes with the clock and with `refresh`). -/
abbrev lease.Lease.Remaining.spec : Prop :=
  ∀ (γl : GName) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj γl l ∗
      threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"Remaining")) (Val #()))
  {{ (d : _root_.Perennial.time.Duration), RET #d; threadTok }}

end spec

end EtcdGrove
end Perennial
