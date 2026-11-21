/-
`(*Lease).expired` (`server/lease/lease.go:51`). Lean-first (no Rocq counterpart); prove-ps2-renew
(2026-11-21), `lessor.Renew`'s callee.
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

/-- `l.expired()` (`l.Remaining() <= 0`), on any goroutine, with the level-0 token of the lease's
leveled pool (as `Remaining`'s, which it returns): some boolean (no claim on it: it changes with the
clock and with `refresh`). -/
abbrev lease.Lease.expired.spec : Prop :=
  ∀ (γl : GName) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLeaseObj γl l ∗
      levelTok leaseLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"expired")) (Val #()))
  {{ (b : Bool), RET #b; levelTok leaseLvl }}

end spec

end EtcdGrove
end Perennial
