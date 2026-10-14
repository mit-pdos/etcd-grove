/-
`(*lessor).Promote` (`server/lease/lessor.go`, names only: the trust boundary). Lean-first (no
Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Promote(extend)` (write-locked): makes the lessor primary (a fresh `demotec`), refreshes
every lease's expiry, registers it with the expiry notifier and schedules its checkpoint, and
spreads out the expiries of piled-up leases (float arithmetic, a float-to-integer conversion,
`sort.Sort` of the leases by `Remaining()`, which read-locks each lease's `expiryMu`); it touches
only the lessor's memory under its lock. -/
abbrev lease.lessor.Promote.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Promote")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
