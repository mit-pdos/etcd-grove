/-
`(*Lease).forever` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
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

/-- `l.forever()`, with the lessor's half of `l.expiry`: sets the expiry to `forever` (the zero
time), under `l.expiryMu`. -/
abbrev lease.Lease.forever.spec : Prop :=
  ∀ (l : Loc) (e : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} e ∗
      sync.isRWMutexGuard (lsF go!"expiryMu" l) (leaseExpiry l) }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"forever")) (Val #()))
  {{ RET #(); lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} (zero_val _root_.Perennial.time.Time) }}

end spec

end EtcdGrove
end Perennial
