/-
`(*Lease).refresh` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); see
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

/-- `l.refresh(extend)`, with the lessor's half of `l.expiry` (the caller holds `le.mu`): sets the
expiry to some time (`time.Now()` plus `extend` and the remaining TTL), under `l.expiryMu`. -/
abbrev lease.Lease.refresh.spec : Prop :=
  ∀ (l : Loc) (d : _root_.Perennial.time.Duration) (r t : w64) (dq1 dq2 : DFrac)
    (e : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lsF go!"remainingTTL" l ↦{dq1} r ∗ lsF go!"ttl" l ↦{dq2} t ∗
      lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} e ∗
      sync.isRWMutexGuard (lsF go!"expiryMu" l) (leaseExpiry l) }}
    (App (Val (l @!! go.GoType.PointerType Lease.ty @!! go!"refresh")) (Val #d))
  {{ RET #(); lsF go!"remainingTTL" l ↦{dq1} r ∗ lsF go!"ttl" l ↦{dq2} t ∗
      ∃ e' : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own (1 : Qp).half} e' }}

end spec

end EtcdGrove
end Perennial
