/-
`leasesByExpiry.Len` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); the lease-read plan
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

/-- `le.Len()` on the slice `sl` of the leases `ls`: their number. -/
abbrev lease.leasesByExpiry.Len.spec : Prop :=
  ∀ (sl : GoSlice) (ls : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦*{dq} ls }}
    (App (Val (sl @!! leasesByExpiry.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 ls.length); sl ↦*{dq} ls }}

end spec

end EtcdGrove
end Perennial
