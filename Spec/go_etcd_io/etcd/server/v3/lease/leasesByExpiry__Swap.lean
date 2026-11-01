/-
`leasesByExpiry.Swap` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); the lease-read plan
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

/-- `le.Swap(i, j)` on the slice `sl` of the leases `ls`, `i`, `j` in range. -/
abbrev lease.leasesByExpiry.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (ls : List Loc) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦* ls ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ls[sint.nat i]? = some a ∧ ls[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! leasesByExpiry.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); sl ↦* (ls.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end EtcdGrove
end Perennial
