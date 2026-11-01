/-
`leasesByExpiry.Less` (`server/lease/lease.go`). Lean-first (no Rocq counterpart); the lease-read plan
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

/-- `le.Less(i, j)` on the slice `sl` of the leases `ls` of the lessor of `γl`, `i`, `j` in range,
on any goroutine with a thread token (`Remaining()` of each, at most `2^30 - 1` live threads): some
answer (`le[i].Remaining() < le[j].Remaining()`, read off the clock: no fixed order of the leases). -/
abbrev lease.leasesByExpiry.Less.spec : Prop :=
  ∀ (γl : GName) (sl : GoSlice) (ls : List Loc) (dq : DFrac) (i j : w64) (a b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ sl ↦*{dq} ls ∗
      ([∗list] l ∈ ls, isLeaseObj γl l) ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ls[sint.nat i]? = some a ∧ ls[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! leasesByExpiry.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ (r : Bool), RET #r; sl ↦*{dq} ls ∗ threadTok }}

end spec

end EtcdGrove
end Perennial
