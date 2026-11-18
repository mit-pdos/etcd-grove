/-
**What `lessor.initAndRecover` makes** (the lease-expiry plan's S1, 2026-11-04): the leases it
recovers from the `Lease` bucket's records, before they join the lessor (`Recover`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI

/-- **The lease map of the recovered leases** `xs` (each a record `(id, ttl, rem)` with its
`*Lease`), inserted in order into `m` (`le.leaseMap[ID] = &Lease{...}`). -/
def recMapFrom (m : GMap w64 Loc) (xs : List ((w64 × w64 × w64) × Loc)) : GMap w64 Loc :=
  xs.foldl (fun m p => m.insert p.1.1 p.2) m

/-- The lease map of the recovered leases, from an empty map. -/
abbrev recMap (xs : List ((w64 × w64 × w64) × Loc)) : GMap w64 Loc := recMapFrom ∅ xs

/-- **The TTLs of the recovered leases** (`lpb.TTL` raised to the minimum `mt`). -/
def recTTLsFrom (mt : w64) (m : GMap w64 w64) (xs : List (w64 × w64 × w64)) : GMap w64 w64 :=
  xs.foldl (fun m x => m.insert x.1 (grantTTL mt x.2.1)) m

/-- The TTLs of the recovered leases, from an empty map. -/
abbrev recTTLs (mt : w64) (xs : List (w64 × w64 × w64)) : GMap w64 w64 := recTTLsFrom mt ∅ xs

/-! ### Maps built by inserting a list's elements in order (`recMapFrom`, `recTTLsFrom`) -/

section fold
variable {α K V : Type} [DecidableEq K]

end fold

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end defs

end lease
end EtcdGrove
end Perennial
