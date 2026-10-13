/-
`LeaseQueue.Swap` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart); see
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

/-- `pq.Swap(i, j)`, `i` and `j` in range: swaps the two items and sets their indices. -/
abbrev lease.LeaseQueue.Swap.spec : Prop :=
  ∀ (s : GoSlice) (xs : List (Loc × w64)) (i j : w64),
  0 ≤ sint.Z i → sint.Z i < xs.length → 0 ≤ sint.Z j → sint.Z j < xs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ queueAt s xs 1 }}
    (App (App (Val (s @!! LeaseQueue.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); queueAt s (listSwap xs (sint.nat i) (sint.nat j)) 1 }}

end spec

end EtcdGrove
end Perennial
