/-
`(*lessor).unsafeLeases()` (`lessor.go:464`), an internal helper's spec (mirrors the code).
**Users**: `Leases` (under `RLock`), `Promote`. **Proof sketch**: a slice of capacity
`len(leaseMap)`, the map's values appended (map iteration: each once). **Changes** (from
`specs-ref`'s `lessor__unsafeLeases.lean`): over `lessorFields`. **Margin**: the order.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The live objects** (under the lock), each once, in a fresh slice. -/
def lessor.unsafeLeases.spec : Prop :=
  ∀ (le : Loc) (c : Cfg) (dq : DFrac) (ls : LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorFields le c dq ls }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"unsafeLeases")) (Val #()))
  {{ (sl : GoSlice), RET #sl; lessorFields le c dq ls ∗ ∃ (ps : List Loc) (ids : List Int),
      sl ↦* ps ∗ ⌜ids.Nodup ∧ (∀ x, x ∈ ids ↔ ls.leases x ≠ none) ∧
        List.Forall₂ (fun p x => ∃ e, ls.leases x = some e ∧ p = e.obj) ps ids⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial
