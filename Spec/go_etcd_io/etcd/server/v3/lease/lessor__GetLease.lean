/-
## `(*lessor).GetLease(item)` (`lessor.go:573`)

**Users.** mvcc's write path (3e), on the apply thread through the `Lessor` interface: `put`
(`kvstore_txn.go:233`, the key's previous lease), `delete` (`:335`, the lease to detach), so also
from inside a revocation's deletes (`rdOk`). Snippet `lessor.go` (`ReqAttachDetach`).

**Proof sketch.** `le.mu.RLock()`; `itemMap[item]` (`0` if absent) at the current state `j ≥ i`;
`RUnlock`. The writer, holding `lessorState γ n ls`, gets `ls.items k`.

**Changes** (from `specs-ref`'s `lessor__GetLease.lean`, the owner's item map `I`): the same read,
over the history (one spec for any caller). **Margin.** None.
**Round 1.** A reader token (`lessorReaders γ 1`: the slot of the `RWMutex` it read-locks; the
writer borrows one, `lessorState_reader`), the bounds plan's reader slots.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **The lease key `k` is attached to** (`itemMap`, `0` for none), at a state `j ≥ i`. -/
def lessor.GetLease.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (i : Nat) (k : Key),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorReaders γ 1 ∗ lessorLb γ i }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"GetLease")) (Val #(go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k)))
  {{ (r : w64), RET #r; lessorReaders γ 1 ∗ ∃ (j : Nat) (ls : LessorState), ⌜i ≤ j⌝ ∗ lessorAt γ j ls ∗
      ⌜r = W64 (ls.items k)⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial
