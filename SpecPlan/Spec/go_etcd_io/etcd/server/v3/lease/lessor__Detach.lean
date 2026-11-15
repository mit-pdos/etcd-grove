/-
## `(*lessor).Detach(id, items)` (`lessor.go:582`)

**Users.** mvcc (3e), on the apply thread through the `Lessor` interface: `put` replacing a key's
lease (`kvstore_txn.go:273`) and `delete` (`:338`), each with the lease `GetLease` returned (error
logged), so also from inside a revocation's deletes (`rdOk`). Snippet `lessor.go`
(`ReqAttachDetach`).

**Proof sketch.** As `Attach.spec`: `le.mu`, the lease absent: `ErrLeaseNotFound`; present: under
`l.mu`, delete each item from `itemSet` and from `itemMap`; the history appended with
`ls.detach id ks`.

**Changes** (from `specs-ref`'s `lessor__Detach.lean`, `deleteAll` with the premise that the items
are on the lease): over the lessor's state, the premise dropped (`itemMap` loses the items whatever
lease they named: `LessorState.detach`). **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **Detach keys from lease `id`** (the writer): `ErrLeaseNotFound` for a lease not live, nothing
changed; else `nil`, the keys detached (`LessorState.detach`). -/
def lessor.Detach.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id : w64) (sl : GoSlice)
    (its : List go_etcd_io.etcd.server.v3.lease.LeaseItem) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ sl ↦*{dq} its }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Detach")) (Val #id)) (Val #sl))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} its ∗
      ((⌜ls.leases (sint.Z id) = none⌝ ∗ errIs go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound err ∗
        lessorState γ n ls) ∨
       (⌜ls.leases (sint.Z id) ≠ none ∧ err = interface.nil⌝ ∗
        lessorState γ (n + 1) (ls.detach (sint.Z id) (its.map (·.Key'))))) }}

end spec
end Lease
end EtcdGrove
end Perennial
