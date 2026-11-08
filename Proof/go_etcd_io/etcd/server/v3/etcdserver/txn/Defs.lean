/-
What the txn package's functions are given (Lean-first): the lessor with its `Lookup`
(`isTxnLessor`). The store is mvcc's API (strict M1, 2026-11-05: `mvcc.api.isMvcc`, the
transactions `mvcc.api.mvccTxn`; `ApiVocab.lean` has the caller's updates); until then this file
also had `isKV` (the store over mvcc's internals) and the writer's parts (`wlogOwn`).

**`isTxnLessor le γl`**: mvcc's `isLessor` (what the store calls: `GetLease`, `Attach`,
`Detach`, `SetRangeDeleter`) and `Lookup(id)`, which `checkLease` calls: for the lease owner
(`lease.lessorUser γl L`) it returns `nil` or a lease of the live set `L`, which mvcc's `Put` of a
key with that lease needs (with the owner's half, `lease.leaseOwn`). Both are derived from the
lessor's proofs (2026-10-13, unit 8 of the backend; they were the trust boundary).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- The `lease.Lessor` `le` as the txn package uses it: mvcc's contract, and `Lookup(id)` by the
lease owner (`lease.lessorUser γl L`: its half of the live set `L`, a reader slot of the lessor's
lock) returns `nil` exactly when `id` is not live (`id ∉ L`; 2026-10-13, unit 8 of the backend:
derived from the lessor's proof, `lease.isTxnLessor_of_lessorInv`; unit T3, L3b, 2026-10-26: until
then `nil` or a live lease), and a lease is the owner's lease of `id`: the owner's resource comes
back opened at it (`lease.lessorUserOpen`, whose `Keys()` reads the item set; the lease-keys plan,
item 4, 2026-10-31). -/
def isTxnLessor (le : GoInterface) (γl : GName) : IProp GF :=
  iprop(mvcc.isLessor le γl ∗ ∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ (∀ (id : w64) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64),
      {{ lease.lessorUser γl L I }} (App (Val #(methods li.ty go!"Lookup" li.v)) (Val #id))
      {{ (l : Loc), RET #l; lease.lessorUserOpen γl L I id l ∗ ⌜l = null ↔ id ∉ L⌝ }}))

instance isTxnLessor_persistent (le : GoInterface) (γl : GName) :
    Persistent (isTxnLessor (GF := GF) le γl) := by
  unfold isTxnLessor; infer_instance

end defs

end txn
end EtcdGrove
end Perennial
