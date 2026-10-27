/-
The lessor's backend, as the lessor's writes use it (2026-10-13, unit 9). Lean-first (no Rocq
counterpart).

`Lease.persistTo(b)` (`Grant`, `Checkpoint`) takes the backend's batch lock inside the apply
(`tx.LockInsideApply()`), writes the lease's record into the `Lease` bucket
(`schema.MustUnsafePutLease`: one `tx.UnsafePut(Lease, ...)`) and unlocks. `leaseBackend b P f`
is that much of the backend `b` (an interface the lessor holds): `BatchTx()` returns a batch
transaction whose `LockInsideApply()`, under the batch lock's critical-section contract
`mvcc.csContract P f Pre Q Post` (the lock's invariant `P`, the post-lock hook `f`: the apply
package's environment), for a write-back token `T` and a lent open share `R` of the backend
(2026-10-17, unit N4, D14f: the real backend's `Unlock` spends a write-back, its `LockInsideApply`
needs the backend open), gives a token `Lk (Post ∗ R)` that `UnsafePut` into the `Lease` bucket
keeps and `Unlock()` turns into `Post ∗ R`. The put takes the right `Rb r` to write the tracked
buckets `r` (the real backend's client half of them, `backend.rbOwn`: the bucket is tracked, D22)
and gives back `Rb (mvcc.rbSet r "lease" k v)` (leases T3, L3c, 2026-10-27: until then the put had
no effect a caller could see; `Rb` defaults to no right and no effect). A contract on the lessor's environment (as mvcc's `isKeyBackend`
was for the store before `BackendBridge.lean`): not yet proved of the real backend.

`lessorBackend lp P f`: the lessor's `b` is such a backend (`newLessor` sets it; `Recover`,
names-only, replaces it under the lessor's lock: D22 receiver epochs, S7c, the field half the
lock's, half its user's, `lessorBeOn`, which the write token lends).

`lessorExpiredC lp GA`: the lessor's `expiredC` (read-only), the channel `ExpiredLeasesC`
returns, of slices of leases each of which met the lessor's grant guard `GA` (D19n, 2026-10-18:
the expiry loop sends only non-empty slices of leases of its map; until then no logical content);
a server whose guard is `False` receives nothing from it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The batch transaction `tx`** as the lessor's writes use it (persistent): `LockInsideApply()`
under the critical-section contract gives the lock's token `Lk Post`; `UnsafePut` into the
`Lease` bucket (the value of `schema.Lease`) of an 8-byte key (a lease's id: unit N4, 2026-10-17;
an empty key is fatal in the real backend) keeps it and puts the entry into the tracked buckets
`Rb` holds (L3c); `Unlock()` gives `Post`. -/
def leaseBatchTx (tx : GoInterfaceOk) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True)) : IProp GF :=
  iprop(∃ Lk : IProp GF → IProp GF,
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ T ∗ R }}
        (App (Val #(methods tx.ty go!"LockInsideApply" tx.v)) (Val #()))
      {{ RET #(); Lk iprop(Post ∗ R) }}) ∗
    □ (∀ (R : IProp GF) (bk : GoInterface) (key val : GoSlice) (kb vb : GoString)
        (r : GMap GoString backend.BktData),
      {{ ⌜kb.length = 8⌝ ∗ Lk R ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk ∗
          key ↦*□ kb ∗ val ↦*□ vb ∗ Rb r }}
        (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #bk)) (Val #key))
          (Val #val))
      {{ RET #(); Lk R ∗ Rb (mvcc.rbSet r mvcc.leaseName kb vb) }}) ∗
    □ (∀ (R : IProp GF),
      {{ Lk R }} (App (Val #(methods tx.ty go!"Unlock" tx.v)) (Val #())) {{ RET #(); R }}))

instance leaseBatchTx_persistent (tx : GoInterfaceOk) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) : Persistent (leaseBatchTx tx P f T R Rb) := by
  unfold leaseBatchTx; infer_instance

/-- **The backend `b`** as the lessor uses it (persistent): the `Lease` bucket variable of
`schema` holds a fixed value, and `BatchTx()` returns a `leaseBatchTx`. -/
def leaseBackend (b : GoInterface) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True)) : IProp GF :=
  iprop((∃ bk : GoInterface, globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk) ∗
    ∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterfaceOk), RET #(GoInterface.ok tx); leaseBatchTx tx P f T R Rb }}))

instance leaseBackend_persistent (b : GoInterface) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) : Persistent (leaseBackend b P f T R Rb) := by
  unfold leaseBackend; infer_instance

/-- **The lessor's backend** (persistent): a `leaseBackend` `b`, and the write token `T` lends a
fraction of the lessor's `b` field at `b` (D22 receiver epochs, S7c, 2026-10-23: the field is no
longer read-only, `Recover` replaces it; until then `lF "b" lp ↦□ b`, which that store refutes):
the writes read `le.b` under the lessor's lock, holding the token. -/
def lessorBackend (lp : Loc) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True)) : IProp GF :=
  iprop(∃ b : GoInterface, leaseBackend b P f T R Rb ∗
    □ (T -∗ ∃ dq : DFrac, lF go!"b" lp ↦{dq} b ∗ (lF go!"b" lp ↦{dq} b -∗ T)))

instance lessorBackend_persistent (lp : Loc) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) : Persistent (lessorBackend lp P f T R Rb) := by
  unfold lessorBackend; infer_instance

/-- **The lessor `lp` is on the backend at `be`** (D22 receiver epochs, S7c, 2026-10-23; not
persistent): its user's half of `le.b` (the other half is the lessor's lock's, `lessorExtra`), the
backend's `*backend` at `be`. The writes' contract (`NewLessor`'s) takes it in their write right,
so that it names the backend they write to; `Recover` replaces both halves under the lock. -/
def lessorBeOn (lp be : Loc) : IProp GF :=
  iprop(lF go!"b" lp ↦{DFrac.own (1 : Qp).half}
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
      #be : GoInterface))

/-- The lessor's `expiredC` (persistent): read-only, a channel of slices of leases, some lease of
each meeting the grant guard `GA` (D19n). -/
def lessorExpiredC (lp : Loc) (GA : w64 → IProp GF) : IProp GF :=
  iprop(∃ (c : GoChan) (γc : ChanNames), lF go!"expiredC" lp ↦□ c ∗
    isChanBag γc c (V := GoSlice) (fun _ => iprop(∃ id : w64, GA id)))

instance lessorExpiredC_persistent (lp : Loc) (GA : w64 → IProp GF) :
    Persistent (lessorExpiredC (GF := GF) lp GA) := by
  unfold lessorExpiredC; infer_instance

end defs

end lease
end EtcdGrove
end Perennial
