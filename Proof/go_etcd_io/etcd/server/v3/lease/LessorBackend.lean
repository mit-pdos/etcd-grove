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
keeps and `Unlock()` turns into `Post ∗ R`. A contract on the lessor's environment (as mvcc's `isKeyBackend`
was for the store before `BackendBridge.lean`): not yet proved of the real backend.

`lessorBackend lp P f`: the lessor's `b` (read-only: `newLessor` sets it; `Recover`, not
proved, would replace it) is such a backend.

`lessorExpiredC lp`: the lessor's `expiredC` (read-only), the channel `ExpiredLeasesC` returns,
of slices of leases with no logical content (the server's `run` passes them on to the
names-only `revokeExpiredLeases`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Golang.Theory.Chan.Idioms.Bag

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
an empty key is fatal in the real backend) keeps it; `Unlock()` gives `Post`. -/
def leaseBatchTx (tx : GoInterfaceOk) (P : IProp GF) (f : val) (T R : IProp GF) : IProp GF :=
  iprop(∃ Lk : IProp GF → IProp GF,
    □ (∀ (Pre Q Post : IProp GF),
      {{ mvcc.csContract P f Pre Q Post ∗ T ∗ R }}
        (App (Val #(methods tx.ty go!"LockInsideApply" tx.v)) (Val #()))
      {{ RET #(); Lk iprop(Post ∗ R) }}) ∗
    □ (∀ (R : IProp GF) (bk : GoInterface) (key val : GoSlice) (kb vb : GoString),
      {{ ⌜kb.length = 8⌝ ∗ Lk R ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk ∗
          key ↦*□ kb ∗ val ↦*□ vb }}
        (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #bk)) (Val #key))
          (Val #val))
      {{ RET #(); Lk R }}) ∗
    □ (∀ (R : IProp GF),
      {{ Lk R }} (App (Val #(methods tx.ty go!"Unlock" tx.v)) (Val #())) {{ RET #(); R }}))

instance leaseBatchTx_persistent (tx : GoInterfaceOk) (P : IProp GF) (f : val) (T R : IProp GF) :
    Persistent (leaseBatchTx tx P f T R) := by
  unfold leaseBatchTx; infer_instance

/-- **The backend `b`** as the lessor uses it (persistent): the `Lease` bucket variable of
`schema` holds a fixed value, and `BatchTx()` returns a `leaseBatchTx`. -/
def leaseBackend (b : GoInterface) (P : IProp GF) (f : val) (T R : IProp GF) : IProp GF :=
  iprop((∃ bk : GoInterface, globalAddr go_etcd_io.etcd.server.v3.storage.schema.Lease ↦□ bk) ∗
    ∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
      {{ (tx : GoInterfaceOk), RET #(GoInterface.ok tx); leaseBatchTx tx P f T R }}))

instance leaseBackend_persistent (b : GoInterface) (P : IProp GF) (f : val) (T R : IProp GF) :
    Persistent (leaseBackend b P f T R) := by
  unfold leaseBackend; infer_instance

/-- **The lessor's backend** (persistent): its `b` field, read-only, a `leaseBackend`. -/
def lessorBackend (lp : Loc) (P : IProp GF) (f : val) (T R : IProp GF) : IProp GF :=
  iprop(∃ b : GoInterface, lF go!"b" lp ↦□ b ∗ leaseBackend b P f T R)

instance lessorBackend_persistent (lp : Loc) (P : IProp GF) (f : val) (T R : IProp GF) :
    Persistent (lessorBackend lp P f T R) := by
  unfold lessorBackend; infer_instance

/-- The lessor's `expiredC` (persistent): read-only, a channel of slices of leases with no
logical content. -/
def lessorExpiredC (lp : Loc) : IProp GF :=
  iprop(∃ (c : GoChan) (γc : ChanNames), lF go!"expiredC" lp ↦□ c ∗
    isChanBag γc c (V := GoSlice) (fun _ => iprop(True)))

instance lessorExpiredC_persistent (lp : Loc) : Persistent (lessorExpiredC (GF := GF) lp) := by
  unfold lessorExpiredC; infer_instance

end defs

end lease
end EtcdGrove
end Perennial
