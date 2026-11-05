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
the expiry loop sends only non-empty slices of leases of its map; until then no logical content;
the lease-expiry plan's X3, 2026-11-04: the slice and each lease's `ID` read-only, `expiredLeases`);
a server whose guard is `False` receives nothing from it. (The lease-grant plan, 2026-11-02, D1)
A slice is sent only once a lease has expired, so each also refutes the deployment premise
`leasesNoExpiry` (no lease granted in the run expires before the run ends): a server whose guard
implies that premise receives nothing either.
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

/-- **No lease of any lessor the program creates expires while the program runs** (a named premise
about the program's deployment, as `leasePeersOk`; the lease-grant plan's S2 (a), the user's choice
of 2026-11-02, restated by the review's S3, `notes/lease-grant-plan.md`, and after the axiom review
of 2026-11-02, `notes/axiom-review/lease-grant-lessor.md`, which refuted the earlier "no lease the
cluster grants": `NewLessor`'s payload reads the premise for every lessor, and a program with a
standalone lessor and a 1 s lease met that wording yet saw an expiry): no lease of any lessor the
program creates (in a cluster or none; granted there, or reloaded by `Recover`) expires, by the clock
the lessor's expiry loop reads, while the program runs. So no lessor's loop (`runLoop`,
`revokeExpiredLeases`, `lessor.go:620-660` at the etcd pin) finds an expired lease
(`findExpiredLeases` returns only leases whose `expiry` is past) and none sends on `expiredC`.

What the theorem reads it over: the program's run ends when `Main` returns (Go exits), but the
adequacy theorem's executions also continue the other goroutines after that (steps Go never takes),
and the premise is read over them too: as used (the payload of `expiredC` refutes it, below), it
says no slice is ever sent on `expiredC`, in any of the theorem's executions.

True of `examples/etcd/leasegrant`: its only lease is granted with TTL 600 s, and the read that must list
it runs within two `RequestTimeout`s of the grant's apply (the expiry is set to at least the grant's
apply plus the TTL, and `Promote`, `Demote`, `Renew`, checkpoints and `minLeaseTTL` only move it
later, `lessor.go:301-303, 480-553`). What a theorem taking it says nothing of: runs longer than a granted lease's TTL, runs
whose clock jumps, and a lessor promoted with leases whose expiry has already passed. The
trust-boundary `NewLessor` states it in the payload of `expiredC` (`lessorExpiredC`): a slice sent
refutes it. `NewServer` takes it (gated on the cluster granting leases, `KVNames.lg = true`, review
S1) for its apply thread, the one place a grant is minted. -/
opaque leasesNoExpiry : Prop

-- `Mode`: `InvLessor.lean` (moved 2026-11-04, X7 option (iii): `KVNames` and `AEnv` name it).

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **The lessor's backend** (persistent): a `leaseBackend` `b`, and the lent part `Ln` lends a
fraction of the lessor's `b` field at `b` (D22 receiver epochs, S7c, 2026-10-23: the field is no
longer read-only, `Recover` replaces it; until then `lF "b" lp ↦□ b`, which that store refutes):
the writes read `le.b` under the lessor's lock, holding it. (The lease-grant stage, 2.12,
2026-11-02) The lent part is apart from the write token `T`, which the write spends: `Grant` and
`Checkpoint` give `Ln` back; until then the token lent the field and was spent with it.) -/
def lessorBackend (lp : Loc) (P : IProp GF) (f : val) (T Ln R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF := fun _ => iprop(True)) : IProp GF :=
  iprop(∃ b : GoInterface, leaseBackend b P f T R Rb ∗
    □ (Ln -∗ ∃ dq : DFrac, lF go!"b" lp ↦{dq} b ∗ (lF go!"b" lp ↦{dq} b -∗ Ln)))

instance lessorBackend_persistent (lp : Loc) (P : IProp GF) (f : val) (T Ln R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) :
    Persistent (lessorBackend lp P f T Ln R Rb) := by
  unfold lessorBackend; infer_instance

/-- **The lessor `lp` is on the backend at `be`** (D22 receiver epochs, S7c, 2026-10-23; not
persistent): its user's half of `le.b` (the other half is the lessor's lock's, `lessorExtra`), the
backend's `*backend` at `be`. The writes' contract (`NewLessor`'s) takes it in their write right,
so that it names the backend they write to; `Recover` replaces both halves under the lock. -/
def lessorBeOn (lp be : Loc) : IProp GF :=
  iprop(lF go!"b" lp ↦{DFrac.own (1 : Qp).half}
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
      #be : GoInterface))

/-- (the lease-expiry plan's X3, 2026-11-04) **A slice of expired leases `ls`**, as the lessor's
expiry loop sends it on `expiredC` (`revokeExpiredLeases`, `lessor.go:640-660` at the etcd pin):
read-only, its elements `ps` non-empty (`if len(ls) != 0`), each a non-null `*Lease` of the lessor's
map whose `ID` (never written after `NewLease`) is read-only at `id`, with the grant guard `GA id`
(every lease of the map was granted under it, `lessorAuth`'s `leaseGranted`). What the server's
`revokeExpiredLeases` reads (`curLease.ID`). -/
def expiredLeases (GA : w64 → IProp GF) (ls : GoSlice) : IProp GF :=
  iprop(∃ ps : List Loc, ⌜ps ≠ []⌝ ∗ ls ↦*□ ps ∗
    [∗list] p ∈ ps, ⌜p ≠ null⌝ ∗ ∃ id : w64, lsF go!"ID" p ↦□ id ∗ GA id)

instance expiredLeases_persistent (GA : w64 → IProp GF) [∀ id, Persistent (GA id)] (ls : GoSlice) :
    Persistent (expiredLeases GA ls) := by
  unfold expiredLeases; infer_instance

/-- The lessor's `expiredC` (persistent): read-only, a channel of slices of leases each meeting the
grant guard `GA` (D19n; the lease-expiry plan's X3, 2026-11-04: the slice's elements, read-only,
with their `ID`s, `expiredLeases`; until then only "some lease of each meets `GA`"), (the lease-grant
plan's D1, 2026-11-02) each sent only once a lease has expired, so refuting `leasesNoExpiry`. -/
def lessorExpiredC (lp : Loc) (GA : w64 → IProp GF) : IProp GF :=
  iprop(∃ (c : GoChan) (γc : ChanNames), lF go!"expiredC" lp ↦□ c ∗
    isChanBag γc c (V := GoSlice) (fun ls => iprop(⌜¬ leasesNoExpiry⌝ ∗ expiredLeases GA ls)))

instance lessorExpiredC_persistent (lp : Loc) (GA : w64 → IProp GF) :
    Persistent (lessorExpiredC (GF := GF) lp GA) := by
  unfold lessorExpiredC; infer_instance

/-- (2026-11-04, R2b-3c part 2, the user's approval; trust boundary) **The right to stop the lessor
`lp` once**: `NewLessor` gives it, `lessor.Stop` takes it (`close(le.stopC)`, which a second call
would make panic). Exclusive by use: nothing duplicates it. -/
axiom lessorStopTok (lp : Loc) : IProp GF
@[instance] axiom lessorStopTok_timeless (lp : Loc) : Timeless (lessorStopTok (GF := GF) lp)

end defs

section ttl
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **A lease granted asked for a positive TTL has a positive TTL in the history** (the lease-expiry
plan's R5, 2026-11-04): from `lessor.Grant`'s success (`leaseLiveFrom`, its `ttl` field at
`grantTTL`). -/
theorem leaseGrant_ttl (γl : GName) (m : Nat) (id : w64) (l : Loc) (mt ttl : w64) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ∗ leaseLiveFrom γl m id l ∗ lsF go!"ttl" l ↦□ grantTTL mt ttl ⊢
      |={E}=> ∃ (i : Nat) (t : w64), ⌜m ≤ i ∧ sint.Z ttl ≤ sint.Z t⌝ ∗ leaseTTLAt γl i id t := by
  iintro H
  imod leaseLiveFrom_ttl γl m id l _ E hE $$ H with ⟨%i, %hi, #Ht⟩
  imodintro
  iexists i, grantTTL mt ttl
  iframe Ht
  ipureintro; exact ⟨hi, grantTTL_ge mt ttl⟩

end ttl

end lease
end EtcdGrove
end Perennial
