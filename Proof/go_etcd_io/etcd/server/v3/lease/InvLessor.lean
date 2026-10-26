/-
The lessor's lock and what it holds (`server/lease/lessor.go`, 2026-10-13, unit 8 of the
backend). Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The lessor's KV-facing
methods and the live leases (unit 8)".

**The lock** `le.mu` (an `RWMutex`, `lessorMu lp γl`): the fields `leaseMap` (the granted leases,
id to `*Lease`), `itemMap` (item to lease id) and `rd` (the range deleter), and the lessor's half
of the **live-lease set**: a ghost variable `γl` (the store's `γ.leases`) at `(lp, L)`, `L` the
domain of `leaseMap`. Every `*Lease` of the map is `isLeaseObj`: not nil, its own lock `l.mu`
guarding its `itemSet`.

**The lease owner's half** (`leaseOwn γl L`): the other half of `γl`, held by the apply thread
(the one goroutine that grants and revokes leases: `lessor.Grant`/`Revoke` run only in the
applier). Holding it, `L` is the live set: `Attach(id, …)` of an `id ∈ L` succeeds, `Lookup(id)`
returns non-nil exactly for `id ∈ L`. A lease known live is a pure fact `id ∈ L` relative to the
half the caller holds, not a persistent fact: `Revoke` takes the half and shrinks `L`.

**The readers** (`lessorRd lp γl`): `GetLease` and `Lookup` take `le.mu`'s read lock, which needs a
reader slot (`sync.ownRWMutex`); the writers (`Attach`, `Detach`, `SetRangeDeleter`) only the
guard.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.SavedProp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace go_etcd_io.etcd.server.v3.lease

deriving instance DecidableEq for LeaseItem

end go_etcd_io.etcd.server.v3.lease

namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section fields
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&le.<f>` -/
abbrev lF (f : GoString) (lp : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.lessor f lp

/-- `&l.<f>` (a `*Lease`) -/
abbrev lsF (f : GoString) (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.Lease f l

/-- `&it.<f>` (a `*LeaseWithTime`) -/
abbrev lwF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.LeaseWithTime f p

/-- `&n.<f>` (a `*LeaseExpiredNotifier`) -/
abbrev nF (f : GoString) (p : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier f p

/-- The lessor `lp` as a `Lessor` interface value. -/
abbrev lessorIface (lp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty) #lp

end fields

section keys
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [LeaseItem.TypeAssumptions]

/-- A `LeaseItem` is its key: its Go value determines it (the field read is deterministic). -/
instance leaseItem_intoValInj [go.BasicIntoValInj] : go.IntoValInj LeaseItem where
  intoVal_inj x y h := by
    have hx := (LeaseItem.TypeAssumptions.get_Key x).isGoStep_det_internal.isGoStep_pure_det
    have hy := (LeaseItem.TypeAssumptions.get_Key y).isGoStep_det_internal.isGoStep_pure_det
    rw [h] at hx
    have h2 := congrFun (hx.symm.trans hy) (Val #(x.Key'))
    simp only [eq_iff_iff, true_iff] at h2
    have h3 : (#(x.Key') : val) = #(y.Key') := by
      have := h2.symm
      injection this
    have h4 : x.Key' = y.Key' := go.intoVal_inj h3
    cases x; cases y
    simp only at h4
    subst h4; rfl

end keys

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The right to close a lease's `revokec`** (unit T3, 2026-10-24): `NewLease` makes it,
`Revoke` closes the channel with it. -/
def revokeCloser (c : GoChan) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan c γc Unit ∗ ownChan γc Unit .Idle)

/-- What a lease's lock `l.mu` guards: half of its item set (unit T3, L2b, 2026-10-25: the other
half is the lease owner's, `leaseItemsOwn`, so that `Keys()` under the read lock returns the set
the owner knows). -/
def leaseItems (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own q.half} sm ∗
    sm ↦${DFrac.own q.half} S)

/-- **The item set `S` of the lease `id` is what the item map `I` attaches to it** (unit T3,
L2b). -/
def itemsFor (I : GMap LeaseItem w64) (id : w64) (S : GMap LeaseItem Unit) : Prop :=
  ∀ it : LeaseItem, S.lookup it = some () ↔ I.lookup it = some id

/-- `m` with every key of `xs` set to `v` (the item map and set after `Attach`'s loop). -/
def insertAll {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (v : V) : GMap K V :=
  xs.foldl (fun m k => m.insert k v) m

/-- `m` without the keys of `xs` (the item map and set after `Detach`'s loop). -/
def deleteAll {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) : GMap K V :=
  xs.foldl (fun m k => m.delete k) m

theorem insertAll_lookup {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (v : V)
    (k : K) : (insertAll m xs v).lookup k = if k ∈ xs then some v else m.lookup k := by
  induction xs generalizing m with
  | nil => simp [insertAll]
  | cons x xs ih =>
    have h : insertAll m (x :: xs) v = insertAll (m.insert x v) xs v := rfl
    rw [h, ih]
    rw [GMap.lookup_insert_eq_iff]
    by_cases hk : k ∈ xs
    · simp [hk]
    · by_cases hx : x = k
      · subst hx; simp [hk]
      · simp [hk, hx, Ne.symm hx]

theorem deleteAll_lookup {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (k : K) :
    (deleteAll m xs).lookup k = if k ∈ xs then none else m.lookup k := by
  induction xs generalizing m with
  | nil => simp [deleteAll]
  | cons x xs ih =>
    have h : deleteAll m (x :: xs) = deleteAll (m.delete x) xs := rfl
    rw [h, ih]
    rw [GMap.lookup_delete_iff]
    by_cases hk : k ∈ xs
    · simp [hk]
    · by_cases hx : x = k
      · subst hx; simp [hk]
      · simp [hk, hx, Ne.symm hx]

/-- **The lease owner's half of the item set of the lease `l`** (of id `id`), which is what the
item map `I` attaches to `id` (unit T3, L2b). -/
def leaseItemsOwn (l : Loc) (I : GMap LeaseItem w64) (id : w64) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own (1 : Qp).half} sm ∗
    sm ↦${DFrac.own (1 : Qp).half} S ∗ ⌜itemsFor I id S⌝)

/-- A lease of the map: not nil, its lock guarding its item set (persistent). -/
def isLeaseObj (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems l))

instance isLeaseObj_persistent (l : Loc) : Persistent (isLeaseObj (GF := GF) l) := by
  unfold isLeaseObj; infer_instance

/-- The values of the lessor's ghost map `γl`: at `false` its location, the name of its grant
guard (D19n) and (unit T3) of its closers' map `γcl` (lease id to `*Lease`), at `true` its live
set. -/
abbrev LessorGV := (Loc × GName × GName) ⊕ List w64

/-- The lessor's ghost map `γl`'s contents: its location and its grant guard's name `γga` at
`false` (pinned for good), its live set at `true`. -/
def lessorGhost (lp : Loc) (γga γcl : GName) (L : List w64) : GMap Bool LessorGV :=
  (((∅ : GMap Bool LessorGV).insert false (Sum.inl (lp, γga, γcl))).insert true (Sum.inr L))

/-- A share `q` of the live set `L` (the ghost map `γl`'s element `true`). -/
def leaseFrag (γl : GName) (q : Qp) (L : List w64) : IProp GF :=
  ghostMapElem γl true (DFrac.own q) (Sum.inr L : LessorGV)

/-- The lessor of `γl` is at `lp`, its grant guard named `γga`, its closers' map `γcl`
(persistent: the ghost map's element `false`, discarded). -/
def lessorPinG (γl : GName) (lp : Loc) (γga γcl : GName) : IProp GF :=
  ghostMapElem γl false DFrac.discard (Sum.inl (lp, γga, γcl) : LessorGV)

instance lessorPinG_persistent (γl : GName) (lp : Loc) (γga γcl : GName) :
    Persistent (lessorPinG (GF := GF) γl lp γga γcl) := by
  unfold lessorPinG; infer_instance

/-- The lessor of `γl` is at `lp` (persistent). -/
def lessorPin (γl : GName) (lp : Loc) : IProp GF :=
  iprop(∃ γga γcl : GName, lessorPinG γl lp γga γcl)

instance lessorPin_persistent (γl : GName) (lp : Loc) : Persistent (lessorPin (GF := GF) γl lp) := by
  unfold lessorPin; infer_instance

/-- **The lessor's grant guard** (D19n, 2026-10-18; persistent): the predicate `GA` its caller
chose at `NewLessor`, a saved predicate pinned in the lessor's ghost map. A lease is granted only
with `GA` of its id (`Grant`'s `leaseGranted`); so every lease of the lessor's map, and every
lease its expiry loop sends on `expiredC`, has it. A server whose policy admits no `LeaseGrant`
picks `GA := False`. -/
def lessorGuard (γl : GName) (GA : w64 → IProp GF) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName), lessorPinG γl lp γga γcl ∗
    savedPredOwn γga DFrac.discard GA)

instance lessorGuard_persistent (γl : GName) (GA : w64 → IProp GF) :
    Persistent (lessorGuard (GF := GF) γl GA) := by
  unfold lessorGuard; infer_instance

/-- **The lease `id` may be granted** (D19n; persistent): it meets the lessor's grant guard. -/
def leaseGranted (γl : GName) (id : w64) : IProp GF :=
  iprop(∃ GA : w64 → IProp GF, lessorGuard γl GA ∗ □ GA id)

instance leaseGranted_persistent (γl : GName) (id : w64) :
    Persistent (leaseGranted (GF := GF) γl id) := by
  unfold leaseGranted; infer_instance

/-- **The lessor's share `q` of its ghost map's authority**, at the live set `L`, every lease of
which may be granted (D19n); (unit T3) and of its closers' map, at the lease map `M`. -/
def lessorAuth (γl : GName) (q : Qp) (lp : Loc) (L : List w64) (M : GMap w64 Loc) : IProp GF :=
  iprop(∃ γga γcl : GName, ghostMapAuth γl q (lessorGhost lp γga γcl L) ∗ ghostMapAuth γcl q M ∗
    □ ([∗list] id ∈ L, leaseGranted γl id))

/-! ### The lessor's apply-side state (2026-10-13, unit 9)

`Grant`, `Checkpoint` (and `Promote`, `Demote`, the expiry loop) touch more of the lessor
under `le.mu`: the primary's channel `demotec`, the expiry notifier (a map from lease id to the
queue's item, and a heap of the items by expiry time), the checkpoint heap, the checkpointer, and
of each lease its `remainingTTL` and the lessor's half of its `expiry` (the other half is
`l.expiryMu`'s: `refresh`/`forever` write it holding both locks, `Grant` and the expiry loop read
it under `le.mu` alone, `Remaining` under `l.expiryMu` alone). -/

/-- Swap the elements at `i` and `j` (`h.Swap(i, j)`; unchanged out of range). -/
def listSwap {α : Type} (xs : List α) (i j : Nat) : List α :=
  match xs[i]?, xs[j]? with
  | some a, some b => (xs.set i b).set j a
  | _, _ => xs

/-- A queue item `&LeaseWithTime` at `p`, at share `q`: its `id` (read-only), its `time`, and
its `index` `k` (its position in its queue). -/
def lwtAt (p : Loc) (id : w64) (k : w64) (q : Qp) : IProp GF :=
  iprop(lwF go!"id" p ↦□ id ∗ (∃ t : _root_.Perennial.time.Time, lwF go!"time" p ↦{DFrac.own q} t) ∗
    lwF go!"index" p ↦{DFrac.own q} k)

/-- A `LeaseQueue` value `s` holding the items `xs` (pointer, lease id), at share `q`, each
item's `index` its position (what `heap.Fix(&q, old.index)` needs), with the slice's capacity
(`append`). -/
def queueAt (s : GoSlice) (xs : List (Loc × w64)) (q : Qp) : IProp GF :=
  iprop(s ↦*{DFrac.own q} (xs.map Prod.fst) ∗ ownSliceCap Loc s (DFrac.own q) ∗
    [∗list] k ↦ x ∈ xs, lwtAt x.1 x.2 (W64 k) q)

/-- **The expiry notifier** at `np` (`LeaseExpiredNotifier`), at share `q`: its map `m` (lease id
to item) holds exactly the items of its queue, each under its own id, no item twice. -/
def notifierAt (np : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (mp : Loc) (s : GoSlice) (M : GMap w64 Loc) (xs : List (Loc × w64)),
    nF go!"m" np ↦{DFrac.own q} mp ∗ mp ↦${DFrac.own q} M ∗ nF go!"queue" np ↦{DFrac.own q} s ∗
    queueAt s xs q ∗
    ⌜(xs.map Prod.fst).Nodup ∧ ∀ (id : w64) (p : Loc), M.lookup id = some p ↔ (p, id) ∈ xs⌝)

/-- What `l.expiryMu` guards at `q`: half of `l.expiry` at `q` (the other half is the lessor's,
in `leaseMeta`). -/
def leaseExpiry (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own q.half} e)

/-- **A granted lease's state** (`l`, of id `id`) under `le.mu`, at `q`: its `ID` and `ttl`
(read-only once granted), its `revokec` (read-only), its `remainingTTL` and the lessor's half
of `expiry`; its `expiryMu` guards the other half. -/
def leaseMeta (id : w64) (l : Loc) (q : Qp) : IProp GF :=
  iprop(lsF go!"ID" l ↦□ id ∗ (∃ t : w64, lsF go!"ttl" l ↦□ t) ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦□ c) ∗
    (∃ r : w64, lsF go!"remainingTTL" l ↦{DFrac.own q} r) ∗
    (∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own q.half} e) ∗
    sync.isRWMutexGuard (lsF go!"expiryMu" l) (leaseExpiry l))

/-- **The lessor's apply-side fields** under `le.mu` at `q`, for its lease map `M`: `demotec`,
the expiry notifier, the checkpoint heap (a queue of fresh items, any ids), the checkpointer
`cp`, and every granted lease's `leaseMeta`; (D22 receiver epochs, S7c, 2026-10-23) half the
fraction of the backend `b` (the other half its user's, `lessorBeOn`: `Recover` replaces it). -/
def lessorExtra (lp : Loc) (M : GMap w64 Loc) (q : Qp) : IProp GF :=
  iprop(∃ (dc : GoChan) (np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (cp : GoFunc)
      (b : GoInterface),
    lF go!"demotec" lp ↦{DFrac.own q} dc ∗
    lF go!"leaseExpiredNotifier" lp ↦{DFrac.own q} np ∗ notifierAt np q ∗
    lF go!"leaseCheckpointHeap" lp ↦{DFrac.own q} h ∗ queueAt h hx q ∗
    lF go!"cp" lp ↦{DFrac.own q} cp ∗
    ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗
    lF go!"b" lp ↦{DFrac.own q.half} b)

/-- **What `le.mu` guards** at fraction `q`: the lease map `M` (whose domain is the live set
`L`; the lessor's share of it, `q/2`, and of the ghost map's authority), half of the item map
(`q/2`: unit T3, L2b, the other half is the lease owner's, `leaseClosers`), half of
the range deleter (`q/2`: unit T3, the other half is `rdOwn`'s, since `Revoke` reads `le.rd`
after releasing the lock); every lease of the map `isLeaseObj`; and (2026-10-13, unit 9) the apply-side fields
(`lessorExtra`). -/
def lessorMu (lp : Loc) (γl : GName) (q : Qp) : IProp GF :=
  iprop(∃ (lm im : Loc) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (rd : GoFunc)
      (L : List w64),
    lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M ∗
    lF go!"itemMap" lp ↦{DFrac.own q.half} im ∗ im ↦${DFrac.own q.half} I ∗
    lF go!"rd" lp ↦{DFrac.own q.half} rd ∗
    lessorAuth γl q lp L M ∗ leaseFrag γl q.half L ∗
    ⌜∀ id : w64, id ∈ L ↔ (M.lookup id).isSome⌝ ∗
    ([∗map] _id ↦ l ∈ M, isLeaseObj l) ∗ lessorExtra lp M q)

/-- **The lessor** at `lp` with ghost map `γl` (persistent): pinned, its lock's guard. -/
def lessorInv (lp : Loc) (γl : GName) : IProp GF :=
  iprop(⌜lp ≠ null⌝ ∗ lessorPin γl lp ∗ sync.isRWMutexGuard (lF go!"mu" lp) (lessorMu lp γl))

instance lessorInv_persistent (lp : Loc) (γl : GName) :
    Persistent (lessorInv (GF := GF) lp γl) := by
  unfold lessorInv; infer_instance

/-- The lessor's `cluster` `cl` (2026-10-13, unit 9): not nil, its `Version()` returns `nil` or
a read-only version (the server's `RaftCluster`, names-only: a contract). -/
def clusterOk (cl : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cl = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Version" ci.v)) (Val #()))
      {{ (v : Loc), RET #v;
        ⌜v = null⌝ ∨ ∃ ver : github_com.Masterminds.semver.v3.Version, v ↦□ ver }}))

instance clusterOk_persistent (cl : GoInterface) : Persistent (clusterOk (GF := GF) cl) := by
  unfold clusterOk; infer_instance

/-- **The lessor's configuration** (2026-10-13, unit 9; persistent): the fields `newLessor` sets
and nothing writes after (`minLeaseTTL`, `checkpointPersist`, `cluster` with its contract,
`checkpointInterval`, `lg`, `leaseRevokeRate`, positive: `Promote` indexes the sorted leases'
first when there are at least `leaseRevokeRate` of them, so a rate below `1` with no lease panics;
audit B4b, 2026-10-18). -/
def lessorCfg (lp : Loc) : IProp GF :=
  iprop(∃ (mt : w64) (cpp : Bool) (cl : GoInterface) (ci : _root_.Perennial.time.Duration)
      (lg : Loc) (rr : w64),
    lF go!"minLeaseTTL" lp ↦□ mt ∗ lF go!"checkpointPersist" lp ↦□ cpp ∗
    lF go!"cluster" lp ↦□ cl ∗ clusterOk cl ∗
    lF go!"checkpointInterval" lp ↦□ ci ∗ lF go!"lg" lp ↦□ lg ∗
    lF go!"leaseRevokeRate" lp ↦□ rr ∗ ⌜0 < sint.Z rr⌝)

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 1024 in
instance lessorCfg_persistent (lp : Loc) : Persistent (lessorCfg (GF := GF) lp) := by
  unfold lessorCfg; infer_instance

/-- `err` is one of the lessor's error variables `Grant` returns (`ErrLeaseNotFound`,
`ErrLeaseExists`, `ErrLeaseTTLTooLarge`: `leaseErrVar` of the package's facts). -/
def lessorErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ (g : GoString) (e : GoInterfaceOk),
    ⌜g = ErrLeaseNotFound ∨ g = ErrLeaseExists ∨ g = ErrLeaseTTLTooLarge⌝ ∗
    globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)

instance lessorErrIs_persistent (err : GoInterface) : Persistent (lessorErrIs (GF := GF) err) := by
  unfold lessorErrIs; infer_instance

/-- A reader slot of the lessor's lock (`GetLease`, `Lookup`). -/
def lessorRd (lp : Loc) (γl : GName) : IProp GF :=
  sync.ownRWMutex (lF go!"mu" lp) (lessorMu lp γl)

/-- **The range deleter's owner** (unit T3, 2026-10-24): the other half of the lessor's `rd`
field, at `rd`. `SetRangeDeleter` takes it (with the lock's half it writes the field) and
`Revoke` reads the field by it, outside the lock. `NewLessor` gives it at `nil`; mvcc's
constructors set the store's deleter with it. -/
def rdOwn (γl : GName) (rd : GoFunc) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lF go!"rd" lp ↦{DFrac.own (1 : Qp).half} rd)

/-- **The owner's resource of the live lease `l`** (of id `id`; unit T3): the closers' map's
element, the right to close its `revokec`, (L2b) its half of the lease's item set (what the item
map `I` attaches to `id`). -/
def closerAt (γcl : GName) (I : GMap LeaseItem w64) (id : w64) (l : Loc) : IProp GF :=
  iprop(ghostMapElem γcl id (DFrac.own 1) l ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c) ∗ leaseItemsOwn l I id)

/-- **The lease owner's closers and items** (unit T3, 2026-10-24): for every lease of the live
set `L`, the closers' map's element (its `*Lease`, which the lessor's map agrees with), the right
to close its `revokec` and (L2b, 2026-10-25) the owner's half of its item set, the items the item
map `I` attaches to it; the owner's half of the item map `I`, every lease of which is live.
Exclusive, so outside `le.mu`'s fractional invariant. -/
def leaseClosers (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc) (im : Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    lF go!"itemMap" lp ↦{DFrac.own (1 : Qp).half} im ∗ im ↦${DFrac.own (1 : Qp).half} I ∗
    ⌜∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ ∗
    [∗map] id ↦ l ∈ C, closerAt γcl I id l)

/-- **The lease owner's half** of the live set: holding it, `L` is the live set (the apply
thread's); (unit T3) with the live leases' closers and (L2b) the item map `I` (item to lease id)
and the live leases' item sets, which agree with it. -/
def leaseOwn (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(leaseFrag γl (1 : Qp).half L ∗ leaseClosers γl L I)

/-- The owner's resource at an equal item map. -/
theorem leaseOwn_eq {γl : GName} {L : List w64} {I J : GMap LeaseItem w64} (h : I = J) :
    leaseOwn (GF := GF) γl L I ⊢ leaseOwn γl L J := by
  subst h; exact .rfl

/-- A reader slot of the lessor of `γl`, wherever it is (`lessorPin`). -/
def lessorRdOf (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lessorRd lp γl)

/-- **The lease owner's resource** at the txn layer: its half of the live set and a reader slot
of the lessor's lock (`Lookup`). -/
def lessorUser (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(leaseOwn γl L I ∗ lessorRdOf γl)

/-- Two pins of one ghost map agree. -/
theorem lessorPin_agree (γl : GName) (lp lp' : Loc) :
    lessorPin (GF := GF) γl lp ∗ lessorPin γl lp' ⊢ ⌜lp = lp'⌝ := by
  unfold lessorPin lessorPinG
  iintro ⟨⟨%γ1, %γ1', H1⟩, ⟨%γ2, %γ2', H2⟩⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

/-- Two shares of the live set agree. -/
theorem leaseFrag_agree (γl : GName) (q1 q2 : Qp) (L1 L2 : List w64) :
    leaseFrag (GF := GF) γl q1 L1 ∗ leaseFrag γl q2 L2 ⊢ ⌜L1 = L2⌝ := by
  unfold leaseFrag
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  ipureintro
  have h2 := H.2
  cases h2; rfl

end defs

end lease
end EtcdGrove
end Perennial
