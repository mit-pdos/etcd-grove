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

/-- What a lease's lock `l.mu` guards: its item set. -/
def leaseItems (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own q} sm ∗
    sm ↦${DFrac.own q} S)

/-- A lease of the map: not nil, its lock guarding its item set (persistent). -/
def isLeaseObj (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems l))

instance isLeaseObj_persistent (l : Loc) : Persistent (isLeaseObj (GF := GF) l) := by
  unfold isLeaseObj; infer_instance

/-- The lessor's ghost map `γl`'s contents: its location at `false` (pinned for good), its live
set at `true`. -/
def lessorGhost (lp : Loc) (L : List w64) : GMap Bool (Loc ⊕ List w64) :=
  (((∅ : GMap Bool (Loc ⊕ List w64)).insert false (Sum.inl lp)).insert true (Sum.inr L))

/-- A share `q` of the live set `L` (the ghost map `γl`'s element `true`). -/
def leaseFrag (γl : GName) (q : Qp) (L : List w64) : IProp GF :=
  ghostMapElem γl true (DFrac.own q) (Sum.inr L : Loc ⊕ List w64)

instance leaseFrag_timeless (γl : GName) (q : Qp) (L : List w64) :
    Timeless (leaseFrag (GF := GF) γl q L) := by
  unfold leaseFrag; infer_instance

/-- The lessor of `γl` is at `lp` (persistent: the ghost map's element `false`, discarded). -/
def lessorPin (γl : GName) (lp : Loc) : IProp GF :=
  ghostMapElem γl false DFrac.discard (Sum.inl lp : Loc ⊕ List w64)

instance lessorPin_persistent (γl : GName) (lp : Loc) : Persistent (lessorPin (GF := GF) γl lp) := by
  unfold lessorPin; infer_instance

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
`cp`, and every granted lease's `leaseMeta`. -/
def lessorExtra (lp : Loc) (M : GMap w64 Loc) (q : Qp) : IProp GF :=
  iprop(∃ (dc : GoChan) (np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (cp : GoFunc),
    lF go!"demotec" lp ↦{DFrac.own q} dc ∗
    lF go!"leaseExpiredNotifier" lp ↦{DFrac.own q} np ∗ notifierAt np q ∗
    lF go!"leaseCheckpointHeap" lp ↦{DFrac.own q} h ∗ queueAt h hx q ∗
    lF go!"cp" lp ↦{DFrac.own q} cp ∗
    [∗map] id ↦ l ∈ M, leaseMeta id l q)

/-- **What `le.mu` guards** at fraction `q`: the lease map `M` (whose domain is the live set
`L`; the lessor's share of it, `q/2`, and of the ghost map's authority), the item map, the range
deleter; every lease of the map `isLeaseObj`; and (2026-10-13, unit 9) the apply-side fields
(`lessorExtra`). -/
def lessorMu (lp : Loc) (γl : GName) (q : Qp) : IProp GF :=
  iprop(∃ (lm im : Loc) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (rd : GoFunc)
      (L : List w64),
    lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M ∗
    lF go!"itemMap" lp ↦{DFrac.own q} im ∗ im ↦${DFrac.own q} I ∗
    lF go!"rd" lp ↦{DFrac.own q} rd ∗
    ghostMapAuth γl q (lessorGhost lp L) ∗ leaseFrag γl q.half L ∗
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
`checkpointInterval`, `lg`, `leaseRevokeRate`). -/
def lessorCfg (lp : Loc) : IProp GF :=
  iprop(∃ (mt : w64) (cpp : Bool) (cl : GoInterface) (ci : _root_.Perennial.time.Duration)
      (lg : Loc) (rr : w64),
    lF go!"minLeaseTTL" lp ↦□ mt ∗ lF go!"checkpointPersist" lp ↦□ cpp ∗
    lF go!"cluster" lp ↦□ cl ∗ clusterOk cl ∗
    lF go!"checkpointInterval" lp ↦□ ci ∗ lF go!"lg" lp ↦□ lg ∗
    lF go!"leaseRevokeRate" lp ↦□ rr)

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

/-- **The lease owner's half** of the live set: holding it, `L` is the live set (the apply
thread's). -/
def leaseOwn (γl : GName) (L : List w64) : IProp GF := leaseFrag γl (1 : Qp).half L

instance leaseOwn_timeless (γl : GName) (L : List w64) : Timeless (leaseOwn (GF := GF) γl L) := by
  unfold leaseOwn; infer_instance

/-- A reader slot of the lessor of `γl`, wherever it is (`lessorPin`). -/
def lessorRdOf (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lessorRd lp γl)

/-- **The lease owner's resource** at the txn layer: its half of the live set and a reader slot
of the lessor's lock (`Lookup`). -/
def lessorUser (γl : GName) (L : List w64) : IProp GF :=
  iprop(leaseOwn γl L ∗ lessorRdOf γl)

/-- Two pins of one ghost map agree. -/
theorem lessorPin_agree (γl : GName) (lp lp' : Loc) :
    lessorPin (GF := GF) γl lp ∗ lessorPin γl lp' ⊢ ⌜lp = lp'⌝ := by
  unfold lessorPin
  iintro ⟨H1, H2⟩
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
