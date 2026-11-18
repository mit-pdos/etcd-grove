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
public import Perennial.Ghost.MonoList
public import Perennial.Proof.ThreadPool
public import Spec.go_uber_org.zap.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace go_etcd_io.etcd.server.v3.lease

deriving instance DecidableEq for LeaseItem

/-- A `LeaseItem` is countable through its key (ghost state stores item sets: Part B). -/
instance LeaseItem.countable [GooseExts] : Pos.Countable LeaseItem :=
  .ofInjective (fun it => Pos.Countable.encode it.Key')
    (fun a b h => by cases a; cases b; simp only at h; rw [Pos.encode_inj h])

end go_etcd_io.etcd.server.v3.lease

namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

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
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [LeaseItem.TypeAssumptions]

end keys

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The right to close a lease's `revokec`** (unit T3, 2026-10-24): `NewLease` makes it,
`Revoke` closes the channel with it. -/
def revokeCloser (c : GoChan) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan c γc Unit ∗ ownChan γc Unit .Idle)

/-- **The lessor's reader-side ghost names** (the lease-keys plan, Part B, 2026-10-31): the
history of its snapshots (`γr.1`, a monotone list) and the item sets' map (`γr.2.1`, each `*Lease`
to its item set); (the lease-grant plan's D2, 2026-11-02) and the lessor's **mode** (`γr.2.2.1`):
`true` for a lessor whose history is monotone (no lease ever leaves its map: `histMono`, which its
`Revoke` and `Recover` would break, so they take the other mode, `lessorRevocable`), fixed by
`NewLessor`'s caller; (the lease-expiry plan's E3 (c), 2026-11-05) and the ids the lessor ever
had (`γr.2.2.2.1`, a ghost variable `U` in halves: `lessorRdBody`'s and the owner's, `leaseEver`);
(the lease-expiry plan's S2–S4, Q-S6, 2026-11-05) and the TTLs the leases were requested at
(`γr.2.2.2.2`, a ghost map of discarded elements, id to requested TTL: `leaseReqIs`, `reqOk`).
The mode is `γr.2.2.1`. -/
abbrev LessorRdNames := GName × GName × Bool × GName × GName

/-- **A snapshot of the lessor**: its lease map (id to `*Lease`), its item map (item to id) and
(the lease-expiry plan's R5, 2026-11-04) its TTLs (id to the lease's `ttl` field, which `Grant` and
`Recover` set before the lease enters the map and nothing writes after: `ttlTie`). -/
abbrev LSnap := GMap w64 Loc × GMap LeaseItem w64 × GMap w64 w64

/-- The values of the lessor's ghost map `γl`: at `false` its location, the name of its grant
guard (D19n), (unit T3) of its closers' map `γcl` (lease id to `*Lease`) and (Part B) its
reader-side names, at `true` its live set. -/
abbrev LessorGV := (Loc × GName × GName × LessorRdNames) ⊕ List w64

/-- The lessor's ghost map `γl`'s contents: its location and its names at `false` (pinned for
good), its live set at `true`. -/
def lessorGhost (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) (L : List w64) :
    GMap Bool LessorGV :=
  (((∅ : GMap Bool LessorGV).insert false (Sum.inl (lp, γga, γcl, γr))).insert true (Sum.inr L))

/-- A share `q` of the live set `L` (the ghost map `γl`'s element `true`). -/
def leaseFrag (γl : GName) (q : Qp) (L : List w64) : IProp GF :=
  ghostMapElem γl true (DFrac.own q) (Sum.inr L : LessorGV)

/-- The lessor of `γl` is at `lp`, its grant guard named `γga`, its closers' map `γcl` and its
reader-side names `γr` (persistent: the ghost map's element `false`, discarded). -/
def lessorPinAll (γl : GName) (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) : IProp GF :=
  ghostMapElem γl false DFrac.discard (Sum.inl (lp, γga, γcl, γr) : LessorGV)

/-- The lessor of `γl` is at `lp`, its grant guard named `γga`, its closers' map `γcl`
(persistent). -/
def lessorPinG (γl : GName) (lp : Loc) (γga γcl : GName) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinAll γl lp γga γcl γr)

/-- The lessor of `γl` has the reader-side names `γr` (persistent). -/
def lessorPinR (γl : GName) (γr : LessorRdNames) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName), lessorPinAll γl lp γga γcl γr)

/-- The lessor of `γl` is at `lp` (persistent). -/
def lessorPin (γl : GName) (lp : Loc) : IProp GF :=
  iprop(∃ γga γcl : GName, lessorPinG γl lp γga γcl)

/-- What a lease's lock `l.mu` guards: half of its item set (unit T3, L2b, 2026-10-25: the other
half is the lease owner's, `leaseItemsOwn`, so that `Keys()` under the read lock returns the set
the owner knows) and (Part B, 2026-10-31) the lease's element of the lessor `γl`'s item sets' map
at the same set, so that `Keys()` under a reader's read lock returns the set the lessor's history
records (`lessorRdInv`). -/
def leaseItems (γl : GName) (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit) (γr : LessorRdNames), lessorPinR γl γr ∗
    lsF go!"itemSet" l ↦{DFrac.own q.half} sm ∗ sm ↦${DFrac.own q.half} S ∗
    ghostMapElem γr.2.1 l (DFrac.own q) S)

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

/-- **Every key of the item map `I` is shorter than `2 ^ 63 - 1` bytes** (the lease-keys plan, Q4
(b), 2026-10-31): what the auth store's checks take of each key `Keys()` returns
(`IsPutPermitted`); a key gets it from the request that put it (`Attach`'s premise). -/
def itemKeysShort (I : GMap LeaseItem w64) : Prop :=
  ∀ (it : LeaseItem) (id : w64), I.lookup it = some id → (it.Key'.length : Int) < 2 ^ 63 - 1

/-! ### The lessor from a reader (the lease-keys plan, Part B, 2026-10-31)

A goroutine other than the lease owner (the server's API layer: `checkLeaseRenew`, ...) looks a
lease up and reads its keys. What it learns is stated over the **history** of the lessor's
snapshots (lease map, item map), which the owner appends to at each change, under `le.mu`'s write
lock: a reader with a lower bound `m` of the history (`lessorLb`) finds the lease map of an index
`≥ m` (`leaseLiveFrom`, `leaseAbsentFrom`), and the keys of a lease `l` of `id` at an index `≥ m`
where the lease map has `l` (`leaseKeysFrom`): each `*Lease`'s item set is its id's items at the
last index the lease map has it (`setsOk`; frozen at its revocation: Go's `Revoke` does not clear
`l.itemSet`, and the id can be granted again). -/

/-- **`l` is the lease of `id` at the index `i` of `hs`, and at no later index.** -/
def lastLiveAt (hs : List LSnap) (id : w64) (l : Loc) (i : Nat) : Prop :=
  (∃ σ, hs[i]? = some σ ∧ σ.1.lookup id = some l) ∧
    ∀ (j : Nat) (σ : LSnap), i < j → hs[j]? = some σ → σ.1.lookup id ≠ some l

/-- **Every `*Lease` of the history is the lease of one id.** -/
def oneIdPerLease (hs : List LSnap) : Prop :=
  ∀ (i j : Nat) (σ τ : LSnap) (id id' : w64) (l : Loc), hs[i]? = some σ → hs[j]? = some τ →
    σ.1.lookup id = some l → τ.1.lookup id' = some l → id = id'

/-- **The item sets agree with the history**: every lease of the history has a set (so a `*Lease`
`Grant` has just made, not in the map `Sm`, is in no snapshot: the Probe, 2026-10-31); and each
`*Lease`'s set is its id's items at the last index the lease map has it, or, if no lease map of the
history has it yet, empty (`Grant` registers a new lease's empty set when it makes the lease's
lock, before it takes `le.mu` and puts the lease in the map; a lease `Grant` then refuses,
`ErrLeaseExists`, stays there, never live). -/
def setsOk (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)) : Prop :=
  (∀ (i : Nat) (σ : LSnap) (id : w64) (l : Loc), hs[i]? = some σ → σ.1.lookup id = some l →
    (Sm.lookup l).isSome) ∧
  ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S →
    ((∀ (i : Nat) (σ : LSnap) (id : w64), hs[i]? = some σ → σ.1.lookup id ≠ some l) ∧ S = ∅) ∨
    ∃ (id : w64) (i : Nat) (σ : LSnap), lastLiveAt hs id l i ∧ hs[i]? = some σ ∧ itemsFor σ.2.1 id S

/-- **The history's facts**: not empty, each lease under one id, every snapshot's keys short. -/
def histOk (hs : List LSnap) : Prop :=
  hs ≠ [] ∧ oneIdPerLease hs ∧ ∀ σ ∈ hs, itemKeysShort σ.2.1

/-- **No lease leaves the history's lease maps** (the lease-grant plan's D2, 2026-11-02): an id
live at an index is live at every later one (the monotone mode's invariant: `lessorRdBody`). -/
def histMono (hs : List LSnap) : Prop :=
  ∀ (i j : Nat) (σ τ : LSnap) (id : w64), i ≤ j → hs[i]? = some σ → hs[j]? = some τ →
    (σ.1.lookup id).isSome → (τ.1.lookup id).isSome

/-- **`id` is live at some index of the history** (the lease-expiry plan's E3 (c), 2026-11-05): an
id the lessor ever had. -/
def everIn (hs : List LSnap) (id : w64) : Prop :=
  ∃ (i : Nat) (σ : LSnap), hs[i]? = some σ ∧ (σ.1.lookup id).isSome

/-- **Each id is live over an interval of the history** (E3 (c); ids only since the lease-expiry
plan's S2–S4, Q-S4 (A), 2026-11-05, which dropped "with one `*Lease`": `Recover` replaces a live
id's `*Lease` by a new one): an id live at `i` and at `k ≥ i` is live at every index between. What
`Grant` keeps by granting only an id the history never had (or, monotone, one not live:
`histMono`), `Revoke` by removing, `Attach`/`Detach` by keeping the lease map, `Recover` by
recovering only ids the history never had or the last snapshot has. -/
def histOnce (hs : List LSnap) : Prop :=
  ∀ (i j k : Nat) (σ τ ρ : LSnap) (id : w64), i ≤ j → j ≤ k →
    hs[i]? = some σ → hs[j]? = some τ → hs[k]? = some ρ →
    (σ.1.lookup id).isSome → (ρ.1.lookup id).isSome → (τ.1.lookup id).isSome

/-- **The snapshot `σ` has the id `id`** (E3 (c)): live in its lease map, or attached to an item
by its item map. -/
def snapHas (σ : LSnap) (id : w64) : Prop :=
  (σ.1.lookup id).isSome ∨ ∃ it : LeaseItem, σ.2.1.lookup it = some id

/-- **Every id of the history is in `U`** (E3 (c)): every id a snapshot has (`snapHas`). -/
def histIn (hs : List LSnap) (U : List w64) : Prop :=
  ∀ (i : Nat) (σ : LSnap) (id : w64), hs[i]? = some σ → snapHas σ id → id ∈ U

/-- **Every id of `U` is an id of the history** (the lease-expiry plan's S2–S4 Probe, 2026-11-05;
`histIn`'s converse, approved with Q-S7): with `histMono`, in the monotone mode every id the lessor
ever had is live in its last snapshot (`ever_live_mono`), which `Recover`'s ever-set premise
takes. `Grant` keeps it (its id is in the new snapshot), `Recover` too (its records' ids are in
the recovered one); the others leave `U` and only append. -/
def histCover (hs : List LSnap) (U : List w64) : Prop := ∀ u ∈ U, everIn hs u

def lessorRdN : Namespace := nroot .@ "lessor_rd"

/-- **The requested TTLs `Q` bound the history's TTLs from below** (the lease-expiry plan's S2–S4,
Q-S6 (A-ii), 2026-11-05): wherever a snapshot has a live id with a TTL, the TTL is at least the
id's requested TTL (`Grant` raises a request to the member's minimum, `Recover` a record's TTL to
it; neither lowers one); and `Q` has only ids the history had (so `Grant`'s fresh id is not in it). -/
def reqOk (hs : List LSnap) (Q : GMap w64 w64) : Prop :=
  (∀ (i : Nat) (σ : LSnap) (id t r : w64), hs[i]? = some σ → (σ.1.lookup id).isSome →
    σ.2.2.lookup id = some t → Q.lookup id = some r → sint.Z r ≤ sint.Z t) ∧
  ∀ (id r : w64), Q.lookup id = some r → everIn hs id

/-- **The snapshot `σ`'s TTLs are its leases' `ttl` fields** (the lease-expiry plan's R5,
2026-11-04; persistent): it has a TTL exactly for its live ids, and each live lease's `ttl` field
holds it, read-only (`Grant` and `Recover` write the field before the lease enters the map, nothing
after). -/
def ttlTie (σ : LSnap) : IProp GF :=
  iprop(⌜∀ id : w64, (σ.2.2.lookup id).isSome ↔ (σ.1.lookup id).isSome⌝ ∗
    [∗map] id ↦ l ∈ σ.1, ∃ t : w64, ⌜σ.2.2.lookup id = some t⌝ ∗ lsF go!"ttl" l ↦□ t)

/-- **The lessor's reader-side invariant** at the names `γr`: a quarter of the history's
authority (`hs`; the owner holds half, `leaseClosers`, and `le.mu`'s invariant a quarter, so that
the owner appends holding the write lock), half of the item sets' map's authority (`Sm`; the owner
the other half), `setsOk` and `histOk`, and every `*Lease` of the item sets' map's `ID` (read-only:
so a `*Lease` `Grant` has just made, whose `ID` it owns, is not one of them); (the lease-grant
plan's D2, 2026-11-02) in the monotone mode (`γr.2.2.1`), `histMono`; (the lease-expiry plan's E3
(c), 2026-11-05) in both modes each id live over an interval of the history (`histOnce`), and
half of the ids the lessor ever had, `U` (the owner holds the other half, `leaseEver`), every id of
the history among them (`histIn`) and (the S2–S4 Probe, 2026-11-05) every one of them an id of the
history (`histCover`); (the lease-expiry plan's R5, 2026-11-04) every snapshot's TTLs
its leases' `ttl` fields (`ttlTie`); (the lease-expiry plan's S2–S4, Q-S6, 2026-11-05) the
authority of the requested TTLs' map `Q`, which bounds the history's TTLs from below (`reqOk`). -/
def lessorRdBody (γr : LessorRdNames) : IProp GF :=
  iprop(∃ (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
    monoListAuthOwn γr.1 Qp.quarter hs ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
    ⌜setsOk hs Sm ∧ histOk hs⌝ ∗ ⌜γr.2.2.1 = true → histMono hs⌝ ∗
    (∃ U : List w64, dghostVar γr.2.2.2.1 (DFrac.own (1 : Qp).half) U ∗
      ⌜histOnce hs ∧ histIn hs U ∧ histCover hs U⌝) ∗
    ([∗list] σ ∈ hs, ttlTie σ) ∗
    ([∗map] l ↦ _S ∈ Sm, ∃ id : w64, lsF go!"ID" l ↦□ id) ∗
    ∃ Q : GMap w64 w64, ghostMapAuth γr.2.2.2.2 (1 : Qp) Q ∗ ⌜reqOk hs Q⌝)

/-- **The lessor `γl`'s reader-side invariant** (persistent). -/
def lessorRdInv (γl : GName) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ inv lessorRdN (lessorRdBody γr))

/-- **The index `i` of the lessor `γl`'s history is the snapshot `σ`** (persistent). -/
def lessorAt (γl : GName) (i : Nat) (σ : LSnap) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ monoListIdxOwn γr.1 i σ)

/-- **The ids the lessor `γl` ever had are among `U`** (the lease-expiry plan's E3 (c),
2026-11-05; exclusive): the owner's half of the ghost variable whose other half `lessorRdBody`
holds, with every id of the history in `U` (`histIn`). `NewLessor` gives it at `[]`; `Grant` adds
its id, `Recover` its records' ids; `Revoke`, `Attach` and `Detach` leave it. -/
def leaseEver (γl : GName) (U : List w64) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ dghostVar γr.2.2.2.1 (DFrac.own (1 : Qp).half) U)

/-- **The lease `id` was requested at the TTL `r`** (the lease-expiry plan's S2–S4, Q-S8,
2026-11-05; persistent): the discarded element of the lessor's requested TTLs' map, which
`Grant` issues for its new lease (the TTL its caller asked for) and `Recover` for each recovered
lease (the TTL its caller names for the record). Every TTL the history gives `id` is at least `r`
(`leaseTTLAt_ge_req`). -/
def leaseReqIs (γl : GName) (id r : w64) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ ghostMapElem γr.2.2.2.2 id DFrac.discard r)

/-! ### The lessor's mode (the lease-grant plan's D2, 2026-11-02)

A lessor's history is **monotone** (no lease ever leaves its map, `histMono`) in the mode its
creator picks (`NewLessor`'s `mono`); the other mode admits `Revoke` and `Recover`. A server whose
cluster grants leases and revokes none (the KV names' `lg`) creates its lessor monotone: a lease it
grants is then listed by every later `Leases()` (`leaseGrantedAt_listed`). -/

/-- **The lessor `γl`'s mode is `mono`** (persistent; pinned with its reader-side names). -/
def lessorModeIs (γl : GName) (mono : Bool) : IProp GF :=
  iprop(∃ γr : LessorRdNames, lessorPinR γl γr ∗ ⌜γr.2.2.1 = mono⌝)

/-- **The lease owner's half of the item set of the lease `l`** (of id `id`), which is what the
item map `I` attaches to `id` (unit T3, L2b). -/
def leaseItemsOwn (l : Loc) (I : GMap LeaseItem w64) (id : w64) : IProp GF :=
  iprop(∃ (sm : Loc) (S : GMap LeaseItem Unit), lsF go!"itemSet" l ↦{DFrac.own (1 : Qp).half} sm ∗
    sm ↦${DFrac.own (1 : Qp).half} S ∗ ⌜itemsFor I id S⌝)

/-- What `l.expiryMu` guards at `q`: half of `l.expiry` at `q` (the other half is the lessor's,
in `leaseMeta`). -/
def leaseExpiry (l : Loc) (q : Qp) : IProp GF :=
  iprop(∃ e : _root_.Perennial.time.Time, lsF go!"expiry" l ↦{DFrac.own q.half} e)

/-- The level of a lease's two reader pools (per-type stage B, r5 §3.3: level 0, every borrow
sequential). -/
abbrev leaseLvl : Nat := 0

def leasePoolN : Namespace := nroot .@ "lease_pool"

/-- The namespace of a lease's pool of `expiryMu`'s reader slots (the lease-read plan). -/
def leaseExpPoolN : Namespace := nroot .@ "lease_exp_pool"

/-- A lease of the map (persistent): not nil, its lock guarding its item set, the lessor's
reader-side invariant, and (Part B) a thread pool of its lock's reader slots, at level `leaseLvl`
(0), from which a reader borrows one with its level-0 token (`threadPool.isThreadPoolL`,
Perennial's `ThreadPool.lean`): `Grant` gives it
every slot but the owner's (`closerAt`), `actualMaxReaders - 1 = 2^30 - 2` of them, enough when at
most `2^30 - 1` threads are live (`threadBound GF ≤ 2^30 - 1`, the premise under which the pool
exists: `threadPool.initL` needs `threadBound ≤ n + 1`; found by Part B's Probe). (The lease-read
plan, 2026-10-31) The same of `l.expiryMu`: its guard (`leaseExpiry`) and a pool of its reader
slots, from which `Remaining()` borrows one (`LeaseLeases`' sort, on a gRPC goroutine); `Grant`
gives it every slot but the one whose guard it keeps. -/
def isLeaseObj (γl : GName) (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ sync.isRWMutexGuard (lsF go!"mu" l) (leaseItems γl l) ∗ lessorRdInv γl ∗
    sync.isRWMutexGuard (lsF go!"expiryMu" l) (leaseExpiry l) ∗
    □ (⌜threadBound GF ≤ 2 ^ 30 - 1⌝ → ∃ γp : GName,
      threadPool.isThreadPoolL leasePoolN leaseLvl γp (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))) ∗
    □ (⌜threadBound GF ≤ 2 ^ 30 - 1⌝ → ∃ γe : GName,
      threadPool.isThreadPoolL leaseExpPoolN leaseLvl γe
        (sync.ownRWMutex (lsF go!"expiryMu" l) (leaseExpiry l))))

/-- **The lessor's grant guard** (D19n, 2026-10-18; persistent): the predicate `GA` its caller
chose at `NewLessor`, a saved predicate pinned in the lessor's ghost map. A lease is granted only
with `GA` of its id (`Grant`'s `leaseGranted`); so every lease of the lessor's map, and every
lease its expiry loop sends on `expiredC`, has it. A server whose policy admits no `LeaseGrant`
picks `GA := False`. -/
def lessorGuard (γl : GName) (GA : w64 → IProp GF) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName), lessorPinG γl lp γga γcl ∗
    savedPredOwn γga DFrac.discard GA)

/-- **The lease `id` may be granted** (D19n; persistent): it meets the lessor's grant guard. -/
def leaseGranted (γl : GName) (id : w64) : IProp GF :=
  iprop(∃ GA : w64 → IProp GF, lessorGuard γl GA ∗ □ GA id)

/-- **The lessor's share `q` of its ghost map's authority**, at the live set `L`, every lease of
which may be granted (D19n); (unit T3) and of its closers' map, at the lease map `M`. -/
def lessorAuth (γl : GName) (q : Qp) (lp : Loc) (L : List w64) (M : GMap w64 Loc) : IProp GF :=
  iprop(∃ (γga γcl : GName) (γr : LessorRdNames), ghostMapAuth γl q (lessorGhost lp γga γcl γr L) ∗
    ghostMapAuth γcl q M ∗
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
`cp`, `nil` (no checkpointer is installed: `NewLessor.spec`; stage B3, 2026-11-12), and every granted lease's `leaseMeta`; (D22 receiver epochs, S7c, 2026-10-23) half the
fraction of the backend `b` (the other half its user's, `lessorBeOn`: `Recover` replaces it). -/
def lessorExtra (lp : Loc) (M : GMap w64 Loc) (q : Qp) : IProp GF :=
  iprop(∃ (dc : GoChan) (np : Loc) (h : GoSlice) (hx : List (Loc × w64)) (b : GoInterface),
    lF go!"demotec" lp ↦{DFrac.own q} dc ∗
    lF go!"leaseExpiredNotifier" lp ↦{DFrac.own q} np ∗ notifierAt np q ∗
    lF go!"leaseCheckpointHeap" lp ↦{DFrac.own q} h ∗ queueAt h hx q ∗
    lF go!"cp" lp ↦{DFrac.own q} func.nil ∗
    ([∗map] id ↦ l ∈ M, leaseMeta id l q) ∗
    lF go!"b" lp ↦{DFrac.own q.half} b)

/-- **What `le.mu` guards** at fraction `q`: the lease map `M` (whose domain is the live set
`L`; the lessor's share of it, `q/2`, and of the ghost map's authority), half of the item map
(`q/2`: unit T3, L2b, the other half is the lease owner's, `leaseClosers`), half of
the range deleter (`q/2`: unit T3, the other half is `rdOwn`'s, since `Revoke` reads `le.rd`
after releasing the lock); every lease of the map `isLeaseObj`; (2026-10-13, unit 9) the apply-side fields
(`lessorExtra`); and (lease-keys Part B, 2026-10-31) a share `q/4` of the lessor's history
(`monoListAuthOwn γr.1`, the readers' model: `lessorRdBody` holds `1/4`, `leaseClosers` `1/2`), whose
last snapshot is the map `M` with the item map `I`: a writer under the lock with the owner's half
(`Grant`, `Revoke`, `Recover`) appends to it; and (the lease-read plan, 2026-10-31) the persistent
time receipt `⧖ |M|` (`M`'s leases were inserted by as many steps), which bounds the map by the
execution's (`preceipt_lt`: `|M| < receiptBound GF`), so `lessor.Leases` can sort them (`sort.Sort`
takes at most `2^62` elements); `Grant` raises it at its insertion (`wp_raise_receipt`). -/
def lessorMu (lp : Loc) (γl : GName) (q : Qp) : IProp GF :=
  iprop(∃ (lm im : Loc) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (rd : GoFunc)
      (L : List w64),
    lF go!"leaseMap" lp ↦{DFrac.own q} lm ∗ lm ↦${DFrac.own q} M ∗
    lF go!"itemMap" lp ↦{DFrac.own q.half} im ∗ im ↦${DFrac.own q.half} I ∗
    lF go!"rd" lp ↦{DFrac.own q.half} rd ∗
    lessorAuth γl q lp L M ∗ leaseFrag γl q.half L ∗
    ⌜∀ id : w64, id ∈ L ↔ (M.lookup id).isSome⌝ ∗ ⧖ (GMap.size M) ∗
    ([∗map] _id ↦ l ∈ M, isLeaseObj γl l) ∗ lessorExtra lp M q ∗
    (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
      monoListAuthOwn γr.1 q.half.half hs ∗ ⌜∃ T, hs.getLast? = some (M, I, T)⌝))

/-- **The lessor** at `lp` with ghost map `γl` (persistent): pinned, its lock's guard. -/
def lessorInv (lp : Loc) (γl : GName) : IProp GF :=
  iprop(⌜lp ≠ null⌝ ∗ lessorPin γl lp ∗ sync.isRWMutexGuard (lF go!"mu" lp) (lessorMu lp γl) ∗
    lessorRdInv γl)

/-- The lessor's `cluster` `cl` (2026-10-13, unit 9): not nil, its `Version()` returns `nil` or
a read-only version (the server's `RaftCluster`, names-only: a contract). -/
def clusterOk (cl : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cl = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Version" ci.v)) (Val #()))
      {{ (v : Loc), RET #v;
        ⌜v = null⌝ ∨ ∃ ver : github_com.Masterminds.semver.v3.Version, v ↦□ ver }}))

/-- **The lessor's configuration** (2026-10-13, unit 9; persistent): the fields `newLessor` sets
and nothing writes after (`minLeaseTTL`, `checkpointPersist`, `cluster` with its contract,
`checkpointInterval`, `lg`, `leaseRevokeRate`, positive: `Promote` indexes the sorted leases'
first when there are at least `leaseRevokeRate` of them, so a rate below `1` with no lease panics;
audit B4b, 2026-10-18). (2026-11-10, the user's decision of 2026-11-07, sweep B3-2) The logger
`lg` is nil or a zap logger (`zapLoggerOk`): the lessor logs only through `le.lg != nil` guards
(`scheduleCheckpointIfNeeded`, `findDueScheduledCheckpoints`, `lessor.go:759,797`), and a non-nil
zero `&zap.Logger{}` panics in its `Debug`; until then `lg` was unconstrained. -/
def lessorCfg (lp : Loc) : IProp GF :=
  iprop(∃ (mt : w64) (cpp : Bool) (cl : GoInterface) (ci : _root_.Perennial.time.Duration)
      (lg : Loc) (rr : w64),
    lF go!"minLeaseTTL" lp ↦□ mt ∗ lF go!"checkpointPersist" lp ↦□ cpp ∗
    lF go!"cluster" lp ↦□ cl ∗ clusterOk cl ∗
    lF go!"checkpointInterval" lp ↦□ ci ∗ lF go!"lg" lp ↦□ lg ∗ (⌜lg = null⌝ ∨ zapLoggerOk lg) ∗
    lF go!"leaseRevokeRate" lp ↦□ rr ∗ ⌜0 < sint.Z rr⌝)

/-- A reader slot of the lessor's lock (`GetLease`, `Lookup`). -/
def lessorRd (lp : Loc) (γl : GName) : IProp GF :=
  sync.ownRWMutex (lF go!"mu" lp) (lessorMu lp γl)

/-- **The range deleter's owner** (unit T3, 2026-10-24): the other half of the lessor's `rd`
field, at `rd`. `SetRangeDeleter` takes it (with the lock's half it writes the field) and
`Revoke` reads the field by it, outside the lock. `NewLessor` gives it at `nil`; mvcc's
constructors set the store's deleter with it. -/
def rdOwn (γl : GName) (rd : GoFunc) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lF go!"rd" lp ↦{DFrac.own (1 : Qp).half} rd)

/-- **The owner's resource of the live lease `l`** (of id `id`; unit T3): half the closers'
map's element (the other half is `leaseRevokers`'), (L2b) its half of the lease's item set (what
the item map `I` attaches to `id`) and a reader slot of the lease's lock (`Keys()`, in
`Revoke`). -/
def closerAt (γl γcl : GName) (I : GMap LeaseItem w64) (id : w64) (l : Loc) : IProp GF :=
  iprop(ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗ leaseItemsOwn l I id ∗
    sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))

/-- **The lease owner's closers and items** (unit T3, 2026-10-24): for every lease of the live
set `L`, the closers' map's element (its `*Lease`, which the lessor's map agrees with), the right
to close its `revokec` and (L2b, 2026-10-25) the owner's half of its item set, the items the item
map `I` attaches to it; the owner's half of the item map `I`, every lease of which is live, (Q4 (b), 2026-10-31) every key of which is short; and
(lease-keys Part B, 2026-10-31) half of the lessor's history, whose last snapshot is `(C, I)` (`C`
is `lessorMu`'s map `M`: the two agree through `γcl`'s elements, and with `lessorMu`'s share the last
snapshots are equal), and half of the item-sets map's authority (`γr.2.1`, the item set of each
`*Lease` ever in the history; the other half is `lessorRdBody`'s). Exclusive, so outside `le.mu`'s
fractional invariant. -/
def leaseClosers (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc) (im : Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    lF go!"itemMap" lp ↦{DFrac.own (1 : Qp).half} im ∗ im ↦${DFrac.own (1 : Qp).half} I ∗
    ⌜∀ (it : LeaseItem) (id : w64), I.lookup it = some id → id ∈ L⌝ ∗ ⌜itemKeysShort I⌝ ∗
    ([∗map] id ↦ l ∈ C, closerAt γl γcl I id l) ∗
    (∃ (γr : LessorRdNames) (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
      lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗ ⌜∃ T, hs.getLast? = some (C, I, T)⌝ ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm))

/-- **The lease owner's revokers** (unit T3, 2026-10-25): for every lease of the live set `L`,
the other half of the closers' map's element and the right to close its `revokec`. Apart from
`leaseOwn` (which the store's puts and deletes take): `Revoke` keeps it while it deletes the
lease's keys, so that its half of the element says the lessor's map still has the lease it
looked up (`Grant` and `Revoke` take both). -/
def leaseRevokers (γl : GName) (L : List w64) : IProp GF :=
  iprop(∃ (lp : Loc) (γga γcl : GName) (C : GMap w64 Loc), lessorPinG γl lp γga γcl ∗
    ⌜∀ id : w64, id ∈ L ↔ (C.lookup id).isSome⌝ ∗
    [∗map] id ↦ l ∈ C, ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗
      ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c)

/-- **The lease owner's half** of the live set: holding it, `L` is the live set (the apply
thread's); (unit T3) with the live leases' closers and (L2b) the item map `I` (item to lease id)
and the live leases' item sets, which agree with it. -/
def leaseOwn (γl : GName) (L : List w64) (I : GMap LeaseItem w64) : IProp GF :=
  iprop(leaseFrag γl (1 : Qp).half L ∗ leaseClosers γl L I)

/-- A reader slot of the lessor of `γl`, wherever it is (`lessorPin`). -/
def lessorRdOf (γl : GName) : IProp GF :=
  iprop(∃ lp : Loc, lessorPin γl lp ∗ lessorRd lp γl)

/-! ### One spec for the owner and the readers (Part B, 2026-10-31)

`Lookup` and `Lease.Keys` are called by the lease owner (the apply thread) and by readers (the
server's API layer); each has one spec, which takes the caller's view: the owner's resource, or
nothing more than a reader's (Part A's `LeaseView` pattern). -/

end defs

end lease
end EtcdGrove
end Perennial
