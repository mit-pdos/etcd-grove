/-
`client/v3/experimental/recipes`: the client bundle, the keys (`key.go`), the claim of a key at a
mod revision (`client.go`) and the events awaited (`watch.go`): the vocabulary of
`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/`. Lean-first (no Rocq counterpart). See
`decisions.md`, "Recipes: the client contracts reused, the queue's claim, two prefixes as one".

**The client** (`isEtcdRecipesClient client pfx`, persistent): the mutex's client
(`isEtcdMutexClient`: gets, transactions and deletes on its `KV` field, range watches on its
`Watcher`) with three changes: its `KV` contracts are at `context.TODO()`, which the recipes pass
to every `KV` call (`isEtcdKVTodo`, ..., `InvEtcdTxn.lean`: `TODO()`'s context is never done, so
it is not an `isContext`); its `KV` also answers puts (`isEtcdPutKVTodo`, a put as the
one-operation transaction `Then(OpPut(...))`); and its `Watcher` is taken **under the premise
that a watch channel is never closed** (`isEtcdRangeWatcherOpen`). No `ctx` field: the recipes
never call `client.Ctx()`.
The recipes as shipped need that premise: on a closed channel `waitEvents` returns `nil` and
`WaitEvents` `(nil, nil)` (`notes/issues/recipes-dequeue-closed-watch.md`,
`recipes-barrier-wait-closed-watch.md`), so every recipes result holds only while no compaction
passes a watched revision and the client is not closed; the fixed code would not need it.

**Keys.** A `RemoteKV` is the record `RemoteKVSt` (the `KV` it talks to, the key, its create
revision, its value) behind an exclusive points-to (`ownRemoteKV`); `Delete` sets `kv` to nil.
What creating a key promises (`keyCreatedAt`): absent just before the returned revision `r`,
present at `r` with create and mod revision `r`, version `1`, the value and the lease.

**The claim** (`revKeyDeleted pfx key rev r`, persistent): `deleteRevKey(key, rev)` succeeded at
`r`: `key` had mod revision `rev` at `r - 1` and is absent at `r`. Two claims of the same
`(key, rev)` are at the same revision (`revKeyDeleted_same_rev`, `InvRecipesClaim.lean`).

**Events** (`waitedEvent`): the `*Event` `WaitEvents`/`WaitPrefixEvents` return, of the awaited
type, with etcd's contract for an event of the watch (`rangeWatchEvOk`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.Base
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

/-! ## The transactions (pure) -/

/-- `putNewKV`'s transaction: `If(Version(key) = 0).Then(OpPut(key, val, WithLease(lease)))`. -/
def newKeyTxn (key val : GoString) (lease : w64) : TxnModel :=
  { cmps := [compareM (cmpKeyM .version key) .eq (.num (W64 0))],
    thenOps := [.put key val lease], elseOps := [] }

/-- `deleteRevKey`'s transaction: `If(ModRevision(key) = rev).Then(OpDelete(key))`. -/
def deleteRevTxn (key : GoString) (rev : w64) : TxnModel :=
  { cmps := [compareM (cmpKeyM .mod key) .eq (.num rev)],
    thenOps := [.delete (opDeleteModel key [])], elseOps := [] }

/-! ## Events -/

/-- `mvccpb.Event_PUT`. -/
abbrev evPut : w32 := W32 0
/-- `mvccpb.Event_DELETE`. -/
abbrev evDelete : w32 := W32 1

/-- The single-key watch `Watch(key, WithRev(rev))` of `WaitEvents`. -/
def keyWatchOp (key : GoString) (rev : w64) : OpFull := opWatchModel key [withRevM rev]

/-- The prefix watch `Watch(kp, WithPrefix(), WithRev(rev))` of `WaitPrefixEvents`. -/
def prefixWatchOp (kp : GoString) (rev : w64) : OpFull :=
  opWatchModel kp [withPrefixM, withRevM rev]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-! ## The client -/

/-- **The contracts of a `KV` interface value** the recipes' helpers take (`client.KV`, the
`KV` field of the bundle; nothing for nil): gets, transactions, deletes and puts under `pfx`, at
`context.TODO()` (the recipes pass it to every call through a `KV`: `isEtcdKVTodo`, ...). -/
def isRecipesKV (kv : GoInterface) (pfx : GoString) : IProp GF :=
  match kv with
  | .nil => iprop(True)
  | .ok kv => iprop(isEtcdKVTodo kv pfx ∗ isEtcdTxnKVTodo kv pfx ∗ isEtcdDeleteKVTodo kv pfx ∗
      isEtcdPutKVTodo kv pfx)

instance isRecipesKV_persistent (kv : GoInterface) (pfx : GoString) :
    Persistent (isRecipesKV (GF := GF) kv pfx) := by
  cases kv <;> unfold isRecipesKV <;> infer_instance

/-- **The client, as the recipes use it** (persistent; see the module docstring): for the
prefix `pfx`, gets, transactions, deletes and puts through its `KV` at `context.TODO()`
(`isRecipesKV`), and range watches (a key, a sub-prefix) through its `Watcher` **under the
premise that the watch channel is never closed** (`isEtcdRangeWatcherOpen`: the recipes as
shipped are wrong on a closed channel, see the module docstring). The trust boundary about the
client (definitions, as `isEtcdMutexClient`). -/
def isEtcdRecipesClient (client : Loc) (pfx : GoString) : IProp GF :=
  iprop(∃ (kv w : GoInterfaceOk),
    clientKVAddr client ↦□ GoInterface.ok kv ∗ clientWatcherAddr client ↦□ GoInterface.ok w ∗
    isRecipesKV (GoInterface.ok kv) pfx ∗ isEtcdRangeWatcherOpen w pfx)

instance isEtcdRecipesClient_persistent (client : Loc) (pfx : GoString) :
    Persistent (isEtcdRecipesClient (GF := GF) client pfx) := by
  unfold isEtcdRecipesClient; infer_instance

/-- The bundle's `KV` field and its contracts. -/
theorem isEtcdRecipesClient_kv (client : Loc) (pfx : GoString) :
    isEtcdRecipesClient (GF := GF) client pfx ⊢
      ∃ kv : GoInterfaceOk, clientKVAddr client ↦□ GoInterface.ok kv ∗
        isRecipesKV (GoInterface.ok kv) pfx := by
  unfold isEtcdRecipesClient
  iintro ⟨%kv, %w, #HKV, -, #H, -⟩
  iexists kv
  iframe #

/-! ## Keys -/

/-- The fields of a `RemoteKV`: the `KV` it talks to (nil after `Delete`), the key, the revision
`putNewKV` created it at, its value. -/
structure RemoteKVSt where
  kv : GoInterface
  key : GoString
  rev : w64
  val : GoString

/-- The `RemoteKV` value of the record `st`. -/
def RemoteKVSt.val' (st : RemoteKVSt) : RemoteKV :=
  { kv' := st.kv, key' := st.key, rev' := st.rev, val' := st.val }

/-- **A `*RemoteKV`** `rk` holds the record `st` (exclusive: `Delete` writes `kv`). -/
def ownRemoteKV (rk : Loc) (st : RemoteKVSt) : IProp GF := iprop(rk ↦ st.val')

/-- **An `*EphemeralKV`** `ek` holds the record `st` in its embedded `RemoteKV` (the field its
promoted methods address). -/
def ownEphemeralKV (ek : Loc) (st : RemoteKVSt) : IProp GF :=
  ownRemoteKV (structFieldRef EphemeralKV go!"RemoteKV" ek) st

/-- The key `key` is present in etcd's state at `r` under `pfx` (persistent). -/
def etcdPresent (pfx key : GoString) (r : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState r pfx s ∗ ⌜∃ v ∈ s, v.key = key⌝)

instance etcdPresent_persistent (pfx key : GoString) (r : w64) :
    Persistent (etcdPresent (GF := GF) pfx key r) := by
  unfold etcdPresent; infer_instance

/-- **`key` was created at `r`** with the value `val` and the lease `lease` (persistent): absent
from etcd's state at `r - 1`, and at `r` holding the key-value created then (create and mod
revision `r`, version `1`). `r` is positive. -/
def keyCreatedAt (pfx key val : GoString) (lease r : w64) : IProp GF :=
  iprop(etcdAbsent pfx key (r - W64 1) ∗ ∃ s : List EtcdKv, □ etcdState r pfx s ∗
    ⌜0 < sint.Z r ∧ EtcdStateWf pfx s ∧
      ∃ v ∈ s, v.key = key ∧ v.createRev = r ∧ v.modRev = r ∧ v.version = W64 1 ∧
        v.value = val ∧ v.lease = lease⌝)

instance keyCreatedAt_persistent (pfx key val : GoString) (lease r : w64) :
    Persistent (keyCreatedAt (GF := GF) pfx key val lease r) := by
  unfold keyCreatedAt; infer_instance

/-- **The claim**: `deleteRevKey(key, rev)` succeeded at revision `r` (persistent): etcd's state at
`r - 1` has `key` with mod revision `rev`, its state at `r` has no `key`; `r` is positive. -/
def revKeyDeleted (pfx key : GoString) (rev r : w64) : IProp GF :=
  iprop(∃ s s' : List EtcdKv, □ etcdState (r - W64 1) pfx s ∗ □ etcdState r pfx s' ∗
    ⌜0 < sint.Z r ∧ (∃ v ∈ s, v.key = key ∧ v.modRev = rev) ∧ ∀ v ∈ s', v.key ≠ key⌝)

instance revKeyDeleted_persistent (pfx key : GoString) (rev r : w64) :
    Persistent (revKeyDeleted (GF := GF) pfx key rev r) := by
  unfold revKeyDeleted; infer_instance

/-- **The claim failed**: at revision `r`, `key` does not have mod revision `rev` (absent, or
modified since) (persistent). -/
def revKeyGone (pfx key : GoString) (rev r : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState r pfx s ∗ ⌜∀ v ∈ s, v.key = key → v.modRev ≠ rev⌝)

instance revKeyGone_persistent (pfx key : GoString) (rev r : w64) :
    Persistent (revKeyGone (GF := GF) pfx key rev r) := by
  unfold revKeyGone; infer_instance

/-- `claimFirstKey`'s progress: each of the first `n` key-values of `vs` was gone (`revKeyGone`)
at some revision at least `lo` etcd has reached (persistent). -/
def claimedBefore (pfx : GoString) (lo : w64) (vs : List EtcdKv) (n : Nat) : IProp GF :=
  iprop(⌜n ≤ vs.length⌝ ∗ □ ∀ (j : Nat) (v : EtcdKv), ⌜j < n ∧ vs[j]? = some v⌝ -∗
    ∃ r : w64, etcdReached r ∗ revKeyGone pfx v.key v.modRev r ∗ ⌜sint.Z lo ≤ sint.Z r⌝)

instance claimedBefore_persistent (pfx : GoString) (lo : w64) (vs : List EtcdKv) (n : Nat) :
    Persistent (claimedBefore (GF := GF) pfx lo vs n) := by
  unfold claimedBefore; infer_instance

/-! ## Events -/

/-- **The event `WaitEvents`/`WaitPrefixEvents` return** (persistent): the `*Event` `ev` is
modelled by `e` (`eventAt`: its type, its `*KeyValue`, the key and mod revision there), of type
`typ` (the last awaited), with etcd's contract for an event of the watch `o` (of a range under
`pfx`) from `rev` (`rangeWatchEvOk`: in the range, at a revision at least `rev` that etcd has
reached; a delete: the key absent then; a put: its key-value in etcd's state then). -/
def waitedEvent (pfx : GoString) (o : OpFull) (rev : w64) (typ : w32) (ev : Loc) : IProp GF :=
  iprop(∃ e : EvModel, eventAt ev e ∗ ⌜e.typ = typ⌝ ∗ rangeWatchEvOk pfx o rev e)

instance waitedEvent_persistent (pfx : GoString) (o : OpFull) (rev : w64) (typ : w32) (ev : Loc) :
    Persistent (waitedEvent (GF := GF) pfx o rev typ ev) := by
  unfold waitedEvent; infer_instance

end defs

end recipes
end EtcdGrove
end Perennial
