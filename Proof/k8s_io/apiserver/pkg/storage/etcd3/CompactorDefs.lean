/-
**Kubernetes' etcd compactor, as the specs see it** (`compact.go`; K2 of
`notes/k8s-compactor-plan.md`, Draft 2 approved by the user 2026-11-04). Lean-first (no Rocq
counterpart).

Every apiserver runs a compactor; they coordinate through the etcd key `compact_rev_key`. A round
(`Compact`) is one transaction (`casTxn ev rev`): if the key's version is `ev`, put `FormatInt rev`
(the winner then compacts etcd at `rev`, the header revision of its previous round), else get the
key (the loser adopts its version and value). The key's protocol involves every writer (never
deleted once written, always a revision the cluster reached: else the compactor panics,
`nonissues/k8s-apiserver-compactor-missing-key-panic.md`, or compacts at a future revision), and the
client's KV state is the workload's (its invariant owns `etcdKV`). So the compactor takes a contract
from its caller, `casOk`, as etcd's own compactor takes the server's `compactableOk`: for a round's
transaction, the caller's atomic update at each member, whose result gives the round's facts. The
caller's ghost state: `Seen` (persistent: the key was written) and `recorded c` (persistent: a
compactor put `FormatInt c`).

The watch loop (`runWatchLoop`, Q1 (b) of the plan, the user's approval of D2 2026-11-04) reads
the key with `Get` and watches it: it learns every value the key held since the revision it read,
not only the current one. So it takes a second contract, `keyReadOk`: the caller's read update of
the cluster's KV state, whose result `keyHistOk` says that every value the key held in the state's
history (each event of the key, and its current value) is `FormatInt c` of a recorded `c`, reached
or `0` (`keyValOk`), and that the state is past etcd's first revision (a watch starts at a revision
`≥ 1`; a read update cannot learn it from the cluster's invariant, which it masks out).

`isCompactor` (persistent, sealed internals) is the compactor object: its fields, the mutex over
`compactRevision` (a recorded, reached revision or `0`, with a monotone lower bound), and its stop
machinery (`stopOnce`, the `stop` channel, the wait group of its loop goroutine).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base
public import Proof.strconv.FormatIntDefs
public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3
public import Perennial.Proof.sync.Results
public import Perennial.Ghost.MonoNat
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import GeneratedProof.k8s_io.utils.clock
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- The compactors' key (`compactRevKey`, `compact.go:39`). -/
def compactRevKey : GoString := go!"compact_rev_key"

/-- The value of key `k` in `σ`'s current store, if present. -/
def keyValue (σ : KVState) (k : GoString) : Option GoString :=
  ((σ.kvs.filter fun v => decide (v.key = k)).head?).map EtcdKv.value

/-- **`Compact`'s transaction** (`compact.go:217`): if the key's version is `ev`, put
`FormatInt(rev, 10)`, else get the key. -/
abbrev casTxn (ev rev : w64) : TxnModel :=
  linkv.txnOf [.ver compactRevKey ev] [.put compactRevKey (fmtInt rev (W64 10))] [.get compactRevKey]

/-- Whether `casTxn ev rev` succeeds at `σ` (the server's verdict at the next revision). -/
def casWins (ev rev : w64) (σ : KVState) : Bool :=
  (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (casTxn ev rev)).1

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client's KV handle** (persistent; K4, 2026-11-04): the client's `KV` field holds a `*kv`
that is a client of etcd's KV at `γk` (`isKv`, which carries the store's receipt bound: its owner
fixes it, `notes/bounds-plan.md`). The round's `Compact(rev)` goes through it. -/
def clientKvOk [go_etcd_io.etcd.client.v3.Assumptions] (cl : Loc) (γk : KVNames) : IProp GF :=
  iprop(∃ (api : Loc) (dup : Bool),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
      GoInterface.ok (client.kvIfaceOf api) ∗ client.isKv api γk dup)

instance clientKvOk_persistent [go_etcd_io.etcd.client.v3.Assumptions] (cl : Loc) (γk : KVNames) :
    Persistent (clientKvOk (GF := GF) cl γk) := by
  unfold clientKvOk; infer_instance

/-- **A revision a round may hold**: `0` (none yet), or positive and reached by the cluster `γk`. -/
def revOk (γk : KVNames) (r : w64) : IProp GF :=
  iprop(⌜r = W64 0⌝ ∨ ⌜0 < sint.Z r⌝ ∗ kvRevLbZ γk (sint.Z r))

instance revOk_persistent (γk : KVNames) (r : w64) : Persistent (revOk (GF := GF) γk r) := by
  unfold revOk; infer_instance

/-- **A revision a compaction may be at**: `0`, or positive, recorded by a compactor and reached. -/
def recRevOk (γk : KVNames) (recorded : w64 → IProp GF) (r : w64) : IProp GF :=
  iprop(⌜r = W64 0⌝ ∨ ⌜0 < sint.Z r⌝ ∗ recorded r ∗ kvRevLbZ γk (sint.Z r))

instance recRevOk_persistent (γk : KVNames) (recorded : w64 → IProp GF)
    [∀ c, Persistent (recorded c)] (r : w64) : Persistent (recRevOk (GF := GF) γk recorded r) := by
  unfold recRevOk; infer_instance

/-- **What a round's transaction tells the compactor** at the state `σ` it ran at: the key was
written (`Seen`); on success, `rev` recorded; on failure, the key present holding `FormatInt c` for
a recorded, reached-or-zero `c`. -/
def casPost (γk : KVNames) (Seen : IProp GF) (recorded : w64 → IProp GF) (ev rev : w64)
    (σ : KVState) : IProp GF :=
  iprop(Seen ∗
    (if casWins ev rev σ then recorded rev
     else ∃ c : w64, ⌜keyValue σ compactRevKey = some (fmtInt c (W64 10))⌝ ∗ recorded c ∗
       revOk γk c))

/-- **The compactor's contract** (persistent; the caller's, see the file header): given `ev = 0` or
`Seen`, and a revision `rev` it may write (`revOk`), the round's transaction's atomic update at each
member, fired at most once, whose result gives `casPost`. -/
def casOk (ms : List (client.SrvAt GF)) (γk : KVNames) (Seen : IProp GF)
    (recorded : w64 → IProp GF) : IProp GF :=
  iprop(□ ∀ (ev rev : w64), (⌜ev = W64 0⌝ ∨ Seen) -∗ revOk γk rev -∗
      [∧list] x ∈ ms, kvOpAu1 x.γr.kv (.txn (casTxn ev rev)) (casPost γk Seen recorded ev rev))

instance casOk_persistent (ms : List (client.SrvAt GF)) (γk : KVNames) (Seen : IProp GF)
    (recorded : w64 → IProp GF) : Persistent (casOk ms γk Seen recorded) := by
  unfold casOk; infer_instance

/-- **A value the compactors' key may hold**: `FormatInt(c, 10)` of a recorded `c`, reached or `0`. -/
def keyValOk (γk : KVNames) (recorded : w64 → IProp GF) (v : GoString) : IProp GF :=
  iprop(∃ c : w64, ⌜v = fmtInt c (W64 10)⌝ ∗ recorded c ∗ revOk γk c)

instance keyValOk_persistent (γk : KVNames) (recorded : w64 → IProp GF)
    [∀ c, Persistent (recorded c)] (v : GoString) : Persistent (keyValOk (GF := GF) γk recorded v) := by
  unfold keyValOk; infer_instance

/-- **What a read of the key tells the watch loop** at the state `σ` (persistent; see the file
header): `σ` is past revision `1`, the key's current value and the value of each of its events
through `σ`'s revision are `keyValOk`. -/
def keyHistOk (γk : KVNames) (recorded : w64 → IProp GF) (σ : KVState) : IProp GF :=
  iprop(⌜1 ≤ σ.rev⌝ ∗
    □ (∀ v : GoString, ⌜keyValue σ compactRevKey = some v⌝ -∗ keyValOk γk recorded v) ∗
    □ (∀ (r : Nat) (ev : mvcc.EvM), ⌜r ≤ σ.rev ∧ ev ∈ σ.revEvents r ∧ ev.kv.key = compactRevKey⌝ -∗
        keyValOk γk recorded ev.kv.value))

instance keyHistOk_persistent (γk : KVNames) (recorded : w64 → IProp GF) (σ : KVState) :
    Persistent (keyHistOk (GF := GF) γk recorded σ) := by
  unfold keyHistOk; infer_instance

/-- **The watch loop's contract** (persistent; the caller's, see the file header): its read update
of the cluster's KV state `γk`, whose result is `keyHistOk`. -/
def keyReadOk (γk : KVNames) (recorded : w64 → IProp GF) : IProp GF :=
  kvReadAu γk (keyHistOk γk recorded)

instance keyReadOk_persistent (γk : KVNames) (recorded : w64 → IProp GF) :
    Persistent (keyReadOk (GF := GF) γk recorded) := by
  unfold keyReadOk; infer_instance

/-- **The client's watcher handle** (persistent): the client's `Watcher` field holds a `*watcher`
of a watch environment over the cluster's KV state `γk` (`isClientWatcher`, what the client's
`Watch` takes). -/
def clientWatchOk [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] (cl : Loc)
    (γk : KVNames) : IProp GF :=
  iprop(∃ (w : Loc) (V : client.WEnv GF),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" cl ↦□
      GoInterface.ok (client.watcherIfaceOf w) ∗ client.isClientWatcher V w ∗ ⌜V.kst = γk.st⌝)

instance clientWatchOk_persistent [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (γk : KVNames) : Persistent (clientWatchOk (GF := GF) cl γk) := by
  unfold clientWatchOk; infer_instance

/-- **A watch response of the key, as `fromWatchResponse` reads it** (persistent): its close error
is a status error (what `Err()` takes), it is modelled by `r` (`respAt`), and, unless it is an
error, each of its events' key-value holds a `keyValOk` value. -/
def respKeyOk (γk : KVNames) (recorded : w64 → IProp GF)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr' ∗ ∃ r : RespModel, respAt v r ∗
    (⌜watchErr v⌝ ∨ □ ∀ (i : Nat) (e : EvModel), ⌜r.events[i]? = some e⌝ -∗
      ∃ kv : EtcdKv, kvValAt e.kv kv ∗ keyValOk γk recorded kv.value))

instance respKeyOk_persistent (γk : KVNames) (recorded : w64 → IProp GF)
    [∀ c, Persistent (recorded c)] (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    Persistent (respKeyOk (GF := GF) γk recorded v) := by
  unfold respKeyOk; infer_instance

/-- The compactor's ghost names: its revision's monotone counter. -/
structure CompactorNames where
  lb : GName

/-- **A lower bound on a compactor's revision** (persistent): later `CompactRevision` calls return
at least `r`. -/
def compactRevLb (γc : CompactorNames) (r : w64) : IProp GF :=
  monoNatLbOwn γc.lb (sint.Z r).toNat

instance compactRevLb_persistent (γc : CompactorNames) (r : w64) :
    Persistent (compactRevLb (GF := GF) γc r) := by
  unfold compactRevLb; infer_instance

/-- The compactor's lock invariant: `compactRevision`, recorded and reached or `0`, its counter. -/
def compactorLockInv (c : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames) :
    IProp GF :=
  iprop(∃ r : w64,
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"compactRevision" c ↦ r ∗
    monoNatAuthOwn γc.lb 1 (sint.Z r).toNat ∗ recRevOk γk recorded r)

/-- **The compactor's stop channel** (persistent): the `stop` field holds `sc`, a broadcast channel
only closed. What the loops need of the stop machinery (they wait on it). -/
def compactorChanOk (c : Loc) (sc : GoChan) (γs : ChanNames) : IProp GF :=
  iprop(structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stop" c ↦□ sc ∗
    ownBroadcastChan sc γs iprop(True) .Unknown)

instance compactorChanOk_persistent (c : Loc) (sc : GoChan) (γs : ChanNames) :
    Persistent (compactorChanOk (GF := GF) c sc γs) := by
  unfold compactorChanOk; infer_instance

/-- **The compactor's stop machinery**: the `stop` channel (`compactorChanOk`); the right to close
it and to wait for the loop goroutines (the wait group's adder, its goroutines added: the
compaction loop's, and the watch loop's when the feature gate is on), held by `stopOnce` until
`Stop` runs (`sync.Once`'s `P`; its `Q` is `True`: `Stop` returns nothing). The wait group is
`sync.join`'s (its counter bounded by its `Add`s, at most two in the compactor's life), not
`sync.tokJoin`'s: that one's invariant needs `threadBound GF ≤ 2 ^ 31`, which `NewCompactor.spec`
does not take (K4, 2026-11-04). -/
def compactorStopOk [sync.Assumptions] (c : Loc) (sc : GoChan) (γs : ChanNames) : IProp GF :=
  iprop(compactorChanOk c sc γs ∗
    sync.isOnce (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stopOnce" c)
      iprop(ownBroadcastChan sc γs iprop(True) .Pending ∗
        ∃ n : w32, sync.join.ownAdder
          (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c) n iprop(True))
      iprop(True))

instance compactorStopOk_persistent [sync.Assumptions] (c : Loc) (sc : GoChan) (γs : ChanNames) :
    Persistent (compactorStopOk (GF := GF) c sc γs) := by
  unfold compactorStopOk; infer_instance

/-- **A compactor's `onClose`** (persistent; Q1 (c), 2026-11-05): `nil`, or a function that returns
when called (`StartCompactorPerEndpoint`'s, which removes the compactor from the registry), as
`Stop` calls it. -/
def closeOk (f : GoFunc) : IProp GF :=
  iprop(⌜f = func.nil⌝ ∨ □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #f) (Val #())) {{ Φ }}))

instance closeOk_persistent (f : GoFunc) : Persistent (closeOk (GF := GF) f) := by
  unfold closeOk; infer_instance

/-- **A compactor, as its loops see it** (persistent; Q1 (b), 2026-11-04): its client `cl`, its
interval (nonzero), a `RealClock`, its `onClose` (`closeOk`; until Q1 (c), 2026-11-05, `nil`), the
mutex over its revision and its stop channel;
and the caller's `recorded` is persistent (`NewCompactor.spec`'s instance), so that the revision
under the mutex can be both kept and returned. Not the right to stop it (`stopOnce`'s): the loop
goroutines start before the wait group's last `Add`, whose adder the `Once` then holds. -/
@[no_expose] def compactorCore (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) : IProp GF :=
  iprop(⌜∀ r, Persistent (recorded r)⌝ ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"client" c ↦□ cl ∗
    (∃ iv : w64, structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"interval" c ↦□ iv ∗
      ⌜iv ≠ W64 0⌝) ∗
    (∃ ck : k8s_io.utils.clock.RealClock,
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"clock" c ↦□
        (interface.mkOk k8s_io.utils.clock.RealClock.ty #ck : GoInterface)) ∗
    (∃ f : GoFunc, structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"onClose" c ↦□ f ∗
      closeOk f) ∗
    sync.isMutex (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"mux" c)
      (compactorLockInv c γk recorded γc) ∗
    ∃ (sc : GoChan) (γs : ChanNames), compactorChanOk c sc γs)

instance compactorCore_persistent (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) :
    Persistent (compactorCore c cl γk recorded γc) := by
  unfold compactorCore; infer_instance

/-- **A compactor** (persistent; see the file header): as its loops see it (`compactorCore`), and
its stop machinery (the `stop` channel `sc`, `compactorStopOk`). -/
@[no_expose] def isCompactor [sync.Assumptions] (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) : IProp GF :=
  iprop(compactorCore c cl γk recorded γc ∗
    ∃ (sc : GoChan) (γs : ChanNames), compactorStopOk c sc γs)

instance isCompactor_persistent [sync.Assumptions] (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) :
    Persistent (isCompactor c cl γk recorded γc) := by
  unfold isCompactor compactorStopOk; infer_instance

/-- **A compactor of the cluster `γk`** (Q1 (c), 2026-11-05): what an endpoint's claim (`epOf`) says
of the compactor `StartCompactorPerEndpoint` registers for it: a compactor (of some client) over
`γk` and `recorded`, with the lower bound `0` on its revision. Over `CompactorId` (the compactor,
its client, its revision's ghost name), the registry's saved predicates' domain. -/
def compactorFor [sync.Assumptions] (γk : KVNames) (recorded : w64 → IProp GF) :
    CompactorId → IProp GF :=
  fun x => iprop(isCompactor x.1 x.2.1 γk recorded ⟨x.2.2⟩ ∗ compactRevLb ⟨x.2.2⟩ (W64 0))

instance compactorFor_persistent [sync.Assumptions] (γk : KVNames) (recorded : w64 → IProp GF)
    (x : CompactorId) : Persistent (compactorFor (GF := GF) γk recorded x) := by
  unfold compactorFor; infer_instance

/-- **Endpoint `ep` is the cluster `γk`'s, its compactors recording `recorded`** (persistent; Q1 (c),
2026-11-05): the registry's claim of `ep` (`epClaim`, `RegistryDefs.lean`) for the compactors of
`γk` and `recorded` (`compactorFor`). What `StartCompactorPerEndpoint` takes of each of its client's
endpoints; made from the claims' authority (`epOf_alloc`). -/
def epOf [CompactorRegistry] [sync.Assumptions] (ep : GoString) (γk : KVNames)
    (recorded : w64 → IProp GF) : IProp GF :=
  epClaim ep (compactorFor γk recorded)

instance epOf_persistent [CompactorRegistry] [sync.Assumptions] (ep : GoString) (γk : KVNames)
    (recorded : w64 → IProp GF) : Persistent (epOf (GF := GF) ep γk recorded) := by
  unfold epOf; infer_instance

/-- **Claim an endpoint not yet claimed** for the cluster `γk` (`epOf`), from the claims' authority. -/
theorem epOf_alloc [CompactorRegistry] [sync.Assumptions] (M : GMap GoString GName)
    (ep : GoString) (γk : KVNames) (recorded : w64 → IProp GF) (h : M.lookup ep = none) :
    regAuth M ⊢ |==> ∃ γa, regAuth (M.insert ep γa) ∗ epOf ep γk recorded := by
  unfold epOf
  exact epClaim_alloc M ep _ h

/-- `nil` is a compactor's `onClose`. -/
theorem closeOk_nil : ⊢ closeOk (GF := GF) func.nil := by
  unfold closeOk
  ileft
  ipureintro
  rfl

/-- A compactor is one as its loops see it. -/
theorem isCompactor_core [sync.Assumptions] (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) :
    isCompactor (GF := GF) c cl γk recorded γc ⊢ compactorCore c cl γk recorded γc := by
  unfold isCompactor
  iintro ⟨#H, -⟩
  iexact H

end defs

section fmtarg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open Iris.ProofMode in
/-- An error whose `Error()` returns and that has no `Format` (`errStrOk`) is one `fmt` formats by
its `Error()` (`fmt.argOk`): what the compactor's `klog.Errorf` needs of the loops' errors
(klog-args-fix, 2026-11-14). -/
theorem fmtArgOk_of_errStrOk (err : GoInterface) :
    go_etcd_io.etcd.cache.v3.errStrOk (GF := GF) err ⊢ fmt.argOk err := by
  cases err with
  | nil => iintro -; unfold fmt.argOk; itrivial
  | ok e =>
    unfold go_etcd_io.etcd.cache.v3.errStrOk fmt.argOk
    iintro #H
    ihave ⟨#HS, %hF⟩ := H $$ %e %rfl
    iright; ileft
    isplitr
    · rw [show fmt.stringMethodSpec e go!"Error" = go_etcd_io.etcd.cache.v3.errorStringSpec e
        from rfl]
      iexact HS
    · ipureintro; exact hF

open Iris.ProofMode in
/-- A client error grpc's `status` accepts (`statusErrOk`, `kvErr`'s) is `fmt.argOk`. -/
theorem fmtArgOk_of_statusErrOk (err : GoInterface) :
    go_etcd_io.etcd.cache.v3.statusErrOk (GF := GF) err ⊢ fmt.argOk err := by
  iintro #H
  iapply fmtArgOk_of_errStrOk
  iapply go_etcd_io.etcd.cache.v3.errStrOk_of_statusErrOk $$ H

end fmtarg

end k8s
end EtcdGrove
end Perennial
