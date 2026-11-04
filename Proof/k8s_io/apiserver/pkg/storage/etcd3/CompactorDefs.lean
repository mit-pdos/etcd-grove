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

/-- The compactor's ghost names: its revision's monotone counter. -/
structure CompactorNames where
  lb : GName

/-- **A lower bound on a compactor's revision** (persistent): later `CompactRevision` calls return
at least `r`. -/
def compactRevLb (γc : CompactorNames) (r : w64) : IProp GF :=
  monoNatLbOwn γc.lb (sint.Z r).toNat

/-- The compactor's lock invariant: `compactRevision`, recorded and reached or `0`, its counter. -/
def compactorLockInv (c : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames) :
    IProp GF :=
  iprop(∃ r : w64,
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"compactRevision" c ↦ r ∗
    monoNatAuthOwn γc.lb 1 (sint.Z r).toNat ∗ recRevOk γk recorded r)

/-- **The compactor's stop machinery**: the `stop` channel, a broadcast channel only closed; the
right to close it and to wait for the loop goroutine (the wait group's adder, its one goroutine
added), held by `stopOnce` until `Stop` runs (`sync.Once`'s `P`; its `Q` is `True`: `Stop` returns
nothing). The wait group is `sync.join`'s (its counter bounded by its `Add`s, one in the compactor's
life), not `sync.tokJoin`'s: that one's invariant needs `threadBound GF ≤ 2 ^ 31`, which
`NewCompactor.spec` does not take (K4, 2026-11-04). -/
def compactorStopOk [sync.Assumptions] (c : Loc) (sc : GoChan) (γs : ChanNames) : IProp GF :=
  iprop(structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stop" c ↦□ sc ∗
    ownBroadcastChan sc γs iprop(True) .Unknown ∗
    sync.isOnce (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stopOnce" c)
      iprop(ownBroadcastChan sc γs iprop(True) .Pending ∗
        sync.join.ownAdder (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c)
          (W32 1) iprop(True))
      iprop(True))

instance compactorStopOk_persistent [sync.Assumptions] (c : Loc) (sc : GoChan) (γs : ChanNames) :
    Persistent (compactorStopOk (GF := GF) c sc γs) := by
  unfold compactorStopOk; infer_instance

/-- **A compactor** (persistent; see the file header): its client `cl`, its interval (nonzero), a
`RealClock`, no `onClose`, the mutex over its revision, and its stop machinery (the `stop`
channel `sc`); and the caller's `recorded` is persistent (`NewCompactor.spec`'s instance), so that
the revision under the mutex can be both kept and returned. -/
@[no_expose] def isCompactor [sync.Assumptions] (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) : IProp GF :=
  iprop(⌜∀ r, Persistent (recorded r)⌝ ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"client" c ↦□ cl ∗
    (∃ iv : w64, structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"interval" c ↦□ iv ∗
      ⌜iv ≠ W64 0⌝) ∗
    (∃ ck : k8s_io.utils.clock.RealClock,
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"clock" c ↦□
        (interface.mkOk k8s_io.utils.clock.RealClock.ty #ck : GoInterface)) ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"onClose" c ↦□ func.nil ∗
    sync.isMutex (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"mux" c)
      (compactorLockInv c γk recorded γc) ∗
    ∃ (sc : GoChan) (γs : ChanNames), compactorStopOk c sc γs)

instance isCompactor_persistent [sync.Assumptions] (c cl : Loc) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) :
    Persistent (isCompactor c cl γk recorded γc) := by
  unfold isCompactor compactorStopOk; infer_instance

/-- **`ListFromCacheSnapshot` off** (U3 of K2, the user's approval 2026-11-04; a scope
restriction, the default since Kubernetes 1.34 is on): `DefaultFeatureGate`'s `Enabled` answers
`false` for it, so `NewCompactor` starts no watch loop (`runWatchLoop`, Q1 (b) of the plan). Its
only producer is the trusted spec of the example's own `Set("ListFromCacheSnapshot=false")` call
(not `featureInit`'s axiom, which answers some `bool`). -/
def gateOff : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    □ ∀ (Φ : val → IProp GF), ▷ Φ #false -∗
      WP (App (Val #(methods g.ty go!"Enabled" g.v))
        (Val k8s_io.apiserver.pkg.features.ListFromCacheSnapshot)) {{ Φ }})

instance gateOff_persistent : Persistent (gateOff (GF := GF)) := by
  unfold gateOff; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
