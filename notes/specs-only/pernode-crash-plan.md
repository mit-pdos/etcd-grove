# Per-node crashes: replanning the crash story (2026-11-10)

The user's decisions (`open-questions.md` D, "The user's answers", 2026-11-10): the end theorem is
about a **new test**: several etcd members, each crashing alone, random reconfigurations (add as
learner, promote, remove), and a client node that never crashes and checks linearizability with
porcupine. It is proved in Perennial's distributed GooseLang (`DistLang.lean`, `DistAdequacy.lean`)
with no Iris axioms: grpc and net/http become trusted operational extensions at their APIs
(`net-extensions-design.md`, being designed in parallel). Bugs with failing Go tests get fork fixes
(`fix-plan.md`, `fix-raft-commit-lost.md`). D7/D31 (a directory entry is durable at its file's first
sync) and D32 (a rename within one directory is atomic across a crash) are accepted OS premises.

This note replaces `top.md` K6's crash design (generations of one process) and says what becomes of
each law and predicate of that design. It is a plan: no spec has been edited.

## 0. What changes, in short

- **Cluster vocabulary is stated over the global ghost state**: the binder `[G : GooseGlobalGS
  HasLC.hasLC GF]`, not `[hG : HeapGS ..]`. This is forced, not only tidier: the cluster has to be
  allocated in the theorem's global setup (`Hstart`), before any node has a local ghost state, and
  every node, the client included, uses that vocabulary under its own heap. Every `*_gen` law goes.
- **A node's disk stays the node's**: the per-disk crash laws (WAL, snapshotter, backend, bbolt,
  `disk_crash`) keep their statements. Their `L'` is now the crashed node's next generation.
- **Raft's per-id tokens become global.** Only the "a node of `id` runs in this generation" part
  stays per generation, as a new token `nodeHeld`, which a crash law turns back into the vacancy. So
  `raftState_gen` goes, and `raftState_crash` loses its `L'`.
- **One protocol per address for the whole run**: D4's per-generation families are withdrawn.
  Requests now cross the receiver's crash, since the client and the other members survive it. The
  lease views (W0's `leaseViewLb`) do not survive a member's crash, so they need a crash epoch
  (a question for the user).
- **Reconfiguration is on the goal path**: F10, the stop gate (E10), the members' request-id
  prefixes, F9 (if snapshots stay in) and etcd's peer handler (3.2/D8) become goal work.

## 1. The semantics, and what a node owes

### 1.1 `goose_dist_crash_adequacy` (Perennial `GooseLang/DistAdequacy.lean:744`), exactly

Parameters: the bounds `N` (steps of all nodes together, crashes included) and `T` (live threads
per node); `es : List (Expr × state)` (node `i`'s boot program and initial local state); `g`
(the initial global state); `φ i` (node `i`'s main-thread postcondition, `hφ`: never a panic). Its
hypotheses:

- `Hinitg`, `Hinit`: the extensions' initial-state predicates (`extsInitgP g.globalWorld`, and
  `extsInitP σᵢ.world g.globalWorld` for each node). For OsFs this is `OsInit`: no fd, every file
  at an allowed path as on disk. All nodes share one `GooseExts`: OsFs plus the network
  extensions, the client node included.
- `P : ∀ [GooseGlobalGS], Nat → GooseLocalGS GF → IProp GF`: node `i`'s boot precondition, at one
  generation `L` of that node.
- **`Hstart`** (global setup): `∀ [GooseGlobalGS], receiptBound GF = N → ⊢ extsGlobalStart
  g.globalWorld ={⊤}=∗ [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i)`, with `nodeStart T σ P := ∀ L,
  ⌜threadBound = T⌝ -∗ ⌜goLctx L = σ.goLctx⌝ -∗ extsLocalStart σ.world -∗ ownGoState
  σ.packageState ={⊤}=∗ P L`. The fancy update runs **under the global ghost state only** and may
  allocate the invariants and ghost state the nodes share. Each `nodeStart` closure may capture
  resources that update made.
- **`Hwp`** (every generation of every node, the first one included): `∀ [hG : HeapGS],
  receiptBound = N → threadBound = T → es[i]? = some (e, σ) → goLctx agrees → ⊢ P i hG.L -∗
  threadTok ={⊤}=∗ WP e {{ v, ⌜φ i v⌝ }} ∗ ∀ L', crashed@hG.L -∗ extsCrashStart hG.L L' -∗
  ownGoState@L' ∅ ={⊤}=∗ P i L'`. **The crash frame is produced at boot, together with the WP**: it
  is a fixed closure. It gets the dead generation's `crashed` and the extensions' crash resources
  (OsFs: `crashRest L L' []`; a network extension: whatever its `crashStart` says). It has an empty
  package state, so the boot program re-runs the package initializers in every generation.
- About the run: `DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c`, `n < N`, one thread
  per node at the start (`Hthreads`), fewer than `T` live threads on every node along the run
  (`Hlive`, `DistCrashThreadsBelow`).

Conclusion: for every node, a terminated main thread satisfies `φ i`, no thread is stuck, and no
thread has an unrecovered panic.

### 1.2 What this means for the specs

1. **Allocation happens in `Hstart`, with no local ghost state.** `cluster_alloc` (W0/2e), raft's
   `cluster_alloc`, `urls_reserve`, the address reservations and `idSpace_alloc` all run before any
   node has a heap, so what they return must be stated without one. Today's opaques take `[hG :
   HeapGS ..]` by convention (D20), which makes them unusable there. Perennial's own `netfs`
   example states its protocol under `[G : GooseGlobalGS hlc GF]`
   (`Proof/.../netfs/Base.lean:80`).
2. **Every node proves its WP under its own `hG = ⟨G, Lᵢ⟩`.** A client holding `etcdLb γ σ`
   (built at the client's heap) and a member firing the client's update (at the member's heap) must
   be talking about the same predicate. Today that comes from the `⊣⊢` `*_gen` laws, which happen to
   relate any two local parts. Under the global binder it holds by construction.
3. **A crash changes one node's `L`**: only that node's frame runs, with its own `crashed`. Nothing
   global changes: neither the network nor any invariant. What a dead generation leaves in a global
   invariant (a node invariant, a deposited update) stays, unusable by its dead threads.
4. **The frame reaches the node's disk only through an invariant allocated before the frame**, i.e.
   in `Hwp`'s update, at that generation. That is today's design per node, so D17 (the crash frame
   cannot take client-owned durable state out of an invariant that callees' atomic updates open)
   remains a Perennial gap, now one per member node (`notes/perennial-changes.md`, the two
   2026-11-09 entries).
5. **The client node may crash in the semantics.** `DistCrashStep.crash` applies to any node.
   "The client never crashes" has to be either a restriction of the semantics or something the
   client's program handles (§4.3, question Q1).

## 2. Keep, change, drop

### 2.1 Per-disk crash laws: keep (a node's disk is its local state)

| law / predicate | file | fate |
|---|---|---|
| `walRecs_crash`, `walWriting_crash`, `walCreating_crash`, `Recs.crashScopeOk`, `crashInScope` | `storage/wal/Api.lean` | **keep** the laws. `crashScopeOk` loses part (a) (`confAboveOk`) with the raft fix (`fix-raft-commit-lost.md` §6). Part (b) (no snapshot record above the commit) is to be closed in the WAL spec (§7 there: such a record is inert at a restart). Then `crashInScope` is deleted. |
| `snapDbs_crash`, `snapSaving_crash`, `snapRen` (D32) | `etcdserver/api/snap/Api.lean` | **keep**. D32 is accepted. |
| `beFile_crash`, `beCrash`, `beDetached_crash`, `beOpenUpd`, `beCloseUpd` (D3, D24) | `storage/backend/Durable.lean`, `Api.lean` | **keep**. D7/D31 accepted: `beOpenUpd`'s `none` revert entry goes, and `BoltSt.named` is true at the first sync. |
| `boltCrash` | `bbolt/Api.lean` | **keep** (OsFs's `crashRestQ`). |
| `disk_crash` | `etcdserver/ApiBoot.lean:774` | **keep the statement** (`∀ L'`, `crashRest L L'`, `diskFiles`). Changes: its premises lose `Wal.crashInScope` (above); its realization uses §2.4's raft laws (no `raftState_gen`) and the global `memberBoot`/`memberJoin` (no crossing needed for the `.boot`/`.join` kinds). |
| `diskState` | `ApiBoot.lean:385` | **keep at `hG`**: it holds the node's OsFs resources, which are local. |
| `diskIdle` | `ApiBoot.lean:388` | **change** (recommended, S): global and exclusive (two give `False`). The start escrows it in `diskState` and deposits a per-generation `diskHeld γ ds` (the same pattern as raft's `nodeHeld`, §2.4). `disk_crash`'s realization consumes `diskHeld` with `crashed` and releases the global token. This retires D28's `crashed` alternative for `diskIdle_excl`/`diskIdle_agree`/`memberDisk_excl` (the "token or `crashed`" realization). Alternative: keep today's per-generation token-or-`crashed`, which still works per node. |
| `dataDirFresh`, `dataDirFresh_crash` | `ApiBoot.lean:370, 807` | `dataDirFresh` stays local (OsFs's per-directory start token). It is consumed in the node's first `nodeStart` (`disk_new`/`disk_join`, §3.2), so `dataDirFresh_crash` is off the end theorem's path. Keep it for single-node programs. |
| `memberStart_disk`, `diskAcc` | `ApiBoot.lean:817, 405` | **keep**. |

The tie between raft's durable state and the disk (asked for in item 1) is `diskState`'s
realization, not a law. For `.member id`, `diskState γ ds (.member id)` at node `i`'s `hG` is `∃ R
D, Wal.walRecs (walDirOf ds) R ∗ raftState γ id D ∗ ⌜walHolds R D⌝ ∗ ... ∗` (while a batch is in
flight) `readyPending ... ∗ ...`. Here `raftState` is now global and the WAL is local. Across node
`i`'s crash, `disk_crash`'s realization applies the WAL's laws (records `R'`, under OsFs's
`crashRest L L'`), then `raftState_crash` (batch in flight: `D ↦ D'` with `D.crashOk b D'` matching
`R'`) or nothing (at rest: `D` unchanged, `R' = R`), then `nodeHeld_crash` (the vacancy back). It
then re-forms `diskState@L'` from `R'@L'` and the same global `raftState γ id D'`. No other node's
`raftState` or disk is touched: the disk invariant is node `i`'s, allocated in node `i`'s `Hwp`.

### 2.2 Cluster-wide resources: global, no crossing laws

**How to state them**: opaques with the binder `[G : GooseGlobalGS HasLC.hasLC GF]`, realized from
global ghost names, invariants (`GooseGlobalGS.gooseInvGS` as a local instance, as in `netfs`) and
later credits. Under a `[hG : HeapGS ..]` context they are used as is (`hG.goose_globalGS` is a
reducible instance). The arguments of such a predicate (a client's `Q`, a read's update) may still
mention local resources: an `IProp` is an `IProp`. Only the opaque's own realization is restricted.
**Who owns the exclusive ones**: W0's `etcdState γ σ` belongs to the client node's invariant `I`,
which is global like every invariant. The client never crashes (§4.3), and even if it did, nothing
of `I` would be lost. The rest are owned by cluster invariants that no crash touches.

The rejected alternative: keep the `[hG]` binder and the `⊣⊢` laws. They do relate any two nodes'
heaps, but they cannot be used in `Hstart` (no `hG`), and every client law then needs a `*_gen`
twin. Under the global binder, D20 ("generation independence as `⊣⊢` laws") is superseded.

| family | file | change |
|---|---|---|
| `etcdState`, `etcdLb`, `servesAt`, `tokenUser`, `soleMember`, `peerLeaseServed`, `urlsReserve`, `urlsRight`, `envUpd`/`etcdPerm`/`etcdPeek`/`authLb` (transparent) | `api/v3/State.lean` | global binder; **drop** `etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen`, `peerLeaseServed_gen`, `envUpd_gen` |
| `leaseViewLb γ ep i` | `State.lean:191`, 18 files | **cannot stay as is**: it is a view of a member's lessor, which a crash of that member can roll back (its uncommitted backend batch is lost). Under per-node crashes the client keeps the view across the member's crash, and the address keeps its contract (§2.3). Proposal: a crash epoch, `leaseViewLb γ ep e i` (the member's lessor in its `e`-th crash epoch; `disk_crash` bumps a global per-disk counter). An answer gives the epoch that answered; the per-member rows hold only within one epoch; `leaseViewLb_zero` holds at any epoch. Client-visible: **Q2**. |
| raft's `committedLb`, `committedOps`, `confAt`, `confDecisions`, `confDecided`, `snapsMade`, `snapValid`, `readCtxs`, `readCtx`, `readState`, `msgSent`, `msgCredit`, `freshIds`, `bootLog`; `cluster_alloc`, `freshIds_take` | `raft/v3/Api.lean` | global binder; **drop** `global.spec` (`:961`) |
| `srvNet γ ν`, `Rafthttp.Net` (`img`, `dbIn`), `peerAddr ν a`, `raftProto ν` | `ApiBoot.lean`, `rafthttp/Api.lean` | global; **drop** `srvNet_gen`, `peerAddr_gen`; `raftFam` goes (§2.3); `peerAddr ν a := Http.protoAt a P ∗ ⌜raftCompat ν P⌝` again (one protocol) |
| `srvEp γ ep id`, `srvAt` | `ApiBoot.lean:435, 444` | global; **drop** `srvEp_gen`. **Re-key**: a joiner's id is assigned by its `MemberAdd`, at run time (time-salted), so an address cannot be bound to an id in `Hstart`. Key the binding by the peer-URL set instead, `srvEp γ ep urls`, which is known at setup and single-use (3.1): `srvAt s γ ep := ∃ id urls, srvFields s γ id ∗ srvEp γ ep urls ∗ urlsOf γ urls id`. Here `urlsOf` is persistent, from the URL set's entry once a member holds it (the initial members' at `cluster_alloc`). |
| `memberBoot γ ms m`, `memberJoin γ urls` | `ApiBoot.lean:373, 381` | global (their realizations are raft's global `raftState`/`nodeVacant`, decisions, `peerAddr`); **drop** `memberBoot_crash`, `memberJoin_crash` |
| `cluster_alloc`, `urls_reserve`, `srvEp_reserve`, `soleMember_intro` | `ApiBoot.lean` | stated under the global binder, so that `Hstart` can call them. `srvEp_reserve` takes a global contract `F` (no family) |
| `Http.addrFree`, `Http.protoAt`, `Http.reserve`, `addrFree_protoAt_excl`; `Grpc.addrAt` | `net/http/Api.lean`, `grpc/Api.lean` | global and set once for the run (§2.3). They become the network extensions' ghost-state laws, proved from the model, not assumed (D5's law included) |
| `idSpace_alloc` | `pkg/v3/idutil/Api.lean:88` | global; see §3.4 on joiners' prefixes |

The single-node crash adequacy (`goose_crash_adequacy`) also keeps `G` across generations, so the
global binder serves the remaining single-process examples unchanged.

### 2.3 Per-generation protocol families: drop (D4 withdrawn)

D4's reason ("a crash kills every connection, so a request a generation-`L` handler reads was sent
in `L`") was a property of the whole-process crash. Under per-node crashes, member A sends to B, B
crashes, and A's next request reaches B's next incarnation; likewise for the client. A request's
precondition is fixed by its sender, who does not know the receiver's incarnation, so **an address's
protocol must be one protocol for the run, over global vocabulary**. That is the 2026-10-22
boundary's decision 1 again.

- **Drop**: `Http.protoFam`, `protoFam_at`, `protoFam_gen`, `addrFree_gen` (`net/http/Api.lean`);
  `Rafthttp.raftFam`; the per-generation reading of `Grpc.addrAt`; `srvEp_reserve`'s family `F :
  GooseLocalGS GF → Proto GF`.
- **Keep**: `reserve : addrFree a ⊢ |==> protoAt a P` (one global `P`), `protoAt` persistent for the
  run, `addrFree_protoAt_excl`.
- **Consequences**: the etcd contract served at a client address (`etcdContract γ ep`) must be
  global. That is fine except for the lease rows (`leaseViewLb`, §2.2, Q2).

**Requirements on `net-extensions-design.md`** (to check against it once it exists):

- N1: a node's crash ends its listeners, connections and running handlers, as local state;
  addresses survive (as the toy Net's `crashStart := ⌜L' = L⌝`).
- N2: its local start and `crashStart` give the node the right to listen at its own addresses in
  every generation.
- N3: the global start gives `addrFree a` for every address, so that `Hstart` reserves the
  protocols.
- N4: a client's call into a crashed incarnation fails with an indefinite error (or never returns),
  never with a reply the dead incarnation did not send.
- N5: at most once across the server's crash. A non-replayable request handled by incarnation `k`
  is never handled again by `k+1`; grpc's transparent retry only for an "unprocessed" stream.
- N6: each handler run is a forked thread of the node. Then the handler-pool premise (5.5) is the
  theorem's thread bound `Hlive`, not a separate premise.

### 2.4 Raft's per-node durable state: what replaces `raftState_gen`/`nodeVacant`

Today (`raft/v3/Api.lean:287, 899-1031`): `raftState γ id D` and `nodeVacant γ id` are at `hG`. The
realization keeps a per-id generation record keyed by the crash token's name, and a vacancy is "a
token or `crashed`". The crossings `raftState_gen`/`raftState_crash` are `∀ L'`, which forces D28's
weakening (two vacancies give `crashed`, not `False`). Raft's `cluster_alloc` gives them at `hG`, so
it cannot run in `Hstart` (§1.2.1). Proposal (a raft node API change, **Q3**):

- `raftState γ id D`: **global**, exclusive, timeless; moved only by `readyEnter`'s firing and by
  `raftState_crash`. No generation record.
- `nodeVacant γ id`: **global**, exclusive. Two give `False` again (D28's alternative goes for it).
- **new** `nodeHeld γ id` (at `hG`, exclusive): "a node of `id` runs in this generation".
  `StartNode`/`RestartNode`/`NewRawNode` take `nodeVacant` and give `nodeHeld` beside the node.
  `Stop` (and `rawNode_drop`) take `nodeHeld ∗ nodeRunning n 1` and give `nodeVacant` back. The disk
  keeps `nodeHeld` in `diskState` while the server runs (the server deposits it through `diskAcc`
  at the start).
- **new** `nodeHeld_crash : nodeHeld γ id ∗ crashed ⊢ |={⊤}=> nodeVacant γ id`. There is no `L'` and
  no "at every `L'`" argument: `crashed` is the generation's own, and `nodeHeld` is consumed.
  Realization: the vacancy is escrowed at the start in a per-generation invariant `nodeVacant γ id ∨
  crashed@g`. Raft's steps refute `crashed@g` with the step's `notCrashed`; that is the recorded
  "WP step lemma refuting `crashed`" gap, which raft's realization needs today as well.
- `raftState_crash` (batch in flight), restated without `L'`: `∀ D', D.crashOk b D' →
  readyPending n γ id st b ∗ raftState γ id st.durable ∗ crashed ⊢ |={⊤}=> raftState γ id D'`.
  **D6 revisited**: `readyPending` is a new **exclusive** opaque (at `hG`), given by `readyGot` beside
  `readyEnter` and required by `readyEnter`'s firing, so a batch is either entered or crashed, once.
  It cannot be forged (D6's flaw: `readyEnter`'s refutable `nodeRunning` premise). D6's persistent
  `readyBatch` would let a later generation apply the crash law to an old batch whose `D` happens to
  equal the current one. `readyPending` makes the law one-shot.
- **Drop**: `raftState_gen`, `global.spec`, D18 ("the vacancy comes with `raftState`'s crossing"),
  and the section "Crashes and generations"'s at-every-`L'` argument and the generation-record
  realization.
- `cluster_alloc`/`freshIds_take` give global `raftState γ id Durable.init ∗ nodeVacant γ id`.
  `cluster_alloc` takes the global binder and runs in `Hstart`.

### 2.5 The whole-process K6 text

`top.md` K6 is rewritten from this note once the user answers Q1-Q4. Gone: the generation story,
`*_gen`, protocol families, `crashInScope`. Stays: K6's first sentence and the per-disk crash law
list. The Perennial gaps (crash-aware invariant, OsFs `rename`/directory fsync) are now per node.

## 3. The boot program

### 3.1 The test (Go; new, e.g. `examples/etcd/reconflin`)

Nodes: `K` member nodes (indices `0..K-1`; the first `k₀` are initial members, the rest potential
joiners) and one client node `C`. All addresses are fixed in the test: each member node has one
peer address and one client address, and one data directory. The test's single configuration
`TestCfg` is a constant of the program, the same in every generation. Member node `i`'s boot
program (the same at the first boot and after every crash, as `DistLang` requires):

```go
func Member(i int) {
	c := testCfg.node[i]
	cfg := serverCfg(c)                     // one config for all members: StrictReconfigCheck true,
	if !wal.Exist(c.walDir()) && !c.initial { // MaxLearners default, snapshot count Q6
		cfg.NewCluster = false                  // a joiner without a WAL: wait until it is added
		cfg.InitialPeerURLsMap = waitAdded(c)   // MemberList through a client, until c's peer URLs
	}                                         // are listed; the map from that answer
	s, err := etcdserver.NewServer(cfg)       // bootstrap decides: WAL → restart; else new / join
	if err != nil { select {} }               // a failed start idles (3.3 sidestepped; liveness only)
	go servePeer(c.peerAddr, etcdhttp.NewPeerHandler(lg, s)) // raft, /members, /members/promote, /leases
	s.Start()
	go serveClient(s, c.clientAddr)           // v3rpc
	<-s.StopNotify()                          // removed (stopWithDelay) or an error
	select {}                                 // idle forever
}
```

The client node runs `lintest.Run` (txnlin's `Model`, `Apply`, `Gen`, unchanged) over a client of
all `K` client addresses. A reconfigurer goroutine draws random actions: `MemberAddAsLearner` of a
node never added; `MemberPromote` of a learner; `MemberRemove` of a member. It never re-adds a node
(Q5) and never retries an add after an indefinite error. The client panics iff porcupine says the
history is illegal. The Go test runs each node as an OS process and kills and restarts member
processes at random (`kill -9`; optionally lazyfs as etcd's robustness tests), never the client's.
This is the Go counterpart of `DistCrashStep.crash`.

### 3.2 The boot spec and the node's crash rule

**Precondition of a member node's generation** (`P i L`, at `hG = ⟨G, L⟩`):

    memberPre γ ν i := nodeStatic γ ν i ∗ listenRights i ∗ ∃ k, diskState γ dsᵢ k ∗ diskIdle γ dsᵢ k ∗ ⌜roleOk i k⌝

- `nodeStatic` (persistent, global): `srvNet γ ν`, `envUpd γ ecfg`, `peerAddr ν paᵢ`, `srvEp γ caᵢ
  urlsᵢ` and the address's `servesAt γ caᵢ` contract, the request-id prefix fact, and the pure
  `testCfg`.
- `roleOk`: an initial node's `k ∈ {.boot ms mᵢ, .member _}`, a joiner's `k ∈ {.join urlsᵢ, .member
  _}`. That is the diskState kinds of `disk_crash`'s post.

**`Member.spec`** (a function spec, `Spec/<test pkg>/Member.lean`): `{{ isPkgInit ∗ nodeStatic γ ν
i ∗ listenRights i ∗ diskAcc γ dsᵢ ∗ diskIdle γ dsᵢ k ∗ ⌜roleOk i k⌝ ∗ threadToks }} Member #i {{
True }}`. Its proof chains `memberStart_disk` → `NewServer` (any kind; `diskCfgOk` from `testCfg`
and `k`) → `Start` → serving. The joiner's `waitAdded` uses `Client.MemberList`'s answer: `etcdLb γ
σ` with `urlsᵢ`'s member in `σ.members`, which is K2's join premise. No `diskState` passes through
the function: the server reaches it through `diskAcc`, as today.

**`Hwp` for member `i`** (the adequacy-level boot obligation, a lemma of the end theorem's file):

1. From `P i L`, allocate the generation's **crash-aware disk invariant** `inv diskN (diskState
   γ dsᵢ k ∨ crashed@L)` (D17's mechanism, one per generation) and build `diskAcc` from it.
2. Apply `Member.spec`: the WP.
3. The frame `∀ L', crashed@L -∗ extsCrashStart L L' -∗ ownGoState@L' ∅ ={⊤}=∗ P i L'`:
   - open the invariant and take `diskState@L`, leaving `crashed@L`;
   - split `extsCrashStart` into OsFs's `crashRest L L' []` and the network's address-keeping
     resources;
   - apply `disk_crash` at `L'` (its realization: §2.1's paragraph), giving `diskState@L' γ dsᵢ k' ∗
     diskIdle γ dsᵢ k'`;
   - re-take `listenRights i` at `L'` (N2); `nodeStatic` is persistent and global, so it is copied.

**The node's first generation** (its `nodeStart` closure in `Hstart`): OsFs's local start gives
`dataDirFresh dsᵢ`, and the network's gives `listenRights i`. The closure captured `memberBoot γ ms
mᵢ` (initial node) or `memberJoin γ urlsᵢ` (joiner) from `Hstart`'s update; `disk_new`/`disk_join`
turn them into `diskState ∗ diskIdle`. Then `P i L`.

**`Hstart`** (one update): from the network's global start, reserve every member node's peer address
(`peerAddr`) and client address (the etcd contract), then `cluster_alloc` of the `k₀` initial members.
Then, for each joiner node, `urls_reserve`: its `urlsRight` goes to the client's precondition and its
`memberJoin` to the joiner's closure. Then `idSpace_alloc` for the initial members and the client's
invariant `I` over `etcdState γ (State.init ms)`. Finally, split everything into the `K + 1`
`nodeStart`s.

**`Hwp` for the client node**: `P C L := I-facts ∗ (∀ j, servesAt γ caⱼ) ∗ urlsRight` for each
joiner `∗ isPkgInit-ready`, plus the WP of `Client`. The frame: §4.3.

**What the end theorem asks of a node, in one list**: (O1) `Hinit` for its initial state (OsFs
`OsInit` with an empty data directory and a file domain covering every path etcd touches: E4's
directories, `/proc/self/fd`; the network's local init); (O2) its `nodeStart`, from local start
resources and what `Hstart` captured; (O3) `Hwp` in every generation, with the frame above; (O4) its
thread count under `T` (`Hlive`, a hypothesis). Not stuck means every OsFs operation it reaches is
in the extension's domain, so the domain has to cover etcd's paths.

## 4. Reconfiguration in scope, and the client

### 4.1 Specs on the path (most exist; their trusted ones must be proved or modelled)

- **Raft**: `ProposeConfChange` (etcd uses v1: `AddNode`, `AddLearnerNode`, `RemoveNode`; promote
  is `AddNode` of a learner), `ApplyConfChange`, `confDecided`/`confDecisions`, `nodeConf`,
  `freshIds_take`, `node.Status` (for `isLearnerReady`). R2's safety proof under crashes and
  reconfiguration, with the R1 guard fix's invariant ("a conf change followed by a later one in a
  log is committed", `fix-raft-commit-lost.md` §2). 2.6's adopted designs (restart at a
  configuration above the WAL's commit; snapshots whose configuration is ahead) are now goal-path
  obligations of R2.
- **etcd server** (`Spec/go_etcd_io/etcd/server/v3/etcdserver/`): `EtcdServer__{AddMember,
  RemoveMember, PromoteMember, MemberList, configure, applyConfChange, publishV3,
  stopWithDelay}`, `raftNode__ApplyConfChange`, `membership/RaftCluster__*`
  (`ValidateConfigurationChange`, `IsIDRemoved`, ...), v3rpc's `ClusterServer__*`, the client's
  `cluster__Member*` (all exist). **Missing**:
  - `mayAddMember`/`mayRemoveMember`/`mayPromoteMember` with `isLearnerReady`;
  - `promoteMemberHTTP` (a follower forwards a promote to the leader's peer `/members/promote`);
  - `bootstrap`'s join path, translated with bodies: `GetClusterFromRemotePeers`,
    `ValidateClusterAndAssignIDs`, `isMemberBootstrapped`. Today `bootstrap.lean` is trusted, with
    3.4's trust in the peers' `/members` answers;
  - **etcd's peer handler** `etcdhttp.NewPeerHandler` (`/raft`, `/members`, `/members/promote/`,
    `/leases`, `/leases/internal`, `/version`): translate with bodies and specify. This settles
    3.2, makes 3.4's trust a lemma, gives D8's `leasePeerURL`, and is what promote forwarding and
    joins need. `/members` is JSON, so E3's `encoding/json` model of `Member` is on the path.
- **Open questions that become goal-path**:
  - **3.1** (single-use peer-URL sets): kept. Each node's URL set names one member over the run
    (Q5). A removed node does not rejoin. Rejoining at the same address would also reach
    `nonissues/etcd-rafthttp-misaddressed-403-member-removed.md`: a peer still sending to the old
    member gets `403` and stops itself as "removed".
  - **3.3** (a failed start loses its right): sidestepped by idling on failure (§3.1). A crash
    re-runs the boot from a restartable disk (`disk_crash`).
  - **3.4**: proved via the peer handler.
  - **3.5(a)** (`--max-learners`): met, since all members share `testCfg`.
  - **3.2/D8**: the peer handler above.
  - **F10** (`nonissues/etcd-concurrent-remove-last-voter.md`, blocks-proof: yes): the premise "no
    two `RemoveMember`s in flight" **cannot be discharged by the client**. A remove that returned
    an indefinite error may still commit, so even a sequential reconfigurer has removes in flight.
    Under the user's rule, write the failing integration test (failpoint holding the first removal),
    move the finding to `issues/`, and fix it on the fork: `ValidateConfigurationChange` refuses
    removing the last voter at apply (a refused change becomes raft's no-op). That also closes the
    `StrictReconfigCheck = false` path to `nonissues/raft-remove-last-voter-panic.md`.
    `etcdstart`'s configuration leaves the check off; `testCfg` sets it on.
  - **F9** (`etcd-merged-snapshot-same-index-image`, blocks-proof: yes): on the path iff snapshots
    are reachable (joiners and lagging restarted members get `MsgSnap`; `SnapshotCount` 10000 is
    reachable within a large `N`). **Q6**.
- **Fixes from `fix-plan.md` that move onto the goal path**:
  - **R1** (commit lost, the guard fix in `fix-raft-commit-lost.md`): a goal premise until fixed.
  - **R5** (`raft-advance-before-applyconfchange`; the fork's leader wait `4d9282b0f` for
    `etcd-leader-advance-before-applyconfchange`): goal: met by the fork. `node__Advance.lean`'s
    "unapplied conf entries decided skip" is the documented contract (`fd30b41`, doc only). Now
    exercised: concurrent membership changes arise from indefinite errors.
  - **R2-R4**: R4 (`Clone`'s `autoLeave`) is still off the path (v1 changes, no joint
    configurations).
  - **E10** (`issues/etcd-read-after-backend-close-panic.md`, stop gate, L): **mandatory now**. A
    removed member stops itself (`stopWithDelay`, not the program), so the drain premise
    (`HardStop`/`Stop` take the whole `srvGate`) cannot be met. Clients read through every endpoint.
    With the gate, a stopped member's handlers answer `ErrStopped`, an indefinite error.
  - **E28** (`rafthttp` server-version header): met (same binary), cheap to fix.
  - **E26/E27** (`leasehttp` nil response): off (no leases), cheap.
- **Fixed on the fork already and now exercised**: `raft-readindex-removed-leader`,
  `raft-snapshot-during-apply-stale-confchange`, `etcd-unary-interceptor-learner-removed`,
  `etcd-leader-advance-before-applyconfchange`.
- **Membership nonissues whose premises become derivable**: `transportEffectsOk`
  (`etcd-rafthttp-misaddressed-403-member-removed`: "peer URLs address the members they name")
  follows from fixed per-node addresses, single-use URL sets and the network model. The comma and
  bad-URL panics (`etcd-rafthttp-peerurl-comma-split`, `...-addremote-bad-peerurls-panic`): met by
  `testCfg`'s URLs.

### 4.2 Request ids across members (new on the path)

`nonissues/etcd-request-id-member-prefix.md`: request ids are unique across members only through
the member id's low 16 bits. A collision delivers one member's result to another's waiter, a wrong
answer to a client. `idSpace_alloc` requires distinct prefixes. The test can check that for the
initial members (their ids come from fixed URLs), but **a joiner's id is drawn at `MemberAdd`**
(time-salted), so for a joiner the prefix is a probabilistic premise, about 10/65536 for five
members. The note says an integration test could promote it. Fix candidates: refuse at add a member
id whose low 16 bits collide with a current or removed member's; or check, when triggering, that the
result is for the waiter's own request. **Q7**.

### 4.3 The client node and porcupine

**A member crash, as the client sees it**: calls through a connection to the crashed incarnation
fail with an indefinite error (`indefCall`: `Unavailable`, `DeadlineExceeded`, a closed connection;
N4). The balancer and the retry interceptor send later attempts to other endpoints: a read is
resent after `Unavailable`, a non-repeatable write only after an attempt known not applied
(`ApiClient.lean`, `AttemptTriple` case (3)). Learners refuse with `.notSupportedForLearner`, which
is case (3), resent elsewhere. A removed member answers `ErrStopped` (with E10), which is
indefinite. Members not yet started refuse connections. **W0 already covers all of this**:

- K4: an indefinite error fires nothing at return, and the update may fire later.
- A proposal accepted by the crashed member fires at its commit inside raft's invariant, which is
  global. Deposits are not per member.
- A read's persistent update registered in `readCtx` (global) may fire or not.
- txnlin's `Model` keeps a failed write pending forever (`closure`) and ignores a failed read
  (`linkvtxn.go:688-740`).

So `isClient`, `KV.*Triple`, txnlin's `Model`, `Apply` and `Gen`, and `lintest` are unchanged.

What changes:

- (a) The contract at each client address is global and fixed (§2.3). The client gets `servesAt γ
  caⱼ` for all `K` addresses from `Hstart`.
- (b) The client's invariant `I` must also accept the firings of the reconfigurer's updates and of
  members' publications (`envUpd`). Both change `σ.members` only, so `linLog` is unchanged.
- (c) The lease rows' epoch (Q2) does not reach txnlin's proof (no leases), but the server must
  prove the rows.
- (d) The at-most-once claim across a server's crash is N5's, now a property of the grpc model,
  proved, not assumed.
- (e) Porcupine's checker is proved, not trusted (unchanged plan).

**"The client never crashes"** (§1.2.5), two ways:

- **(A)** a general Perennial change to the trusted semantics: `DistCrashStep` with a predicate of
  the nodes that may crash (`crashable : Nat → Bool`). `Hwp` asks for a frame only of crashable
  nodes. Small (S-M), but it changes `DistLang`'s trusted definitions.
- **(B)** no Perennial change: the client's boot program first checks a marker file on its own
  disk. If the marker is present, it blocks forever (`select {}`). Otherwise it creates and fsyncs
  the marker (D7/D31 makes its name durable) before its first operation. The frame gives `P C L'`
  with "the marker is durable". The proof of `I` must then tolerate late firings of a dead client's
  updates whose prophecies are never resolved.

Recommendation: (A), **Q1**.

## 5. What stays a premise of the end theorem

| premise | kind | removable by a fix? |
|---|---|---|
| OsFs's environment (a local ext4 `data=ordered`/xfs, sector-atomic writes, `RLIMIT_FSIZE`; `GooseLang/Ext/OsFs/Impl.lean` header) | physical | no |
| D7/D31: a created directory entry is durable at its file's first sync | physical, accepted | yes in principle (fsync the data directory after `member/`, `member/snap` after `bolt.Open`, the WAL directory after `wal.Create`); the user accepted the premise instead |
| D32: a rename within one directory is atomic across a crash | physical, accepted | no (etcd's design relies on it) |
| `ServerStorage.diskOk` (disk operations succeed; after a crash the WAL holds a prefix, torn only at the tail, no garbage passing the CRC chain, which is **E5**) | physical | E5's CRC part no (any checksum is probabilistic; bbolt's P1 is the same kind); the I/O-error part no (etcd exits on them; liveness) |
| `Wal.crashInScope` | was environment | **yes, goes**: part (a) by the raft fix R1; part (b) by the WAL spec (an inert snapshot record above the commit, `fix-raft-commit-lost.md` §7) |
| **E6**: request-id freshness across a node's restart (the clock never runs back across a crash; fewer than 256 ids per ms; `nonissues/etcd-request-id-restart-reuse.md`). Perennial's `time.Now` is `ArbitraryInt` (`TrustedCode/.../primitive.lean:46`), so nothing about the clock is derivable | about time | yes: a boot counter persisted (backend meta, fsynced at start) and mixed into the generator's suffix makes ids fresh for any clock. A nonissue (no test), so outside the user's rule unless a test is written: **Q8** |
| joiners' request-id prefixes distinct (§4.2) | probabilistic | yes (Q7) |
| `Grpc.msgsFit` (no message over `2^48`) | workload | the server half goes with E2. The client half (grpc-go's codec) may be met by the workload (bounded keys and values, the server's request limit bounding replies); else it stays until grpc-go is fixed |
| `EnvCfg.leaseExpiry = false` | about time | **goes for this test**: no lease is ever granted, so the program can take `leaseExpiry = true` (expiry an environment step), which txnlin's invariant tolerates |
| the step bound `N` (terms, indices, revisions below `2^63`: 5.1, K7) and the thread bound `T` | Perennial's | no (they are the theorem's form). The handler-pool bound (5.5) folds into `T` (N6) |
| `addrFree`'s closed world (5.4: one string per socket, no proxy) | physical | becomes part of the network models' faithfulness claim (the test's addresses are distinct `host:port` strings each bound by its node), not a Lean premise |
| configuration scope (K8: `--max-txn-ops`, request bytes; `ConfigOk`; `UnsafeNoFsync = false`; `StrictReconfigCheck`) | met by `testCfg` | E1/E2 remove two; the rest are configuration facts the program discharges |
| F9, if snapshots are reachable | workload/leader behavior | yes (a fork fix; needs a test first): Q6 |
| `leasePeerURL`, `transportEffectsOk`, `verHdrOk`, 3.4's trust in `/members` | were deployment premises | derived (§4.1) |

Not premises but proof work, recorded as gaps: D17 (the crash-aware invariant), the WP step lemma
refuting `crashed`, OsFs `rename` and directory fsync (E4), and `readyPending` (§2.4).

## 6. Order of work (hardest first)

Sizes: S (days of one agent), M (a week), L (several weeks), XL (the critical path).

1. **Decisions** (Q1-Q8; one sitting with the user). The spec refactor (step 3) needs Q2-Q4.
2. **Riskiest proof arguments, started at once and in parallel:**
   - **2a. XL: raft's safety under per-node crashes with reconfiguration.** Covers R2's invariant
     with the R1 guard, `raftState_crash` with `readyPending`, `nodeHeld_crash`, 2.6's obligations,
     learners and promote. Start with the paper argument (`notes/reconfiguration-safety.md`,
     `fix-raft-commit-lost.md` §2) extended to per-node crash prefixes, then the Lean invariant.
   - **2b. L: the network extensions** (`net-extensions-design.md`): N1-N6 checked against the
     design, and the grpc/http models' ghost state realizing §2.3's laws. Perennial's Grove
     extension (`GooseLang/Ext/Grove`) is a candidate substrate.
   - **2c. M: the Perennial infrastructure:**
     - the crash-aware invariant (D17);
     - the WP step lemma refuting `crashed`;
     - Q1's (A) if chosen;
     - OsFs directories, `rename`, directory fsync, with D7/D31/D32 in the crash relation (E4).

     Each goes on a branch off Perennial's `lean` (or this repository's OsFs), designed on its own.
3. **M: the vocabulary refactor (mechanical, cross-cutting; needs Q2-Q4).**
   - The global binder: `State.lean`, `raft/v3/Api.lean`, `ApiBoot.lean`, `rafthttp/Api.lean`,
     `net/http/Api.lean`, `grpc/Api.lean`.
   - Delete the generation laws: the 12 `*_gen` laws in `State.lean`, `ApiBoot.lean`,
     `rafthttp/Api.lean` and `net/http/Api.lean`; raft's `global` and `raftState_gen`; and
     `memberBoot_crash`/`memberJoin_crash`. Then fix their users.
   - Withdraw D4's families.
   - Re-key `srvEp`; add the lease epoch; make `diskIdle`/`diskHeld` global.
   - Raft's `nodeHeld`/`readyPending`.
   - Rewrite K6.

   One agent, a fresh `spec-reviewer` pass after it.
4. **M: the fork batches.**
   - The raft batch: R1 (branch `raft37-goose-lean-a3`, done locally), R2-R5.
   - The etcd goal batch of `fix-plan.md`.
   - Added to the etcd batch: E10 (L inside it), F10 (test, then fix, S), request-id prefixes (Q7,
     S), E28 (S), and E6 and F9 if chosen.
   - Re-translate each fork once.
5. **M: the test and its boot spec.**
   - Write `examples/etcd/reconflin` (member boot, client node with `lintest` and the reconfigurer,
     the multi-process kill harness) and run it in Go.
   - Write `Member.spec`, `Client.spec`, and the end theorem's statement with `Hstart`/`Hwp` as
     lemmas, `sorry`-free up to the callees' specs (a statement-level check early: the
     schedule-adequacy-early rule).
6. **L: specs for code newly on the path:**
   - `etcdhttp.NewPeerHandler` and its handlers;
   - `bootstrap`'s join path, translated with bodies;
   - `promoteMemberHTTP`, `may*Member`, `isLearnerReady`;
   - E3's JSON models for `Member`.
7. **L: the proofs of the boot spec and the disk crash.**
   - `disk_crash`'s realization per node (mostly the existing plan);
   - the frame;
   - `Hstart`;
   - the client invariant's acceptance of reconfigurations;
   - porcupine's checker (already planned);
   - the adequacy theorem.

Steps 2a, 2b and 2c run in parallel (disjoint). Step 3 unblocks 5 and 6. Step 4 can start
immediately for R1, F10, E10 and Q7, since they do not depend on the refactor.

## 7. Questions for the user

- **Q1.** "The client never crashes": (A) a general change to Perennial's trusted `DistLang` (a set
  of crashable nodes), or (B) the client's program idles after a crash behind a durable marker file
  (no Perennial change; the client's invariant tolerates late firings)? Recommended: (A).
- **Q2.** Lease views across a member's crash: index W0's `leaseViewLb` by a crash epoch bumped by
  `disk_crash` (client-visible ghost state; the per-member lease rows hold within one epoch), or gate
  the per-member lease rows on a crash-free deployment token? Recommended: the epoch.
- **Q3.** Raft's approved node API: global `raftState`/`nodeVacant`, a new per-generation `nodeHeld`
  with `nodeHeld_crash`, and an exclusive `readyPending` in place of D6's `readyBatch`. Approve?
- **Q4.** D4 withdrawn: one protocol per address for the whole run, the 2026-10-22 boundary's shape.
  Acknowledge?
- **Q5.** Reconfiguration workload: each member node hosts at most one member over the run (no
  rejoin after removal; single-use URL sets kept, 3.1), or rejoin through fresh addresses and a wiped
  data directory (more boot-program and spec work)? Recommended: no rejoin.
- **Q6.** Snapshots: keep etcd's snapshotting reachable in the test, which puts F9 on the path (write
  its test, then a fork fix), or configure `SnapshotCount` out of reach (a scope choice that removes
  the install paths from the goal)? Recommended: keep them, with F9's test and fix.
- **Q7.** Joiners' request-id prefixes and F10: write the failing tests and fix both on the fork (F10:
  refuse removing the last voter at apply; ids: refuse a colliding member id at add, or check the
  waiter's ownership at trigger)? Recommended: yes.
- **Q8.** E6 (request ids across a member's restart): keep the clock premise, or take a fork fix (a
  persisted boot counter in the id suffix; needs a test to fall under the rule)?
