/-
**DRAFTS (N3, design only): the interim axioms `Watch_dist.wp_proof` and `RequestProgress_dist.wp_proof`**
(`notes/etcd-dist-plan.md` §22; #50, the etcd_safe lead, 2026-11-25). Lean-first (no Rocq counterpart).

NOTHING IS DECLARED HERE: no axiom, no proof, no `sorry`; unbuilt; nothing imports this file. The statements
are `Spec/.../etcd/dist/WatchDist.lean`'s. At adoption (after the coordinator's decision, an `axiom`-skill
review given the code and not this reasoning, and the etcd_safe packet) the two blocks below become this
file's declarations, as `KVGetDist.lean`'s:

  axiom Watch_dist.wp_proof : Watch_dist.spec (GF := GF) (hG := hG)
  axiom RequestProgress_dist.wp_proof : RequestProgress_dist.spec (GF := GF) (hG := hG)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist

/-!
## `Watch_dist.wp_proof` (draft docstring)

**`(*watcher).Watch(ctx, key, opts...)` across machines** (interim trust boundary until #24's S2 client
side with streams; see the spec). What it asserts of clientv3 v3.6 (the fork's `goose-lean`, with the
watch-resume fixes `cafce83d8`, `c15c7dda8`, `2e2dc077c`, `2aed163b1`) and grpc-go v1.84 (the model) over
the net extension.

**Why it is an axiom** (the standing rule's order):
1. *Real Go translated?* Yes: clientv3's `watch.go` with bodies, grpc-go's model `models/grpc`. In one
   process the call is proved (`watcher.Watch.spec`, over `isClientWatcher V w`, whose `watchSrvFacts V`
   holds the `Watch` stream's registration at each member's address, `isGrpcStreamsMd … watchUp
   watchSpec`). Across machines the stream goes through grpc's `NewStream` over the net extension: this
   line's S2 interface has unary table entries only (`GrpcSvc := GoString → Option (GrpcEntry GF)`),
   `etcdSvc` has no law, and no proof establishes the protocols of any bytes (`grpcCliPI`/`grpcSrvPI`
   opaque), so no `watchConnFacts V` can be built for a remote member: nothing can be proved over the
   existing S2/S5 statements. Needs #24's S2 client side for streams (SW1's `.stream` entries and a
   proved `NewStream` over the model).
2. *A Go model with the same behaviour* is the grpc model itself, which is what S2 proves over: the
   same gap.
3. *Trusted code*: a stand-in for the watcher and grpc's stream would still need the wire proof, and
   would trust the whole reconnection logic (`run`, `serveSubstream`, the resume queue) that the
   single-process proof verifies, instead of one contract.

**Why it is true.** It is `watcher.Watch.spec` with `isClientWatcher V w ∗ ⌜V.kst = γ.st⌝` replaced by
`watchClientAt` (the address facts at `Γ`), `γ := Γ.kv`, and no auth row:
* *Who answers.* As `KV_Get_dist`: the client dials the endpoints themselves (`clientNoProxy`); each
  endpoint's table is set once by the start and answered only by `Serve_dist` at a member whose KV names
  are `kvCongr` to `Γ.kv`; another program at the address (a raw listener, a server registering nothing)
  answers no stream (a stream error: the error arm, or a closed channel). So every response is a real
  member's `Watch` handler, at KV names `kvSame` to `Γ.kv`, and that handler's spec is the one its
  in-process proof meets (`v3rpc.watchSpec`).
* *Reconnection and resumption are inside the triple.* The single-process spec is already over a
  connection to several members (`V.nm`, W3b): on a stream error that `isHaltErr` does not halt on
  (`Unavailable`, `Internal`), `run` opens a new gRPC stream (the balancer may pick another endpoint) and
  re-creates each live substream from its resume revision, the cursor plus one (moving only forward:
  `2e2dc077c`). The elements are per response with one cursor across streams, so the post does not
  change: the resumed member's events are of the same cluster history (every member applies one
  committed log; a lagging member's store is a prefix of it, and a watch from a revision it has not
  reached waits for it), and its progress notification is sent only once its store reached the
  watcher's start (`progressIfSync`), so `p ≥ c` holds at the new member too.
* *Errors, faults, cancellation are allowed outcomes.* A stream error that halts (any other status, a
  canceled context, the server's cancel, a compaction past the start: `CompactRevision ≠ 0`) is a
  response with `watchErr` (the error arm, position kept, its compaction revision `cmpOkOf`), after which
  the channel closes; a closed channel is `isSpsc`'s end. Nothing says a response ever arrives. The read
  update is persistent (`□`), so a resumed or repeated read fires it again harmlessly.
* *What a response claims* is `watcher.Watch.spec`'s element at `Γ.kv`: the update's `□ Q σ` at the
  cluster's state `σ` it fired at, the read of `σ`'s range events from the cursor (`watchStateRespOkP`:
  exact events in revision order, or a progress notification with no event skipped), and the
  compaction revision the cluster's permit (`kvCmpPermit Γ.kv`: a positive revision `cret` behind one
  the cluster's requested log `rlog` reached), which the in-process proof derives from the member's
  `crevOk` (`kvCpOk` at its names, `cmpOkOf_same` through `kvSame`).
* *Any auth mode.* A member checks a watch's permission only at its create; a refused create is a
  canceled response (the error arm). With auth on, a token refresh on reconnection (`getToken` re-runs)
  that fails is a stream error. The auth row of the single-process spec (`watchCheckOk`, gated on
  `V.nm = 1`) is not claimed: it reads member 0's auth tag and server, per-member names not in `Γ`
  (N11).

**Margin: the watcher's environment.** `isNewClient cl eps V` fixes `V` at `New`, and the watcher's lock
invariant (`watcherMu V w`) keeps each stream's `isWGS V G`, which holds `watchSrvFacts V`. The draft is
stated for every `V`, as the KV contracts are, and its post reads nothing of `V`. No proved spec opens
the lock without `isClientWatcher V w` (every `watcher` method's spec takes it; `Client.Close` is
names-only, `clientCoreAt`), so nothing can learn `watchSrvFacts V` from the lock but these two axioms.
A retiring proof meets the `∀ V` form only after a client-proof refactor (no trust) that takes
`watchSrvFacts` out of `isWGS` and gives it to `run` per stream from the connection's table, or at the
table's own environment `V` (a weaker statement): §22.3.

Retired by #24's S2 client side with streams: `etcdSvc` defined with its `Watch` stream entry (each
member's `watchUp`/`watchSpec`), `NewStream` over the net model, and this statement proved from
`watcher.Watch.spec` over `isClientWatcher` built from the table (`isNewClient_watcher_of`,
`watchConnFacts_of_members`), `V.kv` `kvSame` to `Γ.kv` from `Serve_dist`'s `kvCongr`.

## `RequestProgress_dist.wp_proof` (draft docstring)

**`(*watcher).RequestProgress(ctx)` across machines** (interim trust boundary, as `Watch_dist`).

**Why it is an axiom.** As `Watch_dist`: real Go translated and proved in one process
(`watcher.RequestProgress.spec`, over `isClientWatcher V w`); the call takes the watcher's lock and, when
no stream has `ctx`'s key, starts one (`newWatcherGRPCStream`, whose `run` calls `NewStream` across
machines), so it needs the same stream facts, which nothing proves across machines yet.

**Why it is true.** The call only sends a `*progressRequest` on the stream's `reqc` (or returns the
closed watcher's, the context's or the stream's close error), and grpc's `status` accepts each error it
returns (`statusErrOk`); nothing is claimed of the server's answer, which arrives, if ever, as a
progress response of the watch channels `Watch_dist` describes. Retired with `Watch_dist`.
-/
