/-
`(*watcher).Watch(ctx, key, opts...)` and `(*watcher).RequestProgress(ctx)` by a client of members at other
machines, at the cluster view: two interim trust-boundary axioms (`notes/etcd-dist-plan.md` §22, route (b) of
§22.6). Lean-first (no Rocq counterpart).

**Why axioms and not theorems.** The Go is translated (clientv3 v3.6's `watch.go` with bodies, grpc-go v1.84's
model) and both calls are proved in one process (`watcher.Watch.spec`, `watcher.RequestProgress.spec`, over
`isClientWatcher V w`). Across machines the watcher's gRPC stream needs its method's entry in the dialed
address's service table, `etcd_dist.etcdSvc Γ mid "/etcdserverpb.Watch/Watch"`, and that entry cannot be stated
yet: the proved stream contract (`v3rpc.watchMethod pw R W`) names each member's run-time heap values and
`NewServer`'s existential apply environment, which no start can fix and no client can learn before `New`.
Stating it needs S2's etcd-side stream work: SW1's `.stream` entries (on `lean`) with etcd's watch contract
restated heap-free and indexed by the view, a restated A1 (`etcdSvc`) and `Serve_dist`'s `grpcServes`
obligation for the entry (§22.6, route (a)).

**What retires them.** That work (route (a), after M1 lands): each statement then becomes a theorem, proved
from `watcher.Watch.spec`/`watcher.RequestProgress.spec` over an `isClientWatcher` built from the table's
entries at every endpoint (`isNewClient_watcher_of`), the members' KV names `kvSame` to `Γ.kv` by
`Serve_dist`'s `kvCongr`. The statements do not change.

**The `∀ V` form.** Both are stated for every watcher environment `V` that `New` was given (their posts read
nothing of it). The retiring proof meets that form only after the watcher-environment refactor (no trust):
`watchSrvFacts` taken out of the watcher lock's `isWGS V G` and given to `run` per stream from the
connection's table; without it, the theorem would hold only at the table's own environment, a weaker
statement (§22.3, "The watcher's environment").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`(*watcher).Watch(ctx, key, opts...)` across machines** (interim trust boundary until S2's etcd-side
stream work; see the spec and the file header). What it asserts of clientv3 v3.6 (the fork's `goose-lean`,
with the watch-resume fixes) and grpc-go v1.84 (the model) over the net extension.

**Why it is an axiom** (the standing rule's order):
1. *Real Go translated?* Yes: clientv3's `watch.go` with bodies, grpc-go's model. In one process the call is
   proved (`watcher.Watch.spec`, over `isClientWatcher V w`, whose `watchSrvFacts V` holds the `Watch`
   stream's registration at each member's address). Across machines the stream goes through grpc's
   `NewStream` over the net extension, which reads the stream's entry off the dialed address's table. This
   line's `GrpcSvc` has unary entries only, and `etcdSvc` has no law. On `lean`, SW1 adds `.stream` entries
   and the transport (`NewStream`, `Serve`), but the entry etcd's member would need, `watchMethod pw R W`,
   names the member's server, lock and logger (heap locations allocated at run time), its store handle and
   its whole apply environment (`NewServer`'s existential), none a function of `(Γ, mid)`. So no
   `watchConnFacts V` exists for a remote member: nothing can be proved yet (§22.6).
2. *A Go model with the same behaviour* is the grpc model itself, which is what the retiring proof uses: the
   same gap (the entry).
3. *Trusted code*: a stand-in for the watcher and grpc's stream would still need the entry, and would trust
   the reconnection logic (`run`, `serveSubstream`, the resume queue) that the single-process proof
   verifies, instead of one contract.

**Why it is true.** It is `watcher.Watch.spec` with `isClientWatcher V w ∗ ⌜V.kst = γ.st⌝` replaced by
`watchClientAt` (the address facts at `Γ`), `γ := Γ.kv`, and no auth row:
* *Who answers.* As `KV_Get_dist`: the client dials the endpoints themselves (`clientNoProxy`); each
  endpoint's table is set once by the start and answered by `Serve_dist` at a member whose KV names are
  `kvCongr` to `Γ.kv`, or by a program that answers no stream (a raw listener writes nothing; a gRPC
  server registering nothing gets every stream `Unimplemented`): a stream error, so the error arm or a
  closed channel. So every response with content is a real member's `Watch` handler at KV names `kvSame`
  to `Γ.kv`, and that handler's spec is the one its in-process proof meets (`v3rpc.watchSpec`).
* *Reconnection and resumption are inside the triple.* The single-process spec is already over a
  connection to several members (`V.nm`): on a stream error that `isHaltErr` does not halt on
  (`Unavailable`, `Internal`), `run` opens a new gRPC stream (the balancer may pick another endpoint) and
  re-creates each live substream from its resume revision, the cursor plus one (moving only forward). The
  elements are per response with one cursor across streams, so the post does not change: a resumed
  member's events are of the same cluster history (every member applies one committed log; a lagging
  member's store is a prefix of it, and a watch from a revision it has not reached waits for it), and its
  progress notification is sent only once its store reached the watcher's start (`progressIfSync`).
* *Errors, faults, cancellation are allowed outcomes.* A stream error that halts (any other status, a
  canceled context, the server's cancel, a compaction past the start: `CompactRevision ≠ 0`) is a response
  with an error (the error arm, position kept, its compaction revision `cmpOkOf Γ.kv`), after which the
  channel closes. Nothing says a response ever arrives. The read update is persistent (`□`), so a resumed
  or repeated read fires it again harmlessly.
* *What a response claims* is `watcher.Watch.spec`'s element at `Γ.kv`: the update's `□ Q σ` at the
  cluster's state `σ` it fired at, the read of `σ`'s range events from the cursor (`watchStateRespOkP`),
  and the compaction revision the cluster's permit (`cmpOkOf Γ.kv`), which the in-process proof derives
  from the member's `crevOk` (`kvCpOk` at its names, `cmpOkOf_same` through `kvSame`).
* *Any auth mode.* A member checks a watch's permission only at its create; a refused create is a
  canceled response (the error arm). The single-process spec's auth row (`watchCheckOk`, gated on
  `V.nm = 1`) is not claimed: it reads member 0's auth tag and server, per-member names not in `Γ` (N11).

**Margin: the watcher's environment.** `isNewClient cl eps V` fixes `V` at `New`, and the watcher's lock
invariant keeps each stream's `isWGS V G`, which holds `watchSrvFacts V`. No proved spec opens the lock
without `isClientWatcher V w` (every `watcher` method's spec takes it; `Client.Close` is names-only), so
nothing but these two axioms acts on the lock without those facts. The `∀ V` form needs the
watcher-environment refactor for its retiring proof (file header).

Retired by S2's etcd-side stream work (§22.6 route (a)): the `Watch` entry stated at `Γ`, and this statement
proved from `watcher.Watch.spec` over `isClientWatcher` built from the table (`isNewClient_watcher_of`),
`V.kv` `kvSame` to `Γ.kv` from `Serve_dist`'s `kvCongr`. The statement does not change. -/
axiom Watch_dist.wp_proof : Watch_dist.spec (GF := GF) (hG := hG)

/-- **`(*watcher).RequestProgress(ctx)` across machines** (interim trust boundary, as `Watch_dist`; see the
file header).

**Why it is an axiom.** As `Watch_dist`: the real Go is translated and proved in one process
(`watcher.RequestProgress.spec`, over `isClientWatcher V w`); the call takes the watcher's lock and, when no
stream has `ctx`'s key, starts one (`newWatcherGRPCStream`, whose `run` calls `NewStream` across machines),
so it needs the same stream entry, which cannot be stated yet (§22.6).

**Why it is true.** The call only sends a `*progressRequest` on the stream's `reqc` (or returns the closed
watcher's, the context's or the stream's close error), and grpc's `status` accepts each error it returns
(`statusErrOk`); nothing is claimed of the server's answer, which arrives, if ever, as a progress response
of the watch channels `Watch_dist` describes.

Retired with `Watch_dist`, from `watcher.RequestProgress.spec`; its `∀ V` form needs the same
watcher-environment refactor (file header). -/
axiom RequestProgress_dist.wp_proof : RequestProgress_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
