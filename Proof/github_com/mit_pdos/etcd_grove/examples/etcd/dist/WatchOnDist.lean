/-
`(*watcher).Watch(ctx, key, opts...)` by a client of auth-on members at other machines, at the cluster view,
with the auth row: an interim trust-boundary axiom (`notes/etcd-dist-watchon.md`; `Watch_dist`'s route,
`notes/etcd-dist-plan.md` §22.6 (b)). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace authd

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **INTERIM: `WatchOn_dist`** (`(*watcher).Watch(ctx, key, opts...)` across machines, auth on; trust
boundary until S2's etcd-side stream work, as `Watch_dist`; the statement and its mirror are in the spec's
docstring). What it asserts of clientv3 v3.6 (the fork's `goose-lean`), grpc-go v1.84 (the model) and auth-on
etcd members (the simple token provider, no client-certificate auth) over the net extension.

**Why it is an axiom** (the standing rule's order; route table row, `Watch_dist`'s):
1. *Real Go translated?* Yes, and proved in one process (`watcher.Watch.spec`, its row `watchCheckOk` from
   `v3rpc.watchAuthed`); across machines the stream needs the `Watch` entry of `etcdSvc Γ mid`, which cannot be
   stated before S2's etcd-side stream work (`WatchDist.lean`'s header, §22.6).
2. *A Go model* is the grpc model itself: the same gap.
3. *Trusted code* would trust the reconnection logic the single-process proof verifies.
Retired by the same route as `Watch_dist` (route (a): the `Watch` entry at `Γ` from SW1's `.stream` entries),
from `watcher.Watch.spec` over the table's `isClientWatcher`, the row from `watchCheckOk` through the entry's
member facts at `Γ.au mid` (a check at an index at least the member's published floor) and `authFloorD`'s
update (the floor's state the history's after a committed `L' ⊒ L₀`, F7's retirement obligation R1), the
token's binding through `New`'s `attemptTokOk` and `outTokOkS`.

**Why it is true.** It is `Watch_dist` (whose docstring's "who answers", reconnection, errors and elements
arguments carry over: with auth on, `Serve_dist` serves a member at `Γ.au mid` with `memberUpOnL`) plus the
row, which etcd's watch server gives:
* *Every create is checked at the member it reaches.* `serverWatchStream.recvLoop` checks each create request
  with `isWatchPermitted` (`AuthInfoFromCtx` of the stream's context, an empty `AuthInfo` for none, then
  `IsRangePermitted` on the key, `""` rewritten to `"\x00"`, and the request's range end) before it registers
  the watcher; a refusal sends a created-and-canceled response with no events (the error arm). Events are
  only sent to a registered watcher, so a response with events is of a stream whose create passed. Each
  reconnection opens a new gRPC stream and re-creates the watch, checked again at its member.
* *The user.* The stream's token is the client's own (clientv3's per-RPC credentials, the token `New` obtained
  for `cfg`'s user; none for an anonymous client) or the stream's context's (`token`, else `authorization`,
  `Bearer ` trimmed). The watcher shares a stream among contexts of one stream key, so the stream's context is
  some context of `om`'s key, whose tokens `outTokOkS` makes absent, or (anonymous only) never of the simple
  provider's shape, which every member refuses (`ErrInvalidAuthToken`). So a passed check is for an
  `AuthInfo` of user `""` (no token) or `P`'s (`userOk`). No TLS identity: the deployment has no
  client-certificate auth.
* *The state.* The check reads the member's auth store at that time, at an index at least the member's
  published index when the call began (as in one process, `watchClassFrom` at `authPubLbM`); `watchFloorsD`
  gives that index's floor above `L₀`, and every state from the floor on is the history's after a committed
  prefix extending `L₀` (`authFloorD`). Across machines a lagging member may also apply a snapshot, which no
  single-process run does (`applySnapshot`: `kv.Restore`, then `authStore.Recover`, which sets the backend, the
  revision and the permission cache before the enabled flag). A check that interleaves reads the pre-snapshot
  state or the snapshot's, piece by piece. Its pass is still witnessed by one of them: a disabled flag, a root
  user, or a cache entry that covers the range (and so a user that exists at that state). The snapshot's state
  is the leader's at its applied index, ahead of the member's, so both are at or after the floor. The window
  between `kv.Restore` and `Recover` (KV new, auth old) checks at the old state, and the row claims only the
  create's check (`notes/axiom-review/watchon-dist.md` §2, Go test [b]). The floor must be the serving
  member's own: a member that lags across `AuthEnable` passes an anonymous create at its old state and then
  streams post-enable events (Go test [lag]). So `watchFloorsD` asks for one at every endpoint, as the
  workload's per-member barriers give.
* *Which member.* The floor at endpoint `a` names some `mid` with `etcdAddrAt a Γ mid`; an address's table is
  set once, and `etcdSvc Γ mid` differs per member (its entries are at the member's names `Γ.au mid`, distinct
  by the premise), so the floor is the serving member's.

**Review** `notes/axiom-review/watchon-dist.md` (2026-11-26, fresh `axiom`-skill review with a Go test on a
3-member auth-on cluster, `notes/axiom-review/watchon-dist/`): SOUND WITH FIXES, the statement unchanged; F1–F3
applied (docstrings); F4 (`Watch_dist`'s "Any auth mode" bullet, stale since F7 step 3) and F5 (`Serve_dist`'s
docstring names `WatchOn_dist`'s streams) go with the adoption commit (`notes/etcd-dist-watchon.md`).

**Margin.** The row is cluster-level only (no member-local check at `Γ.au mid`): what the auth workload's
refused watch needs. The watcher's lock: as `Watch_dist` (this axiom locks `w.mu` and says nothing of it in
its post; `WatchDist.lean`'s header, trigger (4): reviewed with this axiom). -/
axiom WatchOn_dist.wp_proof : WatchOn_dist.spec (GF := GF) (hG := hG)

end proof

end authd
end etcd_dist
end EtcdGrove
end Perennial
