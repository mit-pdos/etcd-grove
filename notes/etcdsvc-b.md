# Stage B′: etcd's service table defined for auth-off KV (2026-11-28)

Branch `etcdsvc-b/2026-11-27` (stage A, the client's `isKv` in registry form, merged with `lean` and its
grpc no-refusal flag, `notes/grpc-nr-e.md`). Draft of trusted text, for review; not landed.

## Net trust direction

- **−5 axioms**: `KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`, `KV_Compact_dist`, `Txn_Commit_dist`
  (`.wp_proof`, with their `Spec/` files) are deleted. The theorems `Client_Put_dist`/`Client_Get_dist` go too.
- **The opaque table `etcdSvc` becomes a definition** over a new opaque table `etcdSvcRest` (no law), so the
  axiom count of the table is unchanged (one).
- **`Serve_dist`'s statement is unchanged; its meaning grows**: serving the defined table now claims, of an
  auth-off member, that its KV handlers through etcd's unary chain meet the view specs and never return a
  refusal (`grpcRunNRMd`). The argument is below ("The no-refusal claim").
- No top-level statement changes. Internal specs that change (all untrusted): `checkCompactRev.spec` (premise
  `Γ.auth = false`), `watchShare` (conjunct `Γ.auth = false`; `RunWatch.spec`, `RunCache.spec` read it), the
  kvremote laws `client_Get_dist.law`/`client_List_dist.law` (premise `Γ.auth = false`), and the client's
  write-path vocabulary (`isKv`'s dup clause and `kvReqPre`/`txnReqPre`/`reqPre`/`modePre`: below).

## Trusted declarations, before → after

### `etcd_dist.etcdSvc` (`Proof/.../examples/etcd/dist/S2Interim.lean`)

Before (axiom; docstring: intended to be #24's `etcdSvc`, no law):
```
axiom etcdSvc [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    {GF : BundledGFunctors} [GooseGlobalGS .hasLC GF]
    (Γ : DistView) (mid : w64) : GrpcSvc GF
```
After (definition; same binders through the section variables):
```
def etcdKvSvc (γk : KVNames) : GrpcSvc GF := fun name =>
  if name = go!"/etcdserverpb.KV/Put" then
    some (.unary ⟨client.putReqWire, client.putRespWire, client.etcdPutSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Range" then
    some (.unary ⟨client.rangeReqWire, client.rangeRespWire, client.etcdRangeSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/DeleteRange" then
    some (.unary ⟨client.delReqWire, client.delRespWire, client.etcdDeleteSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Txn" then
    some (.unary ⟨client.txnReqWire, client.txnRespWire, client.etcdTxnSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Compact" then
    some (.unary ⟨client.compactReqWire, client.compactRespWire, client.etcdCompactSpecV γk, true⟩)
  else none

def etcdSvc (Γ : DistView) (mid : w64) : GrpcSvc GF := fun name =>
  match Γ.auth, etcdKvSvc (GF := GF) Γ.kv name with
  | false, some e => some e
  | _, _ => etcdSvcRest Γ mid name
```
The specs are stage A's view specs (`client/v3/KVService.lean`, heap-free, naming no member); the wire parts
are `KVServiceV.lean`'s (`pbPutRequest.wire = putReqWire`, `rfl`). `Compact`'s entry is unconditional: its view
spec requires `γk.cmp = true` of its caller, so on a non-compacting cluster no call meets it. The guard
`Γ.auth = false` is interim (decided: no auth modes, nomode N1–N4); it goes when the KV view specs are single
(N4), and auth-on members then serve the same entries.

### `etcd_dist.etcdSvcRest` (new axiom, same file)

```
axiom etcdSvcRest [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    {GF : BundledGFunctors} [GooseGlobalGS .hasLC GF]
    (Γ : DistView) (mid : w64) : GrpcSvc GF
```
The old `etcdSvc`'s text under a new name, read only by `etcdSvc` (every entry but the auth-off KV ones). No law,
so the arguments that rested on the opaque table stay as they were for these entries: the lease axioms'
free-name argument, the watch streams, Condition C (`notes/axiom-review/f7-rerev-a.md`): no proof learns an
entry of it, and a server serves it only by registering nothing under its names.

### `Serve_dist.wp_proof` (`Proof/.../dist/ServeDist.lean`; spec `Spec/.../dist/ServeDist.lean`)

The statement (`Serve_dist.spec`) is unchanged, token for token. Its docstrings change:
- the list of calls a connection carries: with auth off, etcd's KV methods at their view entries (`etcdKvSvc`),
  in place of the deleted `KV_*_dist`/`Txn_Commit_dist`;
- a new paragraph, "The KV entries never refuse" (below), in the axiom's docstring, and a short one in the spec's;
- "Retired by": S2's `grpcServes (etcdSvc Γ mid)`, with `grpcRunNRMd` of etcd's KV handlers and chain.

### Unchanged statements whose docstrings were touched

Doc-only (rule 16: pre-approved): the `*On_dist`, `Lease_*_dist`, `Auth_*_dist`, `New_user_dist`, `Watch_dist`
axioms' "Why it is an axiom" paragraphs said "as `KV_Put_dist`" and "`etcdSvc` has no law": now "`etcdSvc`'s entry
is `etcdSvcRest`'s, with no law". The `KV_GetOn_dist`, `KV_DeleteOn_dist`, `Txn_CommitOn_dist` specs' docstrings
named the deleted auth-off statements as their shape; they now name `kv.Get.spec` etc. at a `kvClientAt`. The
kvremote and putget top-level docstrings name the table and `Serve_dist` instead of the deleted axioms.

## The client side (untrusted)

`isKv api γ dup`'s third conjunct was `⌜dup = false → ∀ a ∈ addrs, noRefusalAt a⌝`; `noRefusalAt` is opaque and
only `etcd_noRefusal` (in-process) gives it, so a remote member could not supply it. Now it is
`kvDupNR dup addrs := ⌜dup = true⌝ ∨ kvWriteNR addrs`, with
`kvWriteNR addrs := ⌜∀ a ∈ addrs, noRefusalAt a⌝ ∨ (isGrpcRpcsNR addrs Put ∗ isGrpcRpcsNR addrs DeleteRange ∗
isGrpcRpcsNR addrs Txn)`. The write path carries it down: `kvReqPre`/`txnReqPre` (`kvWriteNR`), `reqPre` and
`modePre .write` (`noRefusalFor method addr := ⌜∀ a ∈ addr, noRefusalAt a⌝ ∨ isGrpcRpcsNR addr method`). In the
retry interceptor's proof (`Client__unaryClientInterceptor.lean`) an attempt's error has `d ∉ refusalDescs` from
either of `grpcInvokerOk`'s two clauses (the `noRefusalAt` one, or E's `isGrpcRpcsNR addrs method -∗ ⌜d ∉ …⌝`), so
a write is still never retried. In-process starts still give the left disjunct (`isKv_of_members`).

Across machines, `isKv_of_kvClientAt` (`KVClientDist.lean`): `kvClientAt cl api eps V Γ ⊢ isKv api Γ.kv false` for
`Γ.auth = false`, from `isNewClient`'s `kvObjAt` and each endpoint's `etcdAddrAt` (`isGrpcRpcMd_of_addr` and
`isGrpcRpcNR_of_addr` at `etcdSvc_kv` and `etcdKvSvc_*`). The users of the deleted axioms take the client specs
(`kv.Put.spec`, `kv.Get.spec`, `kv.Delete.spec`, `kv.Compact.spec`, `txn.Commit.spec`) and their linking modules
pass the client's linked `client.v3.kv.wp_Put`, ...: `client/{CompactCallsDist, KVCallsDist, WriterDist,
CacheWorkDefs, RunCompact, RunPutGet, RunDurable, RunCache, checkCompactRev}`, `kvremote/{CallDist,
CallDistLinked, Link}`, `putget/{Client, ClientCalls (new: putget's put and get, the old Client_*_dist proofs),
AdequacyClient}`, `putgetk/AdequacyClient`. `KV_Get_dist` and `KV_Compact_dist` had no auth premise; their users
now need `Γ.auth = false`, which every deployment start has (`ClusterNames.view`, `on := false`): hence the
`checkCompactRev.spec`, `watchShare` and Get/List law premises above.

## The no-refusal claim (Serve_dist, auth off)

`grpcServesEnt` of a flagged entry is `grpcRunNRMd`: the run of the registered handler `mh srv` through the
server's composed interceptor over etcd's chain (`newLogUnaryInterceptor`, `newUnaryInterceptor`, grpc-prometheus)
and grpc's `dec` returns `nil` or an error whose description is none of `refusalDescs`:
`"etcdserver: invalid auth token"`, `"etcdserver: revision of auth store is old"`, `"etcdserver: user name is
empty"`, `"etcdserver: rpc not supported for learner"`, `"there is no address available"`, `"there is no
connection available"`. At the etcd pin (`6e8f0c004` lineage, `.lake/go-src/etcd`):

1. **Auth refusals.** `togRPCError` (`v3rpc/util.go`) maps `auth.ErrUserEmpty`, `ErrInvalidAuthToken` and
   `ErrAuthOldRevision` to the first three. On a KV call these come only from `AuthInfoFromCtx`, `isOpPermitted`,
   `IsAdminPermitted` and the apply's revision check, each of which returns early when `!as.IsAuthEnabled()`
   (the argument of `etcd_noRefusal`, `v3rpc/NoRefusal.lean`). The member's auth store starts disabled
   (`memberUpL`: `E.authOn = false`, a fresh backend's `isAuthStore … false`) and stays disabled: enabling it is
   an `AuthEnable` request, a unary call of the Auth service. On an address serving an auth-off view, that entry
   is `etcdSvcRest`'s (no law), so no proof calls it through `Invoke` (`isGrpcRpcMd` needs the entry); the
   `Auth_*_dist` contracts require `Γ.auth = true`, and an address carries one table (set once, `etcdAddr_set`
   spends `addrUnset`). The model agrees (`dispatchOk false` excludes `AuthEnable`, `kvInv`'s `authOn = false`).
2. **The learner refusal** (`interceptor.go:54`, `if s.IsMemberExist(s.MemberID()) && s.IsLearner() &&
   !isRPCSupportedForLearner(req)`; `:225` is the stream interceptor's, no KV entry): the serving member is a voter
   for its whole life.
   - It was built by `NewServer` (`NewServer.specG_dist`, or the in-process `NewServer.spec`, the only producers
     of `memberUpL`'s server resources), both under `bootCfgFresh cfg U`: `cfg.NewCluster' = true`, no
     discovery. `bootstrapNewClusterNoWAL` builds the membership with `membership.NewClusterFromURLsMap`, whose
     members are `NewMember(name, urls, token, nil)`, i.e. `newMember(..., false)`: every initial member,
     this one included, is a voter (`examples/lib/etcdstart/common.go`: `NewCluster: true`, the deployment's
     peer map).
   - etcd has no voter-to-learner change. Conf changes come only from the server's member API (`AddMember`,
     `RemoveMember`, `UpdateMember`, `PromoteMember`, through `configure`). At apply, `applyConfChange` runs
     `ValidateConfigurationChange` (`membership/cluster.go:306`): an `AddNode`/`AddLearnerNode` of an id in the
     members map is `ErrIDExists` (unless a promotion, which requires the member to be a learner,
     `ErrMemberNotLearner`), of a removed id `ErrIDRemoved`; a refused change is applied to raft as a no-op
     (`cc.NodeId = raft.None`, `server.go:2047`). `PromoteMember` only clears `IsLearner`. `UpdateNode` sets the
     member's `RaftAttributes` from `MemberUpdate`'s request, whose `IsLearner` is `false`
     (`v3rpc/member.go:81`). So an existing voter never becomes a learner.
   - A removed member is no learner either: `IsMemberExist` fails (and the fork's `IsLocalMemberLearner` returns
     `false` for it).
   - A member catching up by snapshot takes the leader's membership, reached by the same validated changes.
   - Restarts are outside `Serve_dist` (first incarnation, its docstring); a restart replays the same history.
   No premise was added: the voter fact follows from what the premises already fix (`memberUpL` from
   `NewServer` under `bootCfgFresh`). The model does not yet carry it (`IsLearner.spec` returns any boolean;
   `ccLogOk` does not exclude a re-add): S2's proof of `grpcRunNRMd` for etcd's chain needs a voter fact in the
   server's invariants, as `etcd_noRefusal`'s docstring already says.
3. **The balancer strings** occur only in the client (`client/v3/retry.go:93`), in neither the server nor grpc
   v1.84 (`notes/grpc-nr-e.md`).
4. **grpc's own errors** on the run: `dec`'s (`grpcDecOk`'s new `notDescIn refusalDescs` arm, E), and grpc's
   server-side statuses (unknown method, transport), all with grpc's messages. Other etcd errors on a KV call
   (`ErrGRPCNotCapable`, `ErrGRPCNoLeader`, `ErrGRPCNoSpace`, mvcc's `ErrCompacted`/`ErrFutureRev`, the default
   `err.Error()`) are none of the six strings.

The same argument underlies the deleted `KV_Put_dist`'s at-most-once claim; it now sits in `Serve_dist`, the one
server of the entries, instead of in each client contract.

### Who else can serve the defined entries (review item)

`etcdSvc` is now a definition, so any program can name the table. Serving it at an address needs that address's
`grpcAddrAt a (etcdSvc Γ mid)` (`etcdAddr_set`, spending `addrUnset`, or `net.Listen`'s `netAddrLeft`), and
`grpc.Server.Serve` then demands `grpcServesEnt` for every name it registers: a flagged KV entry needs a handler
that meets the view spec (the caller's atomic update at `Γ.kv`, the reply's facts) and never refuses; a name of
`etcdSvcRest` can only be left unregistered (`Unimplemented`). So a non-member at another address could serve
the KV entries only with handlers that are as correct as a member's (forwarding to a member, or failing every
call with a non-refusal error). The remaining dist axioms read the table only through `etcdSvcRest`'s entries,
which such a server answers with `Unimplemented`: their error arms. This is the coordinator's review item (i); the
independent axiom review is still to run.

## Build and gates

See the final report of the session (VM build, `etc/gates.sh`).
