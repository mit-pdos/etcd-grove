# Review: the closed lease example's draft specs (branch `lease-ex`)

Reviewed: `540183c3d0` (Draft), plus `2d9639135a` (Test: only the docstring of
`EtcdServer.leaseTimeToLive.spec` changed, and `examples/leasekv/leasekv_cluster_test.go` added).
Read-only review: no `lake`, no `etc/lean-check.py`, so nothing marked "provable" here was checked
by Lean. Go sources: the pinned etcd fork `ab3c28d9a` (`.lake/goose/etcd`), grpc-go v1.84.0
(`~/go/pkg/mod`). Judged by `.claude/skills/spec/PRINCIPLES.md` and the examples `lease-grpc.md`,
`lease-keepalive.md`, `watch-auth.md` and `reply-size.md`.

**Summary.** I found no false statement. Every new trusted claim checks out against the Go code:
D3's `⌜w.ID' = v.ID'⌝` on both paths, the restated cluster assumption, and F4's per-run
`threadTok`. The client specs are faithful copies of `lessor.Grant`'s shape and are sufficient for
`Main`. Most findings are about `kv_lease_served` and the shared example aggregates. The statement
can be proved, but it needs lemmas that do not exist yet. It repeats `kv_served`'s stock premises,
and it was added by putting a new clause into aggregates that every example destructures by
position. The strengthened axioms are not yet listed with the collections that rest on them.

Ranked by need of revision: **4 (served/example) > 3 (trusted) > 1 (wire) > 2 (client specs)**.

---

## Target 1: the wire models and served specs (`client/v3/InvLeaseRead.lean`)

**Good.** The models match `InvLease.lean`'s grant models field for field (`leaseTTLRespMsg` beside
`leaseGrantRespMsg`, and the `CallOut`s are identical in shape). `LeaseLeasesRespM.ids` is exactly
what the client reads (`lease.go:266-268`, `resp.Leases[i].ID`). The not-modelled `Keys` contents
are documented and point to the existing issue. The two `GrpcSpec`s are the weakest facts `Main`
needs and are implementation-independent: a single in-memory server meets them. They take no
`EtcdModel`, so no server vocabulary leaks to the client. `leaseOptSpec`/`leaseOptsAt` follow
`optSpec`/`optsAt`. A nil option is excluded, because `leaseOptSpec` of a nil func cannot be
proved.

Findings, most severe first:

1. **Missing law (law coverage).** `etcd_leaseLeasesHandlerOk` has to get `m.ids.Nodup` from
   `lease.leaseIdsAt γl i ids` (`leaseLeasesOut`, `v3rpc/InvLeaseRead.lean:162`). `Nodup` sits
   inside the definition (`lease/InvLessor.lean:416`), and no law exports it (`grep "theorem
   leaseIdsAt"`: none). The client-package proof would therefore unfold another package's
   definition. *Fix:* add `lease.leaseIdsAt_nodup : leaseIdsAt γl i ids ⊢ ⌜ids.Nodup⌝` next to the
   definition.
2. **Trusted request model broader than grant's (low).** `pbLeaseTimeToLiveRequest.recv` is the
   whole struct read-only (`r ↦□ v`, line 104). Grant's is two field points-tos
   (`InvLease.lean:100`). The whole-struct form also claims that protobuf's internal fields
   (`state`, `sizeCache`, `unknownFields`) are never written after decode. I checked that this
   holds today: etcd's log interceptor calls `proto.Size(req)` only for the KV types
   (`interceptor.go:111-175`, the `default` arm for leases), and neither the handler nor
   `leaseTimeToLive` marshals `r` (the follower builds a new request, `http.go:229`). The form is
   needed because `LeaseServer.LeaseTimeToLive.spec` takes `r ↦{dq} v`. *Fix:* keep it, but say in
   the docstring that the claim covers the internal fields and why that is true (no `proto.Size` or
   `Marshal` of a lease request on the server).
3. **Margin to state (vocabulary).** Unlike `etcdLeaseGrantSpec`, `etcdLeaseTTLSpec` says nothing
   of the header revision, `TTL` or `GrantedTTL`, and `etcdLeaseLeasesSpec` says nothing of which
   leases are listed. That is right for this example. Several specs of one method may be
   registered, so a later stage can add a stronger spec without changing these two. *Fix:* one
   sentence in each docstring: "the weakest spec `leasekv` needs; the server's answer (`leaseTTLOut`,
   `leaseLeasesOut`) gives more".

## Target 2: the client specs

**Good.** `lessor.TimeToLive`, `lessor.Leases`, the retry wrappers and the stubs are `Grant`'s specs
with the message types swapped. A diff against `leaseClient__LeaseGrant.lean` and
`_Lease_LeaseGrant_Handler.lean` shows only the model and the request tuple changing. Each spec is
faithful to the Go code:
- `toLeaseTimeToLiveRequest` (`op.go:604-608`): the post is the zero request with `ID'` and
  `Keys'`, so `unknownFields' = nil`, which the retry spec needs.
- `applyOpts` (`op.go:593-597`): `leaseKeysFold` is the in-order fold.
- `Leases` (`lease.go:262-272`): the slice is fresh and owned, one `LeaseStatus.mk` per id, and
  `LeaseStatus` has only `ID'` (`Code/.../client/v3/chunk0.lean:11849`).
- `TimeToLive` (`lease.go:246-260`): `ID`, `TTL`, `GrantedTTL` and `Keys` are copied from the
  reply.

Every premise `Main` needs has a source:
- `lessorRemoteAt` comes from `isNewClient`'s `lessorAt`.
- `isGrpcRpcs [addr]` comes from `isGrpcRpcs_singleton`.
- `leaseOptsAt slice.nil []` covers the variadic nil.
- `□ ▷ etcdLeaseTTLSpec (7, false) (fun m => ⌜m.id = 7⌝)` holds trivially.

Findings:

1. **The margin is not stated (low; "Know the margin").** The `TimeToLive` post makes the result's
   fields persistent (`↦□`), but Go gives an owned fresh struct (`lease.go:252`). The `Keys` slice
   has no contents. Grant does the same, so this is a consistent choice. *Fix:* add "(the struct
   is fresh and owned in Go; given read-only)" to the docstring.
2. **Copied provenance lines (vocabulary).** These headers say "item 1, the client lease"
   (copied):
   - `Spec/.../client/v3/retryLeaseClient__LeaseTimeToLive.lean:2-3`
   - `retryLeaseClient__LeaseLeases.lean:2-3`
   - `Spec/.../etcdserverpb/LeaseTimeToLiveResponse__GetHeader.lean`
   - `LeaseLeasesResponse__GetHeader.lean`

   *Fix:* "the closed lease example".

## Target 3: the trusted or frozen changes

**D3, `⌜w.ID' = v.ID'⌝`** (`Spec/.../EtcdServer__leaseTimeToLive.lean:66`; `LeaseTimeToLive`,
`ttlAns`, `leaseTTLOut`). **True.**
- Leader: `ID: r.ID` (`v3_server.go:650`), and `r` is read-only under `r ↦{dq} v`.
- Follower: `TimeToLiveHTTP` is called with `lease.LeaseID(r.ID)` (`v3_server.go:682`). It returns
  `lresp` only if `lresp.LeaseTimeToLiveResponse.ID == int64(id)` (`http.go:274`, which the
  docstring cites correctly). `leaseTimeToLive` then returns that same pointer (`:684`).
- The handler's not-found reply has `ID: rr.ID` (`v3rpc/lease.go:70`).

`leaseTTLOut` puts the conjunct at the top level, so it covers both arms. That is right.

**The restated cluster assumption (`2d9639135a`).** **Accurate.** `examples/common/common.go:146`
serves `s.RaftHandler()`, which is rafthttp's `ServeMux` with only `/raft*` and the probing prefix
(`rafthttp/transport.go:158-167`), so `/leases/internal` gets a 404. `TimeToLiveHTTP` maps 404 to
`lease.ErrLeaseNotFound` (`http.go:262-264`), which is among the triple's `applyErrIs` errors. The
handler then answers TTL `-1` with the asked ID, so D3 and `Main`'s check are unaffected. The new
wording ("200 only with a `LeaseTimeToLiveResponse` and its header set") is exactly what the triple
needs: a 200 without the response is the nil dereference at `http.go:274`; a 200 with a bad body or
a mismatched ID is an error.

The cluster test does what its docstring says: a peer mux with the raft and lease handlers, as
embed does, both paths exercised and the check enforced. It computes `leader` once per member, so
a leader change during the loop would only mislabel the per-path counts, not the checks.

**`grpc.serve` restated (F4)** (`Proof/google_golang_org/grpc/InvGrpc.lean:805-810`). **True of
grpc-go.**
- `serveStreams` runs each stream's `handleStream`, which runs the handler, on `go f()`
  (`server.go:1107`). With `NumServerWorkers` it runs on a worker goroutine instead, which runs one
  `f` at a time (`:1099-1101`); etcd does not set the option.
- In either case the run occupies one goroutine for its whole duration. A translated grpc would
  give that goroutine its token through `wp_fork_tok` (Perennial `Lifting.lean:1806`), and a fork
  at zero fuel stutters, which is consistent with a partial-correctness `grpcServes`.
- `grpc_serve_rpcs` keeps its statement through `grpcMethodsOkMd_frame`, so existing callers are
  untouched. I found no other direct user of `grpc.serve`.
- *Uncertain:* the model behind the examples' adequacy treats grpc's server as an axiom. Whether
  `state.threads` in `leasekv_safe` counts grpc's goroutines is a question about how that model
  interprets `grpc.serve`/`Invoke`. I could not verify it. Today the axiom mints a token per run
  that no fuel accounts for in the logic. That is harmless while runs are bounded by the slots,
  but say it in the axiom's docstring.

Findings:

1. **The axioms are strengthened in place, but no collections are listed (process; hard rule,
   "strengthen the axioms in place, list for each the collections ... and put it to the user").**
   `etc/tcb-report.py --check` does not flag a same-name change. Collections that now rest on the
   stronger claims, by `grep` of `etc/tcb-collections`:
   - `EtcdServer.leaseTimeToLive.wp_proof`: `server.txt`.
   - `grpc.serve`: `authkv`, `cache-client`, `cachekv`, `client`, `compactkv`, `k8setcd3`,
     `lease-served`, `linkv3p`, `linkvtxn`, `m2`, `putget`, `putget3`, `slice`, `v3rpc`,
     `watchkv` (16 in all).

   *Fix:* put both lists in the plan's Freeze section, and add `etc/tcb-collections/leasekv.txt`
   (as `putget.txt`) for the new root.
2. **A stale docstring (low).** `Spec/.../v3rpc/LeaseServer__LeaseTimeToLive.lean:30-39` still
   describes `leaseTTLOut` without the new ID fact. *Fix:* "...the response, about the asked lease
   (`ID`), with its header filled...".

## Target 4: the served meets and the example's statements

**Good.**
- `etcd_leaseTTLHandlerOk`/`etcd_leaseLeasesHandlerOk` follow directly from the proved
  `LeaseServer.LeaseTimeToLive`/`LeaseLeases` specs. Those specs take exactly `leaseServerAt`,
  `raftLeaseRead s E γl S A.revR`, `S ∗ A.revR` and the two lower bounds, and the wire `recv`
  supplies `r ↦□ v`.
- `leaseTTLOut`'s owned `resp ↦ w` and `leaseHdrDone` persist into `leaseTTLRespMsg`.
- The not-found Leases arm (`↦* []`) gives `Nodup []`.
- The method meets are `etcd_leaseGrantMethodOk` again.
- The `quotaLeaseServer` promotions are proved.
- `Main.spec` is putget's with only the address changed, and the closed theorem's "no panic" is
  exactly the two Go checks. The reads' error paths `return` in Go (`leasekv.go:52-71`).

Findings, most severe first:

1. **`kv_lease_served` can be proved, but not from what exists (unprovable as things stand).**
   `ServedLease.lean:43-60`.
   - (a) **One `grpc.serve` for every method, so one slot `S`.** The KV methods are served inside
     `etcd_kv_started` (`client/v3/Results.lean:2883`), which calls `grpc.serve` itself. The lease
     reads cannot be added by a second call, because `grpcServerAt` is exclusive. Prove needs
     `etcd_kv_started` generalized over extra methods (the plan says so). It also needs a
     method-level slot lemma: a `grpcMethodOkMd_slot` that rearranges `etcdGrpcSlot ∗ threadTok`
     into the lease methods' `(S_h ∗ F) ∗ [∗list] etcdIcRs`. Only the handler-level
     `grpcHandlerOk_slot` and the right-frame `grpcMethodOkMd_frame` exist.
   - (b) **The auth fact under `HEo : E.authOn = false`.** `raftLeaseRead_server` takes
     `srvAuthLeaseLb s E` (`v3rpc/Results.lean:1734-1740`). Its only source,
     `srvAuthLeaseLb_of_server` (`etcdserver/LeaseSrc.lean:102`), needs `E.authMode = .off ∨ on`
     and `srvAuthLb s E`. `authOn = false` also allows `.any` (`auth/Model.lean:359-365`), and
     `memberUp` gives only `E.authOn = false` (`envAgree` says nothing of the mode; `common/Defs.lean`
     line 277). `srvAuthLb` is not among the premises. *Fix:* prove `srvAuthLeaseLb` for every mode
     that is not on, from `isServerReadM false` (all of `.any`'s verdicts are `True`,
     `auth/Fresh.lean:58-62`, `Buckets.lean:274`). Alternatively, make `memberBuilt`/`memberUp`
     export `E.authMode = .off`, if `NewServer` gives it.
   - (c) `lease.lessorLb E.γ.leases 0` has to come from `lessorInv`'s `lessorRdInv` through
     `lessorLb_get` and `lessorLb_le`. That works, but it unfolds `srvLessorRd` and `lessorInv`.
     *Fix:* a law `srvLessorRd s γl ⊢ |={⊤}=> lessorLb γl 0` in the lease or etcdserver package.
2. **An unneeded premise.** `HEo` follows from `isServerReq s E ρ`, which contains
   `⌜E.authOn = false⌝` (`InvProposer.lean:454-455`). *Fix:* drop it.
3. **Locality and caller burden: the shared aggregates gain a clause per stage** (hard rule
   "Local": "the boot contract accreted a clause per stage").
   - `memberBuilt`, `memberUp` and `grpcUp` gained `srvLeaseRd`/`grpcLeaseUp`
     (`common/Defs.lean`).
   - Every example's `Main` that destructures them by position had to change: putget, putget3,
     putgetc, watchkv, compactkv, cachekv, k8setcd3, linkvtxn and linkv3p (`git diff lean...HEAD`,
     e.g. `putget/Main.lean:124`, `watchkv/Main.lean:208,225`).
   - Only `leasekv` uses the new clause.

   *Fix:* either keep these facts outside the aggregates (persistent exports beside them), or give
   the aggregates projection laws (`memberUp_leaseRd`, `grpcUp_leaseUp`) and change the examples to
   use those laws instead of positional `icases`. The latter is what "A client does not unfold the
   spec's definitions" asks for in any case.
4. **Bounds (preference, gate).** `kv_lease_served` repeats `kv_served`'s six `List.replicate`
   stocks (the plan's count: 23 → 29) and adds a new `threadBound GF ≤ 2 ^ 30 - 1`, which comes
   from the trust-boundary `leaseTimeToLive`'s premise. *Fix (better at Draft than at Prove,
   because the statement is what Freeze approves):* state the two as one theorem.
   `kv_served_with ms` takes the extra methods' `grpcMethodOkMd … iprop(etcdGrpcSlot ∗ threadTok)`
   and puts the stocks in one definition. `kv_served` (`ms = []`) and the lease form are its
   corollaries. That is the "one proof, variants as corollaries" rule, and it restores the count.
5. **Copies (size, low).** `leasekv/{Defs,Adequacy,Base}.lean` are putget's with renames, and
   `heapAtLkv` is putget's `heapAt` under a different name. That follows the examples' precedent,
   but the rename only avoids a clash. Prefer one shared `heapAt` in `examples/common` if both
   modules can import it.
6. **Margin of the closed theorem (state it).** With one member and no grants, every real run of
   `Main` takes the leader's not-found path. The theorem still covers the found and follower arms,
   because the specs are state-independent, but the Go test exercises those arms only in
   `leasekv_cluster_test.go`, not in `Main`. *Fix:* one sentence in `leasekv/Results.lean`'s
   header.

## Bugs in the Go code

None new in etcd. The examples' peer listeners serve only the raft handler
(`examples/common/common.go:146`), unlike embed's `etcdhttp.NewPeerHandler`. A follower's
`TimeToLive` in an examples cluster therefore answers "not found" for a lease that exists. That is
a deviation in this repository's examples, not an etcd bug. It is recorded in the plan and in the
axiom's docstring, so it needs no `issues/` file. If the examples are meant to behave like
production etcd, `notes/` should say so, or `NewMember` should serve the lease handler too.
