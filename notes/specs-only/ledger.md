# The spec plan's change ledger

A spec defect that a proof (or a review, a test, a user's critique) finds in a spec of the spec plan
(`SpecPlan/Spec/`), or a divergence between a real spec (`Spec/`) and the plan's, is recorded here
**before** either spec is edited (CLAUDE.md, "The spec plan and convergence"). The ledger is how the
plan stays the target the real proofs converge toward: no silent edits.

One entry per defect, newest first, in this format:

```
## <date>: <spec> -- <one-line defect>

- **Spec.** The file and the declaration (`SpecPlan/Spec/<pkg>/<fn>.lean`, `<fn>.spec`; or a law,
  `<pred>_<law>.spec`), and the real spec it corresponds to (`Spec/<pkg>/<fn>.lean`), if any.
- **Defect.** What is wrong: unprovable (false of the Go code), too weak for a user, too strong (a
  premise no caller can meet), not local, vacuous, ...
- **Evidence.** What shows it: the proof step that fails (file:line, the goal), the Go path (a
  panic, an error the post omits), the user or snippet (`examples/specreq/<alias>/`) it breaks, a
  failing test.
- **Proposed change.** The new statement (or its delta), and what else it moves: the snippets, the
  callers' and callees' specs and proof sketches, the open questions it touches.
- **Decision.** Pending / accepted (by whom, date; the commit that applied it) / rejected (why).
```

A change that needs the user's approval (a spec's statement at the client boundary, new
client-visible ghost state, a trust-boundary spec) says so in **Decision** and waits for it.

## 2026-11-15: `applyAll.spec` (proof sketch) -- the merge's guard is no longer only `m.term = raftTerm`, `index ≤ appliedi`: the verified fork defers a merge inside the replay window

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`, `applyAll.spec`
  (its proof sketch and "Changes" paragraph; the statement is unchanged); the real spec
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`, `applyAll.specBatch`.
- **Defect.** The sketch describes the merge's select at the pin as "the code's" guard (`m.term = raftTerm`,
  `index ≤ appliedi`, then `createMergedSnapshotMessage`/`sendMergedSnap`). The verified Go code changed
  (restart3 A1, route (A) via A-g, approved by the user 2026-11-15): the goose fork's commit `6e8f0c004`
  adds a third test, `ep.appliedi < s.consistIndex.ConsistentIndex()` (inside the replay window) under
  which the merge is replaced by `s.ReportSnapshot(m.GetTo(), raft.SnapshotFailure)`, and reports a
  message dropped by the term or index guard failed too (D-A0-6). The sketch's callees miss
  `consistentIndex.ConsistentIndex`, `raftpb.Message.GetTo` and `ReportSnapshot`.
- **Evidence.** `notes/restart3-a0-draft.md` §3 and §8 (the change, the Go runs: the guard fires and the run
  stays correct; unreported drops wedge a follower); the real proof `applyAll.wp_proofBatch`
  (`Proof/.../EtcdServer__applyAll.lean`, `wp_ci_get` for the guard's read, `ReportSnapshot` on each drop).
  The plan's statement already had no window premise, so it needs no change; the real spec's window row
  (`winNoMergedSendR … ∗ T ∗ srvSnapBagN`) is deleted, converging toward the plan.
- **Proposed change.** The sketch's merge paragraph and "Changes" paragraph name the window test, the
  `ReportSnapshot` on a deferred or dropped `MsgSnap`, and the three callees. Statement unchanged.
- **Decision.** Accepted (decided by etcd-grove-81 with the A-g route, 2026-11-15; text only; the restart3 A1
  commit that applies it).

## 2026-11-14: `leaseCheckFrom` (the lease checks' and lease methods' posts) -- admits the empty user unbound

- **Spec.** `Proof/go_etcd_io/etcd/server/v3/etcdserver/LeaseCheck.lean`, `leaseCheckFrom` (the lease-keys
  plan's Part B vocabulary, frozen 2026-10-31), in the posts of `EtcdServer.checkLease{Renew,Leases,TimeToLive}.spec`
  and `EtcdServer.Lease{Leases,Renew,TimeToLive}.spec`; its stream form `v3rpc.leaseCheckT`
  (`api/v3rpc/InvLeaseKeepAlive.lean`, through `infoBoundTM`), in the keep-alive stream's `kaDn`. The spec plan's
  `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkLeaseRenew.lean` (and the other two) state
  nothing of the principal on success: no plan change.
- **Defect.** Too weak. With auth on, the principal is named through `infoBoundM` (`ReqOn.lean`), whose first
  disjunct admits `info.Username' = ""` unbound to the context; for an absent or keyless lease, where the keys'
  verdict `K info` holds trivially, a proof may pick the empty user, so the post does not say "authenticated".
- **Evidence.** The code refuses it: `checkLeaseRenew`, `checkLeaseTimeToLive`, `checkLeaseLeases` return
  `auth.ErrUserEmpty` for a `nil` auth info (`v3_server.go:585, 617, 764` at the pin `2eaeb872bc`); the Scope's
  E2 (`notes/auth-lease-scope/zz_authlease_rows_test.go`) shows it on every lease method, keyless leases included.
  The three check proofs already establish the stronger disjunct (`infoBoundM_of_ctxBound`'s last step,
  `principalBound_of_ctxBoundOrTLS`).
- **Proposed change.** `leaseCheckFrom`'s principal: `□ (⌜E.authOn = true⌝ → principalBound s E.authMode ctx
  (some info))` in place of `infoBoundM E.authOn s E ctx info`; `leaseCheckT`'s: `□ (⌜E.authOn = true⌝ →
  principalBoundT s E.authMode tok info)` (new, `principalBound` over the token) in place of `infoBoundTM`
  (deleted). The TLS fallback (`srvTLSId`) stays admitted: its common name may be empty (E8). No other
  statement text changes; the proofs of the three checks, `leaseCheckFrom_mono`, `leaseCheckFrom_ctx` and
  `leaseCheckT_of_from` are repaired.
- **Decision.** Accepted (Q3 and the CP0 decision, etcd-grove-81, 2026-11-14; branch `auth-lease`, S1).

## 2026-11-14: the mode-`on` KV model (`kvEntryOn`) -- a refused revocation would be applied once the model has leases

- **Spec.** `Proof/go_etcd_io/etcd/server/v3/etcdserver/KVAuthModel.lean`, `kvEntryOn`'s refusal guard
  `apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq`; the auth-lease Scope's Draft
  (`notes/auth-lease-scope.md` §2.3), which replaces `kvGranted` by `kvGrantedL` with a `.leaseRevoke` case.
- **Defect.** Wrong once the auth-on model admits revocations (S3): `isKVKind` excludes `.leaseRevoke`, so the
  Draft's revocation case of `leaseGrantedM` is never consulted and a revocation the auth layer refuses
  (`authApplierV3.LeaseRevoke`'s `checkLeasePuts`, `apply/auth.go:191-196`) would delete the lease's keys in
  the model. Today harmless (the mode-`on` log has no lease request, `plainEntryOn`).
- **Evidence.** The S0 probe (`Scratch/AuthLeaseProbeModel.lean` of the `auth-lease` worktree); `apply.authChecks`
  (`apply/Chain.lean:153`) includes `.leaseRevoke`, `isKVKind` (`apply/InvRequest.lean:299`) does not.
- **Proposed change.** The guard over `authKVKind k := isKVKind k || k == .leaseRevoke`, in S2's Draft of the
  triple-state model (`kvEntryOnL`).
- **Decision.** Accepted (CP0 item 3, etcd-grove-81, 2026-11-14); applied in S2's Draft.

## 2026-11-14: `Http` headers -- Go rewrites header values, adds request headers, decompresses gzip

- **Spec.** `SpecPlan/Spec/net/http/Api.lean`: `hdrView` (the client's view of committed response
  headers), `srvReq r R rd` (the handler's view of the request's headers), the response writer's
  `Flush`; the real boundary's `srvView`, `reqAt`, `hdrsReady`, `Flush_spec` (`Proof/net/http/`).
- **Defect.** Unsound: Go's server turns CR/LF in a response header value into spaces, its client
  trims values and drops non-token keys, and decompresses a body whose handler set
  `Content-Encoding: gzip`; the handler sees `Accept-Encoding`, `User-Agent`, `Content-Length` the
  client never set, and trimmed values; `Flush` on an uncommitted writer commits `200`.
- **Evidence.** The independent review of `http-boundary-fix` (etcd-grove-81, 2026-11-14);
  `examples/premisefix/{httpgzip,httphdr,httpreqhdr}`.
- **Proposed change.** As the real boundary on `http-boundary-fix`: committed response headers
  `respHdrsOk` (token keys, `hdrValOk` values, none of `respNoKeys`); the handler's request headers
  `reqHdrView R.hdr hs` (trimmed, but at `reqTpKeys`); `Flush` of a committed writer.
- **Decision.** Pending (trust-boundary specs of the plan).

## 2026-11-14: `Http.roundTripperOk` -- a response's status may be the server's own, not a handler's

- **Spec.** `SpecPlan/Spec/net/http/Api.lean`, `roundTripperOk` (and the header's "The response's
  status and headers are the handler's"), `reserve.spec`; the real spec `http.roundTripperOk`,
  `http.reserve` (`Proof/net/http/`).
- **Defect.** Unsound: `RoundTrip`'s post gives `respPre P R τ st hs` of a status that may be one
  Go's server answered with itself, running no handler (`400`, `417`, `431`, `501`, `505`), which no
  premise puts in `P.resp`. (The plan's tickets already follow `onceOnly`, the real boundary's other
  finding of the same review.)
- **Evidence.** The network fault review (etcd-grove-81, 2026-11-14);
  `examples/premisefix/httpsrvstatus`.
- **Proposed change.** As the real boundary on `http-boundary-fix`: `reserve` asks of the protocol
  family that each member admits those statuses at any headers/bytes (`Proto.srvOk`, with
  `srvStatuses`), or the post splits handler and server answers.
- **Decision.** Pending (a trust-boundary spec of the plan; the real one fixed on
  `http-boundary-fix`, awaiting review).

## 2026-11-12: `Bucket.node.spec`, `Cursor.node.spec` (internal) -- no panic promised on a deleted handle

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__node.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Cursor__node.lean`
  (internal); no real spec.
- **Defect.** Unsound: `Bucket.node` begins with `common.Assert(b.nodes != nil, ...)`
  (`bucket.go:867`), and `DeleteBucket` sets `child.nodes = nil` on the handle it deletes (`:321`).
  A deleted handle keeps its persistent `bktH` (and its cursors their `boltCur`), so the pre
  `wtxCore ∗ bktH b p` holds where Go panics; `Cursor.node` calls `c.bucket.node(...)` when the
  stack has no leaf node, with its currency `C.bkts b = some p` only as a hypothesis of its post.
- **Evidence.** The 2026-11-12 review of the bucket-handle change (`9fb353a5d1`), finding 1. No
  public triple is affected: each supplies `bktUse`, from which `wtxCore_bktOwn` gives the currency.
- **Proposed change.** `⌜C.bkts b = some p⌝` a premise of both (the cache holds the handle, so it
  is not a deleted one: `DeleteBucket` drops it from `bkts` before clearing its `nodes`); both posts
  keep `C'.bkts = C.bkts` (materializing nodes touches no bucket cache), so a caller's later calls
  keep it. Callers: `Put`, `Delete`, `CreateBucket*`, `Cursor.Delete`, `DeleteBucket` (its `seek`
  on the parent), `SetSequence`/`NextSequence` get it from their `bktUse` by `wtxCore_bktOwn`;
  `node.childAt` from a cached node's bucket; `spill`/`rebalance` walk the cached handles
  (`b.buckets`, `bucket.go:860`).
- **Decision.** Accepted by the coordinator, 2026-11-12. Applied in `c1297a6c6d`.

## 2026-11-12: bbolt's bucket handles -- a generation counter in the view is unobservable, redundant state

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`TxView.gen`, `TxView.gens`, `TxView.dropBkt`), `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean`
  (`bktH tx γ b p gs`, `boltCur … gs …`, `bktH_live`), and every triple taking a handle (`Tx.Bucket`,
  `Tx.CreateBucket(IfNotExists)`, `Tx.DeleteBucket`, `Tx.Cursor`, `Tx.ForEach`, `Bucket.*`,
  `Cursor.*`). Real spec: `Spec/go_etcd_io/bbolt/Api.lean` (`boltBkt tx b n g`, the same counter).
- **Defect.** A handle is valid while the per-path counters `T.gens p` equal those it was made at;
  `DeleteBucket` bumps them. No operation lets the client observe the counter: it is state in the
  client's view that exists only to invalidate stale handles, which ownership already does (using
  a bucket takes its token, deleting it consumes the token). The user, 2026-11-12: "it was
  unobservable state. It introduced a redundancy in the specs which we found was not necessary by
  instead using ownership."
- **Evidence.** What the counter excludes is real (`nonissues/bbolt-deleted-bucket-handle.md`: a
  handle used after delete and re-creation panics in `Put`), and Go has a field that says which
  handle is current: in a write transaction `Tx.Bucket`/`Bucket.Bucket` return the parent's cached
  `*Bucket` (`bucket.go:89-110`), `DeleteBucket` removes the cache entry (`bucket.go:318`),
  `CreateBucket` returns a newly allocated one (`bucket.go`, `return b.Bucket(newKey)`;
  `newBucket`, `:116`). A read transaction has no cache (`bucket.go:50`) and cannot delete.
- **Proposed change.** Write transactions: ownership of buckets, `bktOwn tx γ p o q` (fractional;
  `o : Option Loc` the parent's cache entry for `p`), the only handle predicate of a writer.
  `Begin(true)` gives `bktOwn tx γ p none 1` for every bucket path of the data; a lookup turns `o`
  into `some b` (fraction 1 to fill the cache), `CreateBucket` gives `bktOwn … (some b') 1`,
  `DeleteBucket` consumes the full tokens of the deleted bucket and every bucket below it. Read
  transactions: a persistent `bktH tx γ b p` without generations. One handle premise by cases
  (`bktUse`), so each function keeps one triple. `TxView.gen`/`gens` removed; `bktH_live` restated
  over `bktUse`. Moves no spec above bbolt (none names a handle); the real proved bbolt converges
  to it later.
- **Decision.** Accepted by the user, 2026-11-12 ("I want the ownership version"); read
  transactions keep a persistent handle (the coordinator's proposal: no Go operation can
  invalidate one, and etcd's shared read transaction caches handles across goroutines,
  `read_tx.go:49, 97-104`). Applied in `9fb353a5d1` (with the departures recorded there: `Tx`,
  `Writable`, `Cursor` and `openBucket` take only the persistent `bktH`, which they need alone and
  `bktOwn_bktH` gives from a token; the root's handle, in both kinds, is the persistent `bktH`, which
  `Tx.Cursor` returns; every cursor move, `Next`/`Prev`/`Delete` included, takes the handle premise,
  since without generations a deleted and re-created bucket can leave the view as it was; the
  lookup token is `bktTok`; the data's bucket paths `Ent.bktPaths`, `Ent.bktsUnder`).

## 2026-11-12: `Tx.DeleteBucket.spec`, `Bucket.DeleteBucket.spec` -- the empty name's error arm is false after the first leaf is emptied

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Bucket__DeleteBucket.lean`; real spec
  `Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean` (D-M: either error, true).
- **Defect.** Unsound: `ErrIncompatibleValue` only when `kb = [] ∧ T.ents p = []`, else
  `ErrBucketNotFound`.
- **Evidence.** `c.seek("")` descends to the first leaf; a leaf node emptied by the transaction's
  deletes gives a nil key, `bytes.Equal([]byte{}, nil)`, flags 0: `ErrIncompatibleValue`
  (`bucket.go:296-305`) with buckets left. Test:
  `nonissues/bbolt-deletebucket-empty-name/emptied_leaf_test.go` (2000 buckets, first 50 deleted:
  `incompatible value`).
- **Proposed change.** For `kb = []`: either error, the transaction unchanged (the frozen spec's
  arm). No caller passes the empty name.
- **Decision.** Accepted (coordinator, 2026-11-12; a sound repair to the real spec's form).
  Applied in `9fb353a5d1` (the `kb = []` arm before the lookup: either error, the transaction
  unchanged).

## 2026-11-12: `Model.lean` -- no laws over the data model

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Model.lean` (`Ent.setKey`, `modAt`, `atPath`, `curEnts`, `bktAt`).
- **Defect.** Too weak for users: nothing states lookup after a put or delete, the cursor order
  after a put, or what `modAt` leaves at other paths; each client (the backend's range and
  compaction proofs) would re-derive them.
- **Evidence.** The 2026-11-12 strength review (etcd's server path); `examples/specreq/bbolt/
  backend.go`'s range-after-put in `ReqBackendBatch`.
- **Proposed change.** Pure laws as `def … .spec : Prop` in `Model.lean`: `atPath` after `modAt`
  (same path, other paths), `setKey` then lookup, `curEnts` of `setKey` (sorted insertion/removal),
  `wf` preserved by `setKey`/`modAt` under the entry bounds.
- **Decision.** Accepted (coordinator, 2026-11-12; adds laws, changes no triple). Applied in
  `b899a66c70` (`Ent.atPath_modAt`, `atPath_modAt_other`, `lookup_setKey`, `atPath_child_setKey`,
  `curEnts_put`, `curEnts_del`, `wf_setKey`, `wf_delKey`, `wf_modAt`, `bktPaths_mem`,
  `bktsUnder_mem`). The review of 2026-11-12 (finding 3): how `bktPaths` changes, so the backend's
  lock invariant can rebuild its token list (`Ent.bktPaths_create`, `bktPaths_dropBkt` up to
  `List.Perm`, `bktPaths_setVal`, `bktPaths_setSeq` equal), applied in `e6c84e32fd`.

## 2026-11-12: `DB.Path.spec` (and the close right) -- `Path` needs the exclusive close right, which non-blocking defrag does not hold

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/DB__Path.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`boltOpened db γ`, exclusive), `DB.Sync.spec`,
  `DB.Close.spec`.
- **Defect.** Too strong a premise: etcd's defrag calls `b.db.Path()` without the backend's lock
  (`backend.go:515, 712`), so it cannot hold the exclusive right. A share is enough: `Path` reads
  `db.path`, which only `close()` writes (`db.go:832` at the pin, `db.path = ""`).
- **Evidence.** The 2026-11-12 completeness review (etcd's server).
- **Proposed change.** `boltOpened db γ q` fractional; `Path` (and `Sync`, if its Go body only
  races with `close()`) take a share and return it; `Close` takes the whole. Exclusivity at 1.
- **Decision.** Accepted (coordinator, 2026-11-12; weakens a premise, no new ghost state).
  Applied in `9fb353a5d1` (`boltOpened db γ q`, used at `1`) and `6eae035a46` (`Path` and `Sync`
  take a share: `Sync`'s body, `Logger`, `db.path` and `fdatasync`'s `db.file`, races only with
  `close()`, `db.go:829, 832` at the pin).

## 2026-11-12: `Open.spec` -- written against bbolt `743299d`, the pin is `ea4cab5`

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`; the API's header (`743299d`).
- **Defect.** Out of date: at the pin a writable `Open` with `NoSync` off (`!db.NoSync ||
  IgnoreNoSync`) `fdatasync`s the file before any commit and, on its error, closes under the locks
  and returns it (`db.go:320-334`; `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`,
  blocks-proof: yes). The spec has neither the sync's effect on the durable state nor the error path.
- **Evidence.** `diff` of the two module versions: the only non-test change (`db.go`).
- **Proposed change.** `Open.spec` at `ea4cab5`: with `NoSync` off, the state `Open` read is durable
  (the post's state records it, as a successful sync does), the sync's error is an `Open` error
  (`boltClosed` back); the API header names the pin.
- **Decision.** Accepted (coordinator, 2026-11-12; follows the pinned code). Applied in
  `ac1de7621a`: with `NoSync` off (`IgnoreNoSync` is false on Linux) `Open` takes a sync update
  (`σ.sync ok`, as `DB.Sync.spec`'s), the success post gives `Ss true`, an error `Ss` of the outcome
  or the update back. With `NoFreelistSync` off too, the freelist commit's updates are nested in
  the sync update's `COMM` (a holder of one `boltState` builds both; the review's finding 2):
  applied in `dc5d1f1826`.

## 2026-11-12: `Open.spec`, `DB.Close.spec` -- their errors cannot be excluded, and the server panics on both

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Open.lean`, `SpecPlan/Spec/go_etcd_io/bbolt/DB__Close.lean`; the backend's `New`/`Close` specs.
- **Defect.** Too weak for the server: over OsFs every system call may fail; `newBackend` panics
  on an `Open` error (`backend.go:234-236`), `applySnapshot` on the old backend's `Close` error
  (`server.go:1149-1151`). The backend's opaque `dbOpenOk` is tied to nothing, so a proof closes
  only if it is `False`.
- **Evidence.** The 2026-11-12 completeness review; `req/go_etcd_io_bbolt.md` item 1.
- **Proposed change.** As the main tree (the user's decision for mvccrand, 2026-11-08): named
  environment premises `dbOpenOk`/`dbCloseOk`, with `Open`'s/`Close`'s error giving their negation
  (a trust-boundary layer over the proved specs); or an environment resource the call consumes.
- **Decision.** Pending: the user's (a trust-boundary statement).

## 2026-11-12: bbolt's file vocabulary -- no law for a file renamed over while open (snapshot install)

- **Spec.** `SpecPlan/Spec/go_etcd_io/bbolt/Api.lean` (`fileHolds`, `boltFile`, `boltRelease`, `boltCrash`).
- **Defect.** Incomplete: the snapshot install renames the new file onto the open database's path
  (`storage/backend.go:68`) and closes the old database later; bbolt names a file by its path, so
  its release and crash laws would hand out the path's resources, now the new file's.
- **Evidence.** The 2026-11-12 completeness review; recorded only as the generic missing OsFs
  `rename` (C42/C43).
- **Proposed change.** Name a database by its OsFs file, not its path, or a rename law moving the
  path's name to the new file while the old file's resources stay with `boltFile γ`. With OsFs's
  `rename`.
- **Decision.** Pending (needs OsFs's `rename`; the file extension's owner).

## 2026-11-12: `backend.Defrag.spec` -- no reader slot, yet defrag opens read transactions

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Defrag.lean` (or its
  file).
- **Defect.** Unprovable: defrag's read transactions (`backend.go:597, 812, 883, 963`) each need a
  `threadTok` for `Begin(false)`; the spec takes none (`Hash` takes one).
- **Evidence.** The 2026-11-12 completeness review.
- **Proposed change.** `Defrag.spec` takes a `threadTok` and gives it back, as `Hash`.
- **Decision.** Pending (a new premise on a spec with clients: the user's).

## 2026-11-12: the backend's realization -- bbolt's state in `mu`, though commits and non-blocking defrag run without it

- **Spec.** `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Api.lean:44` (realization
  note), `batchTx__commit.lean:4-5`, `Durable.lean:36-39`.
- **Defect.** The intended realization keeps `boltState` in the `mu` lock; batch commits and
  non-blocking defrag's `Begin` run without `mu`, and the crash law wants a share in a
  crash-surviving invariant, so the commit's update cannot be built as sketched.
- **Evidence.** The 2026-11-12 reviews (both).
- **Proposed change.** The realization keeps `boltState` in an invariant (the bank's pattern),
  the commit's update opening it.
- **Decision.** Pending (the backend's; no statement changes).

## 2026-11-15: the auth-on KV results at `kvStateOf log` -- unprovable once `kvInvOn` carries the lease table (auth-lease S3a)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Put.lean:63`,
  `EtcdServer__DeleteRange.lean:59` (`Q (kvStateOf x.log)`), `EtcdServer__Txn.lean`'s writing post (through
  `txnQhOn_res`), and the read side's conversion `client/v3/Results.lean:1052` (`readQ_of_ansM`: `kvStM true`
  is `kvStateOf (kvModelM true …)`, so a range's `□ Q (kvStateOf log)`), at `E.authOn = true`.
- **Defect.** S3a (Draft rev 5 §2, frozen) puts the lease table in `kvInvOn`'s state and keeps the clients'
  half in every lease mode, so a client's update fires at `kvStateOf (kvModelOn L) (kvLeasesOn L)`. These
  posts give `Q` of `kvStateOf x.log` (the table `[]`), true only while no lease is granted. The off mode
  proves its text by refuting a granting cluster from the client's half (`kvSt_client_lg`: `kvStQ` owns the
  whole variable at `γk.lg`), which S3a removes with auth on by design. Nothing on the request side
  (`isServerReqM true`, `putPermitM true`, `reqPropOkOn`) ties the mode to `none`.
- **Evidence.** The S3a port: `ReqOn.grantedRes_applied` (`kvRes γc Q (kvStateOf lb)` from `grantedRes` at
  `kvStateOf (kvModelOn L) (kvLeasesOn L)`), `ReadOn`'s `kvStOn` (must equal the invariant's state for the
  read deposits' firing, `ReadOn.lean:666`), `readQ_of_ansM`'s `by cases on <;> rfl`.
- **Proposed change.** (A) the posts give `Q` of the state with its table: `∃ lt, ⌜E.authOn = false → lt =
  []⌝ ∗ Q (kvStateOf x.log lt)` (or the model's table named through `modelOutM`), and the read side's
  `□ Q (kvStateOf log lt)`, followed through v3rpc (`ServerKVOn`) and the client's KV results; (C) a
  transitional tie of the auth-on request side to the lease mode `none` until S3b. Not in Draft rev 5 §7.
- **Decision.** (A), with the stronger guard `⌜E.authOn = false ∨ γ.kv.lm = .none → lt = []⌝` (etcd-grove-81, 2026-11-15): S3a Draft rev 6, §14 (recorded here 2026-11-15, S3a2 review r2 S7).

## 2026-11-15: the latest track's certificate premise for a leased put or transaction -- unprovable at a dead lease (auth-lease S3a §6)

- **Spec.** `apply.Apply.kvSpecL`, `apply.uberKVC`, `apply.uberApplier.Apply.kvSpecL`
  (`apply/ApplyFnKVL.lean:73,110`, `apply/ApplyKVL.lean:54`; exported as `apply_*_kv_latest`): the premise
  `certPreVW v3 E x.chain rq x.log (kvOutL …)`; through `certPreW_inner` (`apply/AuthApplyLatest.lean:238`, used by
  the latest Put/Txn/Revoke) it becomes the class track's `certPre E c rq log` (`apply/Chain.lean:1532`): a
  certificate `E.Nx` of the log after EVERY `chainStep backendStep` outcome.
- **Defect.** `backendStep`'s put case (`apply/Chain.lean:209`, kept unchanged by S3a's N1 (ii′)) admits
  `applied (log ++ [putChangeOf op …])` whatever the lease, and its transaction case an applied commit without
  `PathsLeaseOk`. The model (`backendLog`) keeps the log for a put of a lease not live (`leaseMissingIn`) and for a
  transaction whose path names one. With auth on, `E.Nx = kvNxOn` certifies only the models of committed raft logs,
  so the server cannot give the certificate of that outcome: Draft §6's KV branch ("as today, S2's latest triple
  ... no more `plainCover` discharge") is unprovable for an admitted leased put or leased transaction at the
  revocable mode, which a concurrent revocation makes reachable (a put proposed with a lease revoked before it
  applies). §3a's `leaseExactL` reaches the posts, not this premise. The backend's Put gets the certificate before
  its lease check (`applierV3backend__Put.lean:88-95`) and uses it only in the live branch.
- **Evidence.** `certPreW_inner`'s hypothesis `∀ oc, chainStep backendStep c rq log oc → X oc`; `kvNxOn`
  (`KVApplyOn.lean`); `kv_certPreW_on` (`ApplyEntryOn.lean`), which needs every admitted outcome to be the model's
  (`outcomeOn_of_kvOutLL` needs `leaseExactL` at the model's table, not available for the premise).
- **Proposed change.** (1) Restrict the class track's certificate to lease-exact outcomes at the live set `T`
  (`certPre` -> `certPreT … T`, outcomes with `leaseExactL T`; the class track's `leasesLive` at `T`, i.e. `kvOwnAt E
  log T`, split at the top from the two `ltHalf`s; the backend Put/Txn take `E.Nx` in their live branch), and the
  latest track's `X` with `leaseExactL T`; (2) `backendStep` over the live set (wider); (3) narrow S3a: no leased put
  or transaction admitted (`plainReqL lm := plainReq`), leased puts moved to a later stage with (1).
- **Decision.** (3) now, then (1) as its own stage S3a2 (etcd-grove-81, 2026-11-15): Draft rev 7, §15; `plainReqL lm :=
  plainReq`.

## 2026-11-15: txn.Txn's write wand is not told the lease check (auth-lease S3a2 §2)

- **Spec.** `txn.Txn.specSole` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/Txn.lean:62-65`; frozen text,
  `notes/mvcc-api-clients/clients-txn.md` §8): the caller's write wand is told `PathsIgnOk (stateAfter log) br` only.
- **Defect.** Too weak for a caller whose commit certificate depends on the leases: `applierV3backend.Txn` builds
  the commit's witness `E.Nx` inside that wand, and S3a2's certificate at the live set (`certPreT … L`, ledger
  2026-11-15 option (1)) covers an applied transaction only with `PathsLeaseOk (stateAfter log) L br`.
- **Evidence.** Go: `checkTxn` (with `checkPut` → `checkLease`) runs before `kv.Write` (`server/etcdserver/txn/txn.go:54-67`,
  `put.go:71-72`). Proof: `Hlok : PathsLeaseOk L` is in scope at `Proof/…/txn/Txn.lean:182`, the wand called at
  `:256`. Probe: `Scratch/S3a2Probe.lean` (`Txn_wp_T` over a local copy of the strengthened spec).
- **Proposed change.** The wand's premise `⌜PathsIgnOk … br ∧ PathsLeaseOk (stateAfter log) L br⌝` (a weaker
  obligation on the caller); `txn.Txn`'s proof passes `⟨Hign, Hlok⟩`; `TxnSpecs.lean`/`clients-txn.md` §8 updated.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3a2 Freeze, decision 2): the wand gains
  `PathsLeaseOk (stateAfter log) L br`; `clients-txn.md` §8's frozen text noted as changed by this entry.

## 2026-11-15: authTie at a leased request -- false in the refused-implies-not-permitted direction (auth-lease S3a2 §4a)

- **Spec.** `authTie` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/ReqOn.lean:89-91`), in `resultIsWOn` and
  `modelOutM` (`:151`, `:221`), read by `EtcdServer.processInternalRaftRequestOnce`'s spec.
- **Defect.** `o = .rejected .auth ↔ ¬ kvGranted st rq`: `kvGranted` is the permission check only; the auth layer
  also refuses a leased put whose lease carries a key the principal may not write (`checkLeasePuts`,
  `apply/auth.go:198-219`; the model's `¬ kvGrantedL`). Once S3a2 admits leased puts with auth on, the `→` direction
  is false.
- **Evidence.** S3a2 review r3 F1 (`/shared/tmp/auth-lease-s3a2/review-r3.md`); the example: key `a` permitted, the
  lease carrying `b` not.
- **Proposed change.** (b) the iff at `kvGrantedL st (leaseItemsOf (stateAfter lb)) rq`, `authTie` gaining the log
  `lb` (recommended since S3a2 Draft rev 5, review r4; probed `Scratch/S3a2ProbeTie.lean`); alternatives (a) one
  direction, (c) the iff for requests without a leased put: S3a2 Draft §4a.
- **Decision.** (b) (etcd-grove-81, 2026-11-15, the S3a2 Freeze, decision 3): the iff at the model's `kvGrantedL`,
  `authTie` gaining `lb`.

## 2026-11-15: the 7f-5a Draft's store watch (independent re-review: M1, M2, m1, m2)

- **Spec.** `Draft.store.Watch.spec` and its vocabulary (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean`,
  unlinked; `notes/k8s-7f5a-draft.md` §10), before 7f-5a-P moves it to `Spec/`.
- **Defects.** (M1) the client may deliver a progress notification at the watch's start, `hdrRev = c` with
  `c + 1 = rev`, with no bound by a fired state (`watchStateRespOk`, `WatchStateDefs.lean:125-128`); the producer
  queues it as a bookmark, which `KRawTail.bm`/`KTail.bm` (`p ≤ σ.rev`) cannot hold. (M2) `kCancelPD` lacked the
  processing goroutine's own cancel (its `sendError`'s deferred `wc.cancel()`, watcher.go:559-562, 796).
  (m1) the post's error arm said only `err ≠ nil`. (m2) `kStartOk`'s `max m.req 1 ≤ st` needs `1 ≤ σ0.rev` in
  the legacy case, which neither `kvWf` nor a firing gives.
- **Evidence.** The re-review (etcd-grove-81, 2026-11-15); Go: watcher.go as cited; for M1, the driver check
  `watchOkL` rejects any event above the configuration's revision (`KWatch.lean:209`), and 7f-6's traffic draws
  future resource versions for legacy watches (`notes/k8s-7f-scope.md` §1), so a bookmark at a future start is
  one the consumer cannot accept; etcd does not send one (`progressIfSync` returns unless `rev ≥ w.startRev`,
  `server/storage/mvcc/watchable_store.go:539`): the client spec is looser than etcd.
- **Changes.** (M2) `kProcExited` set before the processor's `sendError`; `kCancelPD` gains it; `kInElem`'s no-gap
  fact gains it as a third disjunct (the processor refutes it). (m1) error arm `err ≠ nil ∧ sie = some false ∧
  uint.nat n = 0`. (m2) `kStartOk`'s watch-list arm `st = σ0.rev ∧ m.req ≤ st` (the `1` from the caller's `Q`).
  (M1) see the next entry. Was OPEN: the Draft-local fix (`bm` admitting `p = c` unbounded) does not serve the consumer (above); the
  alternative is the client's `watchStateRespOk` start disjunct gaining `hdrRev ≤ σ.rev` (an exported client
  spec), a stop for etcd-grove-81.
- **Decision.** M2, m1, m2: decided by etcd-grove-81 (2026-11-15; m2's form chosen by the agent). M1: open.

## 2026-11-15: the client watch's progress notification at the watch's start has no state bound (7f-5a M1)

- **Spec.** `client.watchStateRespOk` (`Proof/go_etcd_io/etcd/client/v3/WatchStateDefs.lean:125-128`), the element
  of `watcher.Watch.spec`'s channel (`watchStateElemP`), and the server-level `client.rawRespOk` (same file).
- **Defect.** Too weak: a progress notification at the cursor when the cursor is the watch's start
  (`hdrRev = c`, `c + 1 = rev`) carries no bound by the state `σ` (`watchStateRespOk`) nor a certified log
  (`rawRespOk`'s `c = hdrRev` arm). A consumer cannot exclude a progress notification at a revision etcd has not
  reached: the etcd3 store's watch queues it as a bookmark (`KTail.bm` needs `p ≤ σ.rev`), and 7f-6's driver check
  rejects a bookmark above the configuration's revision while its traffic watches from future revisions.
- **Evidence.** etcd sends a progress notification to a watcher only once the store reached its start
  (`progressIfSync`: `if rev < w.startRev { return false }`, `server/storage/mvcc/watchable_store.go:539` at
  `673da07c8f`). Proof: the server-level fact already has the log (`progCovd`: `sint.nat x.rev < L.length`;
  `cmpl_cov` gives `dd ≤ Lc.length` outright), which `cmpl_prog`'s at-the-cursor case drops.
- **Proposed change.** `rawRespOk`'s progress arm always carries `∃ L, □ W.histLb L ∗ ⌜hdrRev < L.length ∧
  rangeLogEvents L o (c+1) (hdrRev+1) = []⌝` (the `c = hdrRev` arm without a log removed); `watchStateRespOk`'s
  progress arm always `hdrRev ≤ σ.rev ∧ rangeEvents σ o (c+1) (hdrRev+1) = [] ∧ kvLogOkTo σ hdrRev` (the start
  disjunct removed: at `c = hdrRev` the range is empty). A stronger post of the exported client spec; `cmpl_cov`/
  `cmpl_prog` keep the log; `raw_to_state` fires at a state through it; the readers lose a case.
- **Decision.** Approved (etcd-grove-81, 2026-11-15): strengthen, land as its own unit before 7f-5a-P; no closed
  theorem statement changes, tcb stays 870/4; upstream's traffic kept.

## 2026-11-15: the server's lease requests with auth on (auth-lease S3b; Draft `notes/auth-lease-s3b-draft.md` rev 3)

One entry for the frozen texts S3b changes (Draft §6's table); the evidence of each is the Draft's section.

- **Spec.** `EtcdServer.LeaseGrant.spec`, `EtcdServer.LeaseRevoke.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/`),
  `srvGrantsLeases`/`srvRevokesLeases`, `reqPropOkOn`, `putPermitOn`/`txnPermitOn`/`txnPermitM` (`ProposeOn`, `ReqOn`).
- **Defect.** No proposer of a grant, a revocation, a leased put or a leased transaction with auth on: the two lease
  specs and `srvGrants/RevokesLeases` require auth off, `reqPropOkOn` has no lease form, `putPermitOn` requires lease 0
  and `txnPermitM` `txnPlain`, though Go serves all four with auth on (`v3_server.go` `LeaseGrant`/`LeaseRevoke`,
  `requireAuthInfo` at `:447`; the apply side admits them since S3a/S3a2).
- **Proposed change.** Draft §1, §2, §4.2, §4.3: the auth-off conjuncts dropped; the specs at `isServerReqM E.authOn`
  with the client's update (`leaseGrantPermitM`/`leaseRevokePermitM`) and, on success, `authedOutB` and
  `leaseGrantResM`/`leaseRevokeResM`; `reqPropOkOn`'s write disjunct at `plainReqL lm ∨ grantPropOk lm ∨ revokePropOk lm`,
  `rqShape lm`, `grantIdOwn`; the permits' lease disjuncts at the revocable mode.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3b Freeze); D6: the v3rpc lease handlers' contracts and
  etcdstart's registrations at the mode in S3c.

## 2026-11-15: authTie says nothing of revocations or of a leased put's lease (auth-lease S3b D1)

- **Spec.** `authTie` and its carriers `resultIsWOn`, `entryWitOn`, `resultΨOn`, `modelOutM` (`ReqOn.lean`; frozen at
  S3a2 rev 6), read by `processInternalRaftRequestOnce.spec`/`raftRequest.spec` through `appliedOkM`.
- **Defect.** Guarded by `isKVKind` (excludes `.leaseRevoke`): a successful revocation cannot be shown granted. It
  carries no liveness: a successful leased put cannot be shown to have met a live lease (`backendStep` admits an
  applied put of a dead lease; the lease exactness is dropped at the KV arm).
- **Evidence.** Draft §3; probe `Scratch/S3bProbe.lean` (`authTieB_of_kvOutL`, `kvGrantedL_of_tieB`, `leaseLive_of_tieB`).
- **Proposed change.** Guard `authKVKind`; the post gains `plainCover rq ∨ apply.leaseExactL lt.ids rq lb o`; `authTie`
  gains the model's table `lt`, threaded through the carriers.
- **Decision.** D1 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: grantedAt is the permission check only (auth-lease S3b D2)

- **Spec.** `grantedAt`, `grantedAt_iff` (`ProposeOn.lean`), hence `writeGrantG`/`grantedRes` and the posts of
  `Put`/`DeleteRange`/`Txn.spec`.
- **Defect.** `kvGranted` omits the lease part of the model's verdict (`kvEntryOn`'s guard is `kvGrantedL`): a client's
  update cannot be refuted for a put permitted on its key but refused for its lease's keys (`etcd_authlease_safe`
  checks 2, 3, 5).
- **Proposed change.** `grantedAt` at `kvGrantedL … (leaseItemsOf (stateAfter (kvModelOn …)))`; `grantedAt_plain` keeps
  the old meaning for every request without a lease part.
- **Decision.** D2 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: Put.spec's success does not say the lease was live (auth-lease S3b D3)

- **Spec.** `EtcdServer.Put.spec` (frozen `Spec/` text), with the exported `put_applied`.
- **Defect.** The success's client result `Q (kvStateOf x.log lt)` does not exclude the state where `kvOpStep (.put op)`
  is `leaseMissing`'s identity, though Go's success means the lease was found (`checkLease`, `put.go:71`).
- **Proposed change.** The success post's pure conjunct gains `¬ (kvStateOf x.log lt).leaseMissing op.leaseID`.
- **Decision.** D3 approved (etcd-grove-81, 2026-11-15).

## 2026-11-15: txnAppliedOk does not say a leased transaction's leases were live (auth-lease S3b D7)

- **Spec.** `txnAppliedOk` (`InvRead.lean`, the writing post of `EtcdServer.Txn.spec`; frozen).
- **Defect.** As D3's for a transaction: a committed transaction's executed path's leases were live (`checkTxn`), the
  post does not say so.
- **Proposed change.** The pure conjunct gains `l ≠ x.log → txn.PathsLeaseOk (stateAfter x.log) lt.ids (t'.branch …)`.
- **Decision.** D7 approved (etcd-grove-81, 2026-11-15).
