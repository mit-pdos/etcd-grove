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

## 2026-11-15: real bbolt's `flock.spec`, `DB.close.spec_owned` and writer invariant -- the descriptor's `flock` lock unaccounted

- **Spec.** `Proof/go_etcd_io/bbolt/Open/Flock.lean` (`flock.spec`, internal), `Open/Close.lean`
  (`DB.close.spec_owned`, internal), `Inv/Locks.lean` (`wdbCoreG`: the descriptor and the `path` field), the
  internal specs naming the database's descriptor (`fdatasync.spec`, `Tx.write` ext, the remaps', `Open/Core`'s,
  `DB.loadFreelist`'s pre).
- **Defect.** Unprovable after the merge of `wal-int` `7fe119fb19` (the file-lock semantics, pending the
  user's review): `OsFd` gains lock fields (`ofd`, `flk`), `syscall.Flock` changes them (`lockOut`) and
  `os.File.Close.spec` takes the description's lock tokens (`lockToks`). bbolt's `flock` kept the
  descriptor unchanged, and `close` had no token for `funlock`/`Close`.
- **Evidence.** The full build: `Proof/go_etcd_io/bbolt/Inv/Locks.lean:293` (`⟨p.ino, true, true⟩`: 3 of
  `OsFd.mk`'s 5 fields), then `Open/Flock.lean`, `Open/Close.lean`, `Open.lean` against the new
  `syscall.Flock.spec`/`os.File.Close.spec`.
- **Change (made).** As minibolt's on `wal-int`: `flock.spec` takes `d.flk = none` and returns, on `nil`, the
  descriptor `d.setLk .flock (some ex)` with its `lockTok`, on an error `d` unchanged; `close.spec_owned`'s file
  takes `lockToks fd d` (its `funlock` passes the `flock` token through, `File.Close` gets both); the database's
  descriptor after `Open`'s `flock` is `dbFd i` (`⟨i, true, true, none, some true⟩`); its token rides with the
  `path` field in the writer's core (`dbPathLk db p fd`, `wdbCoreG`), which only `Open`, `close`, `loadFreelist`
  and the remaps touch. No exported statement changed (`Open.spec`, `DB.Close.spec` unchanged).
- **Decision.** Repair made on `wal-lean` (session 3, `notes/wal-units/lean-integration.md`), following the
  coordinator's instruction ("rebuild bbolt and repair as minibolt was"); stands or falls with the lock
  semantics' review.

## 2026-11-15: the etcd examples' closed theorems -- over no file extension, but `fileutil`'s initializer needs one

- **Spec.** The closed theorems of the etcd and Kubernetes examples (`Proof/.../examples/{etcd,k8s}/*/Adequacy.lean`
  and their restatements in `Results.lean`): `etcd_{compacted,putget,putget3,restart1,lease,leasegrant,leaseexpiry,
  leasecatchup,compactwatch,txnlin,partition}_adequate` (`_safe`), `etcd_partition_watch_adequate`, `k8s_compactor{,
  _partition}_adequate`, `k8s_etcd3{,_cluster,_partition}_adequate`, and, through the same cause, `etcd_{auth,auth3,
  watch,cache}_adequate`.
- **Defect.** Unprovable on `wal-lean`: they ran over `TrivialExt.lean`'s `[idIssueExt]`, but `fileutil` (now
  translated with bodies) has a package `init` (lock_linux.go) that probes `F_OFD_GETLK` through
  `syscall.FcntlFlock`, whose model is over the Linux file extension, and the server imports `fileutil`, so every
  etcd program's `wp_initialize'` takes `[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`.
- **Evidence.** The full build of `wal-lean` (session 2 of `notes/wal-units/lean-integration.md`): 13 adequacy
  modules fail with `failed to synthesize HasExt Fs.fsExt` (the other four import `putget`'s or `partition`'s and
  were not attempted).
- **Change (made).** Each theorem runs over `etcdFsExts` = `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`; the
  file extension's own semantics `fs_semantics`, no premise on the environment; its ghost state `fs_interp`) and
  takes one new premise, `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)` (the file extension's initial state: no
  process state, nothing logged, every file named and on disk, the roots well formed), as the osfs programs'
  results do. The conclusion is unchanged. The proofs use none of the extension's start resources (the probe takes
  no extension step, `syscall.FcntlFlock.wp_getlk`).
- **Decision.** The user's, option (A) (2026-11-15; the alternatives were a trust-boundary fact for `fileutil`'s
  initializer, or a names-only second translation of `fileutil` for the server). Made on `wal-lean` (session 3 of
  the log, which lists the restated theorems for the user's review).
## 2026-11-16: the client watch's element (`watchStateRespOk`, `client_Watch_field`) -- too weak for a user: a watch response's close error has no known dynamic type

- **Spec.** `Proof/go_etcd_io/etcd/client/v3/WatchStateDefs.lean`, `watchStateRespOk` (and the server-side
  `rawRespOk`), the element of every client `Watch` spec (`Spec/go_etcd_io/etcd/client/v3/
  Client__Watch*.lean`, `client_Watch_field`); the plan's client watch (`SpecPlan/Spec/go_etcd_io/etcd/
  client/v3/`) states no close error at all.
- **Defect.** Too weak: the error arm gives only `statusErrOk v.closeErr'`. k8s's `watchChan.startWatching`
  hands `wres.Err()` to `sendError`/`isCancelError`, which need the error's dynamic type (one of
  `clientErrTys`, a leaf) and, for an `*errors.errorString`, that it is a pointer (`kErrOk`'s `==` with
  `context.Canceled`). The placeholder `clientWatchCE.spec` asked `clientErr` and `errCellOk`; `errCellOk`
  is FALSE: a refused create's close error is `rpctypes.Error(errors.New(resp.CancelReason))`, an
  `*errors.errorString` holding the server's message (permission denied, `"mvcc: watcher range is empty"`).
- **Evidence.** `watchChan__startWatching.lean`'s pending hypothesis (7f-5a-P step 5); Go:
  `nonissues/etcd-watch-refused-create-err-plain.md` (its test); the stream errors' shape:
  `examples/k8s/etcd3/streamerr_test.go` (T-CE).
- **Proposed change.** New client vocabulary `errPtrOk e` (an `*errors.errorString` error is a pointer) and
  `closeErrOk e := statusErrOk e ∗ ⌜(e ≠ nil → clientErr e) ∧ errPtrOk e⌝`; the element's error arm, `run`'s
  published close error (`closeErrPub`), the stream's `closeErr` field and the receive errors (`errP`) carry
  `closeErrOk` in place of `statusErrOk`. Needs the trusted `cliStreamErr` to give `errCellOk` (T-CE).
  startWatching then uses the client's `Watch` spec instead of `clientWatchCE.spec`.
- **Decision.** Accepted with `errPtrOk`, not `errCellOk` (etcd-grove-81, 2026-11-16); T-CE approved (same).

## 2026-11-15: `fmt.ErrorfPlain.spec` (trust boundary) -- false for a flagged `w` verb (`%+w`, `%-5w`): the premise `¬ List.IsInfix "%w" format` lets them through

- **Spec.** `Spec/fmt/ErrorfPlain.lean`, `fmt.ErrorfPlain.spec`; its axiom `fmt.ErrorfPlain.wp_proof`
  (`Proof/fmt/ErrorfPlain.lean`). No SpecPlan counterpart.
- **Defect.** False of Go: a `w` directive with flags, width or precision has no `%w` infix, parses as
  a `w` directive (`fmt.fmtDirectives`), which `fmt.argsOk fmt.errorfVerbs` admits, and Go's
  `doPrintf` wraps at every `w` verb (`fmt/print.go:1051-1052,1146-1147`, go1.27.3): `Errorf` returns a
  `*fmt.wrapError`, not the leaf `*errors.errorString` the post claims. Latent: the two callers
  (`rafthttp.checkPostResponse`, `streamReader.dial`) use literal formats with no `w` verb.
- **Evidence.** `notes/axiom-review/errorfplain.md` (k8s 7f-5a-P, 2026-11-15); the counterexample
  `examples/axiomcx/errorfplain` (`errors.Is(fmt.Errorf("%+w", io.EOF), io.EOF)` is true).
- **Proposed change.** The premise becomes E3's (`notes/k8s-7f5a-draft.md` §11.3): `∃ ds,
  fmt.fmtDirectives format = some ds ∧ ∀ d ∈ ds, d.verb ≠ W8 119`; the post unchanged. Evidence of the
  new premise: `examples/premisefix/errorfwrap` (`TestNoWDirectiveGivesErrorString`, 200000 random
  formats). The callers discharge it by `refine ⟨_, rfl, ?_⟩; decide`.
- **Decision.** Accepted (etcd-grove-81, 2026-11-15; branch `errorfplain-fix`).

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

## 2026-11-13: `wal.WAL.ReadAll.spec` -- the success post `walReadCut … = some σ` is false of a Save-then-SaveSnapshot history

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReadAll.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable: Go's `ReadAll` folds from `Open`'s start snapshot `s` (the entries' base fixed
  at `s.Index`), while `walReadCut`'s fold moves its base only at snapshot records it has read.
- **Evidence.** `readAllFold_zero_dev` (branch `wal-fold`, `Proof/go_etcd_io/etcd/server/v3/storage/WalEncFold.lean`,
  proved): the history `Save({Term 1, Commit 5}, [entry 6 term 1])`, `SaveSnapshot({Index 5, Term 1})`;
  `Open` starts at `(5,1)`; Go's `ReadAll` succeeds with `[e6]`, `walRead I = none`. Raft does not
  produce this order (etcd saves the snapshot record before entries above it), but `Save`'s spec allows it.
- **Proposed change.** `ReadAll`'s success post states Go's fold, `walReadAt I k s` (the fold from the
  base `s`), and a lemma gives `walReadAt I k s = walReadCut I k` under a history condition the server's
  and the tester's histories meet (the condition to be found: e.g. every entry above a snapshot record's
  index is saved after it), so the clients keep `walReadCut`.
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, no client-visible ghost
  state added); the condition and the lemma on branch `wal-fold`.

## 2026-11-13: the WAL decoder's `isEofOk` -- `errors.Is` asked of `nil`, and `io.EOF` must be neither `io.ErrUnexpectedEOF` nor an `IoE` error

- **Spec.** `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/DecDefs.lean`, `isEofOk` (in `decEnv`, the
  precondition of `decoder.Decode`/`decodeRecord`; W3a of `notes/wal-fsext-plan.md`).
- **Defect.** Unprovable `decodeRecord`: (1) Go asks `errors.Is(err, io.EOF)` of `readInt64`'s error also
  when it is `nil` (decoder.go:95), which `isEofOk` did not cover; (2) with `io.EOF = io.ErrUnexpectedEOF`
  a short length word would drop the file; (3) with `IoE io.EOF` a reader may end a file early with
  `io.EOF` (`decRdErr`), and the decoder goes on in the next file, which `goDecode` does not say.
- **Evidence.** The proof of `decoder.decodeRecord` (branch `wal-dec2`): the three cases are where it stuck.
- **Proposed change.** `isEofOk` also covers `e = nil` and carries `⌜eof ≠ ueof ∧ ¬ IoE eof⌝`; all three are
  true of Go (`errors.Is(nil, t)` is `nil == t`; the two `errors.New` allocations differ; the client's `IoE`, the
  `os` file errors, are expected not to include `io.EOF`), a client obligation like the rest of `isEofOk`.
- **Decision.** Adopted (proof agent, minor: an intermediate client obligation, no ghost state).

## 2026-11-13: the WAL decoder's `proto.Unmarshal` -- a failure is not `recDecode bs = none`; the decoded record cannot be reset

- **Spec.** `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean` (a hypothesis of
  `decoder.decodeRecord`), `walpb.Record.Reset.spec`, `decoder.{decodeRecord,Decode}.spec` and `decPost`
  (`DecDefs.lean`), the registered `walpb.Record`'s `decC` (`PbRecord.lean`); W3a of `notes/wal-fsext-plan.md`.
- **Defect.** (1) `UnmarshalWalRecord.spec` said `Unmarshal` fails exactly when the canonical decoding
  `recDecode` does; `proto.UnmarshalPb.spec` (D1/D2) gives only "success is the canonical decoding" and
  "a valid encoding succeeds", so it was not derivable. (2) Its precondition `l ↦ zero_val` and `Reset`'s
  post, against the registration's `blank`. (3) The registered `decC` put the record's hidden fields in an
  invariant, so a decoded record could never be `Reset` (the decoder reuses `rec`) without duplicating them.
- **Evidence.** The derivation attempt (`wal-dec2`, notes W3a), and `UnmarshalPb`'s error post, which
  returns no record.
- **Proposed change.** The coordinator's decision (2026-11-13): the weaker model. `Unmarshal` may fail on
  bytes that are no record's encoding (`UFail`), a failure being a `badRec` stop of the Go decoder
  (`GoFail`, `decPost`'s third disjunct, the record not given back; `ReaderRun.fail`); success is
  `recDecode`. The spec stated over `walCodec` and `pbRecordC.data.blank`, derived from `UnmarshalPb`;
  `decodeRecord`/`Decode` take `C = walCodec`; `Reset` returns `blank`; `decEnv` gains `isPkgInit proto`;
  the registered `decC` owns the decoded record whole (trusted, pending the user's review with the
  registration).
- **Decision.** Adopted (the coordinator for the model; proof agent for the `decC` ownership, flagged for review).

## 2026-11-13: `wal.WAL.Sync.spec` -- the error arm keeps the handle, though a failed flush leaves a partial write

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Sync.lean` (the W4a axiom; its proved replacement
  over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`, branch `wal-save`).
- **Defect.** Unprovable: `sync` flushes the encoder's page writer first; a failed flush drops the pending
  buffer after part of it reached the file, so the handle's state no longer matches the file and no
  later operation on it can be proved.
- **Evidence.** The W6 proof attempt (`notes/wal-fsext-plan.md`, W6 log); `ioutil.PageWriter.Flush.spec`'s
  error post (proved, branch `wal-enc3`).
- **Proposed change.** On error, `Sync` consumes the handle (as `Save`'s and `SaveSnapshot`'s error arms
  do, plan §3); etcd's callers stop on that error (`Fatal`).
- **Decision.** Adopted (the coordinator, the user away; an intermediate spec, every client stops there).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- a snapshot's index must not be below an earlier snapshot record's

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshot.lean` (the W4a axiom; its proved
  replacement over `fsExt`, `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`).
- **Defect.** `SaveSnapshot` sets `w.snapi` to the saved snapshot's index (not the maximum), and `cut` names
  the next segment after `max(w.enti, w.snapi) + 1`, which must exceed every index in the history
  (`walLastIdx`) for the segment names to stay increasing; a snapshot saved below an earlier one breaks
  it (the W6/W2 proofs, `notes/wal-fsext-plan.md`).
- **Evidence.** The handle fact `walLastIdx H ≤ max(enti, snapi)` (W2, `wal-cut7`) cannot be kept by
  `SaveSnapshot` otherwise (W6, `wal-save8`'s log).
- **Proposed change.** `SaveSnapshot.spec` takes `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`. etcd
  saves the snapshots raft hands it (received, above the committed index) and its own (at the applied
  index, at least every snapshot applied before): monotone, to be checked at C6.
- **Decision.** Adopted provisionally (the coordinator, the user away); **for the user's review**: a new
  client obligation on the server (C6).

## 2026-11-13: `wal.WAL.SaveSnapshot.spec` -- the index premise above is not needed (withdrawn); the handle's snapshot bound is

- **Spec.** The previous entry (`SaveSnapshot.spec`'s proposed `∀ s ∈ snapshot records of H, s.Index ≤ m.Index`);
  `walHandleIn` (`LinuxFs/Proof/.../wal/Handle.lean`).
- **Defect.** The previous entry's defect does not hold at the pin: the translated `SaveSnapshot` (fork
  `0b50f0426`, S/wal.go:1161-1167) raises `w.snapi` and `w.enti` to the snapshot's index only when it is
  larger, so `walLastIdx (H ++ [snap m]) ≤ max(enti', snapi')` follows from the old bound with no premise.
  The real gap is elsewhere: `Save` of entries below an earlier snapshot record (`saveEntry` *sets* `w.enti`,
  S/wal.go:1086) needs `walMaxSnapIdx H ≤ snapi`, which the handle did not carry (with `enti = 120`,
  `snapi = 50`, a snapshot record of 100 read back, a `Save` of entries 60-70 would leave `walLastIdx = 100 >
  max(70, 50)`).
- **Evidence.** The W6 proofs (`wal-save9`): `walLastIdx_snap`, the Go code above.
- **Proposed change.** No premise on `SaveSnapshot`. `walHandleIn`'s index facts become `(rest = 0 →
  walLastIdx H ≤ max(enti, snapi)) ∧ walMaxSnapIdx H ≤ snapi` (internal; `saveEntry`/`saveState` take the
  `rest = 1` case as a premise, which `Save` supplies). Obligation for `ReadAll` (W3/W5) and `Create` (W4) when
  they build the handle: `walMaxSnapIdx H ≤ snapi` (`ReadAll`: every snapshot record before its first segment
  is below that segment's name index, at most the target snapshot's, which it reads; `Create`: 0).
- **Decision.** Adopted (proof agent; withdraws a provisional client obligation, so nothing for the user to
  approve; flagged in the W6 log).

## 2026-11-14: `wal.WAL.Save.spec`, `wal.WAL.SaveSnapshot.spec` -- no bound on the records' size

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`,
  `WAL__SaveSnapshot.lean`).
- **Defect.** The append's commit (`walTail_append`, before any record is written) must keep the
  invariant's static relation, whose `fit` says every record's encoding is below `2^56` bytes (the
  frame's 56-bit length field: `encodeFrameSize` puts the padding in the top byte, so a longer record
  corrupts its frame); the encoder's spec needs each record below `2^47` (`encode.specG`'s `recSize`,
  protobuf-go's `MarshalAppend`). Nothing bounds `Mr.encEntry e` or `Mr.encSnap md`: the part's `Save`
  dropped the main tree's `walSaveEnts sized` (whose `entSizeOk` bounded the entries), and `entIn` has no
  size.
- **Evidence.** `Append.lean`/`HandleAppend.lean` (`walHandleIn_append`'s `hfit`: `∀ c, RecsFit walCodec
  (chainRecs walCodec c (opDs Mr o.toM))`); `encoder__encodeG.lean`.
- **Proposed change.** A premise of `Save`: `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`, and of
  `SaveSnapshot`: `(Mr.encSnap md).length < 2 ^ 40` (the hard state's record: `walAreaOk`'s law). True of
  etcd: raft entries are bounded by the server's request size limit (`--max-request-bytes`, below
  `2^31`), snapshot metadata is a few varints and the conf state's member ids. A C6 obligation on the
  server.
- **Decision.** Adopted as a minor fix (`wal-save11`, for the coordinator's and the user's review): the two premises
  are in the part's specs.

## 2026-11-14: `wal.WAL.SaveSnapshot.spec` -- `walSnapAt` does not determine the bytes `SaveSnapshot` writes

- **Spec.** `walSnapAt sp md cs` (the WAL vocabulary, `Proof/go_etcd_io/etcd/server/v3/storage/WalDisk.lean`),
  taken by `SaveSnapshot.spec`; in the part over `fsExt`, `LinuxFs/Spec/.../wal/WAL__SaveSnapshot.lean`, whose
  history records `.snap md` written as `Mr.encSnap md` (`WalEncRecs.opDs`).
- **Defect.** `walSnapAt` fixed the index, the term and whether the conf state is nil, not the conf state's
  content nor either level's unknown fields, all of which `pbutil.MustMarshalMessage` writes; so the bytes
  of the snapshot record were not a function of `md`, and the law `MustMarshalMessage.specWalSnap` (bytes
  `Mr.encSnap md`) was false of the real marshaller. It also held the object as a whole frozen struct
  (`sp ↦□ s`), which protobuf-go's `Marshal` (it writes `sizeCache`) cannot read.
- **Evidence.** The W6 proof (`notes/wal-fsext-plan.md`, W6 log, fifth and ninth sessions);
  `MustMarshalMessageWalSnap.lean`'s former "Open" note.
- **Proposed change (made, in the part).** `walSnapAt Mr sp md cs` (`LinuxFs/Proof/.../wal/walpb/
  PbSnapshot.lean`): a frozen `walpb.Snapshot` at a wire content `c` (`snapRoC`, the registered
  `walpb.Snapshot`, hidden fields of both levels in invariants) with `c.model = md`, `Index`/`Term` set,
  `cs = c.confState.isSome`, and **`snapEnc c = Mr.encSnap md`**. `walSnapIdTerm` is over the same content
  (the getters' index and term). **New client obligation (C6):** the server's marshaller parameter `Mr`
  must give one wire form per snapshot metadata, the one of every `walpb.Snapshot` it passes. Plausible: the
  server builds each one the same way (`storage.go:62-66`, `Index`/`Term` copied from raft's metadata, the
  conf state raft's own object), so `Mr.encSnap md` is `snapEnc` of that shape provided raft's conf states
  carry no unknown fields (raft builds them; a decoded one from a peer could, which C6 must exclude or
  carry). The main tree's `walSnapAt` (the W4a axioms' vocabulary) is unchanged until the part's specs
  replace them.
- **Decision.** Adopted (the coordinator's decision, W6 ninth-session plan; the user away). **For the
  user's review** with the two trusted axioms `snapEncC_ok`, `pbSnapC_reg` (plan §10).

## 2026-11-14: the WAL's marshaller parameter `Mr` -- a bound on the hard state's encoding

- **Spec.** The WAL specs over `fsExt` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`), their parameter
  `Mr : WalMarshal` (the client's marshallers of entries, hard states, snapshots).
- **Defect.** `cut` writes the hard-state record into a new segment's headers and needs
  `h.md.length + (Mr.encState h.st).length < 2^42` (W2, `wal-cut9`); nothing bounds `Mr.encState`.
- **Proposed change.** A law of `Mr` (in `walAreaOk` or `WalMarshal.Ok`): `(Mr.encState hs).length < 2^32` for
  every hard state; `md` is bounded at `Create`. raft's `HardState` encodes as three varints (at most
  ~33 bytes): discharged at C6 from raftpb's encoder.
- **Decision.** Adopted (the coordinator, the user away): a client-visible law on a parameter, true of
  etcd's marshaller.
- **Made** (`wal-save11`): the law is the last conjunct of `walAreaOk` (`CreateDefs.lean`;
  `walAreaOk_encState`); the metadata's bound `h.md.length < 2^41` is a conjunct of the sealed client
  handle `walOpenWF` (`Handle.lean`), an obligation of its producers: `Create` (a premise
  `md.length < 2^41` when its spec returns `walOpenWF`) and `ReadAll` (the WAL's metadata is `Create`'s:
  needs the invariant to keep `d.metadata.length < 2^41`, established at `Create`'s commit). The cuts'
  increase (`cut.spec`'s `h.cuts.Pairwise`) is not carried by the handle: the append's commit returns it
  from the invariant's static relation (`walTail_append`).

## 2026-11-14: `wal.Create.spec` (the part's, over `fsExt`) -- its success post is the ghost-only handle

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` (`wal.Create.spec`), success arm:
  `walOpenW w dir` (the sealed ghost handle: mode and lock token) and `osCallPerm ½`.
- **Defect.** `Save`/`SaveSnapshot`/`Sync`/`Close` (W6/W10) take the client handle `walOpenWF P Mr w dir`
  (`Handle.lean`: `w`'s fields, encoder, tail, pipeline, directory share, `walOpenW` inside), as `ReadAll`
  returns it; a WAL made by `Create` could not be appended to. The commit's out-record, the tails' authority half,
  the named entry and the metadata belong in that handle, and were dropped.
- **Evidence.** W4 log, eleventh session ("For the coordinator"); the coordinator's decision of 2026-11-14
  (task 3 of `wal-create12`).
- **Change (made).** `wal.Create.spec (P : WalPbIn GF) (Mr : WalMarshal)` over `walAreaOk walCodec Mr` (the
  handle's codec, as `Save`'s), `HeapGS HasLC.hasLC` (the handle's receipts); success arm `Q ∗ walOpenWF P Mr w dir ∗
  walNamed dir ∗ walLenLb w dir 0 ∗ walSyncedLb dir 0 ∗ walPurgeW w dir`, the call permission's half now inside the
  handle (`walDirH`). An internal refinement: no new client-visible ghost state (`walOpenWF` is the existing
  handle; it implies `walOpenW`, `walOpenWF_iff`); no client of `Create`'s part spec exists yet.
- **Decision.** Adopted (coordinator's decision; proof agent, `wal-create12`).
- **Addendum (2026-11-14, `wal-save11`'s obligation).** `Create.spec` also takes `md.length < 2 ^ 41` (a
  premise: the handle `walOpenWF` now holds `h.md.length < 2^41`); minor, the metadata etcd writes is small.
  The invariant's `d.metadata.length < 2^41` (for `ReadAll`) is to be established at `Create`'s commit
  (`walCreate_osAUnc`), not yet done.

## 2026-11-14: `wal.Exist.spec` -- the lock token, and a `false` that `fsExt` cannot exclude

- **Spec.** `wal.Exist.spec` (the main tree's W4a axiom `Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean`),
  restated over `fsExt` in `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Exist.lean` (W12 of
  `notes/wal-fsext-plan.md`).
- **Defects.** (1) *The token.* To read a present WAL's directory, `Exist` needs a fraction of its directory's
  claim, which `walParked` holds while no handle is open; taking it out needs the lock (`walParked_lock`,
  as `Open`'s pin). The old spec took no token. (2) *Q4 (b).* `Create`'s failure after its rename leaves a
  fresh, unnamed WAL whose directory `cleanupWAL` may have moved aside (plan §11): `false` must allow it.
  (3) *`false` on a present WAL.* `Exist` returns `false` when `ReadDir` fails with an error
  `errors.Is(_, os.ErrNotExist)` accepts. `fsExt` lets every failing system call return any errno, `ENOENT`
  included (`IsFsStep` "Open", "Readdir"), so the model has runs where `Exist` of a present, named WAL
  returns `false`: the old post (`false → o = none`) is false of the model, though true on configuration C
  (Linux's `open(2)` returns `ENOENT` only for a missing component; `getdents64` only on a removed
  directory, which a WAL directory under the area discipline is not).
- **Evidence.** `GooseLang/Ext/Fs/Impl.lean`, "Environmental failure is a nondeterministic errno"; the W12
  proof (the plan's W7-W12 log).
- **Proposed change.** (1) `Exist` takes `walUnlockedTok` (framed), as `Open` and `Create` do; its callers
  (the server's bootstrap, the tester's restart) call it with no handle open. (2) `false → o = none ∨ ∃ d,
  o = some d ∧ d.H = [] ∧ d.named = false`. (3) Kept the strong post, proved over the hypothesis
  `fileutil.ReadDir.specChildIs` (a present directory's read fails only with an error `errors.Is` does not
  take for `os.ErrNotExist`), unprovable against the current model; the model fix ("`ENOENT` only when the
  path does not resolve", for `open` and `getdents`) is the user's (trusted semantics) -- the alternative,
  a `false` that claims nothing, would leave `Create` (which needs `walAbsent`) unreachable from the
  server's bootstrap.
- **Decision.** (1), (2) adopted (minor; (2) is the coordinator's Q4 (b)). (3) **for the user**: the
  hypothesis stays until the model tightens `ENOENT` (`notes/wal-fsext-plan.md`, W7-W12 log).
## 2026-11-14: `wal.openAtIndex.spec`, `wal.Open.spec`, `wal.OpenForRead.spec` (the part's, over `fsExt`) -- the WAL directory's length and name

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/{openAtIndex,Open,OpenForRead}.lean`.
- **Defect.** `openWALFiles` (`filepath.Join(dir, name)`) and `newFilePipeline` take `dir.length < 2^61`; the
  specs bound neither `dir` nor the area `r` (the invariant records no length of a WAL's directory path).
  For an absent WAL, `selectWALFiles.specAbsent` (`os.Open` of a missing name) takes `NameOk nm`, which
  `walNameOk nm` does not give (it allows a NUL byte).
- **Evidence.** `openAtIndex`'s proof (W3/W5 log, twelfth session): the premises of `openWALFiles.spec` and
  `newFilePipeline.spec`.
- **Change (made).** The three take `dir.length < 2 ^ 59` and `NameOk nm`, as `wal.Create.spec` does (a path to
  a WAL directory is short in practice: Linux's `PATH_MAX` is 4096; etcd's name is `wal`).
- **Decision.** Adopted (minor, proof agent `wal-read12`; no client of the part's `Open` exists yet).

## 2026-11-14: `wal.Open.spec` (the part's, over `fsExt`) -- the call permission counted twice

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` (`wal.Open.spec`), success arm:
  `walOpeningF w dir s ∗ osCallPerm ½`.
- **Defect.** The client's `osCallPerm 1` is split by `openAtIndex` in write mode: half to the file pipeline
  (`walPipeH`), half returned. `Open` returned that half to the client, but the handle `ReadAll` makes from
  `walOpeningF` (`walOpenWF`, its `walDirH`) holds a half of its own (as `Create`'s does, ledger 2026-11-14):
  after `Open` and `ReadAll` the client would hold 3/2 of the permission, and `ReadAll` could not be proved
  (nothing in `walOpeningF` supplies the handle's half).
- **Evidence.** `openAtIndex`'s proof and `ReadAll`'s obligations (W3/W5 log, twelfth session, item (a)).
- **Change (made).** `Open`'s success arm is `walOpeningF w dir s` alone; the sealed `walOpeningF`
  (`ReadDefs.lean`) holds the half (`osCallPerm ½`), which `ReadAll` moves into `walDirH`. A resource
  placement, no new client-visible ghost state; `OpenForRead` (read mode: no pipeline, the whole permission
  returned to the client) and `openAtIndex` unchanged.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14, task 1 of `wal-read13`; no client of the
  part's `Open` exists yet).

## 2026-11-14: `wal.decoder.Decode.spec` (the part's, over `fsExt`) -- the error's identity

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean` (`decPost`, `stopErr`,
  `isEofOk` in `DecDefs.lean`).
- **Defect.** A reader looping to the end (`ReadAll`, S/wal.go:523-611) tests `errors.Is(err, io.EOF)` on the
  error `Decode` returned. (1) `stopErr`'s catch-all (`e ≠ nil`, for a bad frame, a CRC mismatch, a frame too
  large) allows `io.EOF` itself: `ReadAll` would then take a stop in the middle of the WAL for its end and succeed
  with the records after it missing, so its success post cannot be proved. (2) `isEofOk` answers `errors.Is` only
  on `nil`, `io.EOF`, `io.ErrUnexpectedEOF` and the readers' `IoE` errors, not on the decoder's own errors
  (`fmt.Errorf`'s, `proto.Unmarshal`'s), so the call cannot be stepped on them at all.
- **Evidence.** `ReadAll`'s proof (W3/W5 log, fourteenth session): the loop's exit and the write-mode stop check.
- **Change (proposed, not made).** `Decode.spec` (and `decodeRecord.spec`) add to `decPost`: `err = io.EOF` only
  at `goDecode`'s `.eof` stop, and `errors.Is(err, io.EOF)`'s answer for a non-nil `err` (`isEofAns`). Stated as
  `decoder.Decode.specR` (`decoder__DecodeR.lean`), a hypothesis of `WAL.ReadAll.wp_proof` until then. The
  proof needs Perennial's `fmt.Errorf` model to give an error distinct from `io.EOF` with `errors.Is` answering
  false on it (its wrapping is not kept) and the same of `proto.Unmarshal`'s error.
- **Decision.** Adopted (the coordinator, 2026-11-14; made by `wal-readall15`). `decPost` (`DecDefs.lean`) is now
  `decPostB ∗ decAns eof err`: the old body, and `errors.Is(err, io.EOF)`'s answer on a non-nil error
  (`isEofAns`); `stopErr`'s catch-all is `e ≠ nil ∧ e ≠ eof`, so `io.EOF` comes only from the `.eof` stop
  (the `IoE` arm excludes it by `isEofOk`). `Decode.spec`'s and `decodeRecord.spec`'s statements read the same
  (over `decPost`); `decoder.Decode.specR` is gone. The proof's new inputs: `fmt.ErrorfErrsNot.spec` (`Errorf`'s
  result is not `t` and `errors.Is(_, t)` is false on it when it is so of every error argument, `t` a package
  variable's value; a hypothesis, `LinuxFs/Spec/fmt/ErrorfErrsNot.lean`), `proto.UnmarshalWalRecordE.spec`
  (`Unmarshal`'s error is not `io.EOF`, the same answer; a hypothesis), `walpb.Record.Validate.spec` with the
  same of its error (statement change: targets `X`/`t`, premise `errIsNot ErrCRCMismatch t`), and `decEnv`
  holding `errIsNot ErrCRCMismatch io.EOF` (a client obligation, as `isEofOk`). `notes/perennial-changes.md`,
  2026-11-14, "`errors.Is` on `fmt.Errorf`'s result".

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch's size, not each entry's

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean`, premise
  `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40` (ledger 2026-11-14, "Records' size").
- **Defect.** Each entry bounded, the batch is not: the tail's stream grows by the whole batch before `Save`
  checks `SegmentSizeBytes`, and nothing then bounds the encoder's offset and pending bytes by ext4's maximum
  offset (`0xffffffff000`, `walHandleIn`'s `o0 + |out| + |pend|` bound, `Seek`'s and the writes' arithmetic):
  `saveEntry`/`saveState`/`encode.specTail` claimed it in their posts with no source (W6 log, twelfth
  session).
- **Evidence.** W6 log, thirteenth session (`wal-save13`): the bound is the stream before the call (a handle
  fact at quiescence, below) plus the batch's frames; a frame is at most its data plus 64 bytes
  (`frame_walRecEnc_tight`).
- **Change (made).** `Save` takes `walBatchBytes Mr es < 2 ^ 40` (each entry's encoding plus 64 bytes, summed;
  implies the per-entry bound). `SaveSnapshot`'s per-record premise is already its batch's. The handle fact
  (sealed `walOpenWF`, no client-visible change): the tail's stream end `o0 + |out| + |pend| < 2 ^ 43` at
  quiescence (`Save` cuts once the offset reaches `SegmentSizeBytes`, the pending bytes at most the page
  writer's buffer, 2^18; a cut's or `Create`'s headers at most the metadata, below 2^41, and the state).
  **C6 obligation**: raft bounds a `Ready`'s entries (`MaxSizePerMsg`, the uncommitted-size limit), so the
  server's batches are far below 2^40 bytes.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14 for `wal-save13`, task 2), with two
  corrections to its wording found in the proof: the fact is on the stream's end, not the offset (a `Save` that
  syncs flushes its pending bytes after its `Seek`, so the next `Save` may start at `SegmentSizeBytes` plus the
  buffer), and its bound covers a cut's headers (the metadata may reach 2^41 bytes).
- **Withdrawn (2026-11-14, `wal-maxb14`).** The model now bounds every file at ext4's `s_maxbytes`
  (`fsExt`'s `maxBytes = 0xffffffff000`, a trusted semantics change pending the user's review:
  `examples/osfs/semantics/data_maxbytes.go`, measured on configuration C). A write never lands a byte at or
  past it, so the tail's written stream stays below it by the writes' success alone, and nothing needs a
  bound on the stream before the write: `Save` is back to the per-entry premise of "no bound on the records'
  size" (needed by the frame encoding, not by the offsets), the handle's stream-end fact
  (`o0 + |out| + |pend|`, in `walHandleIn` and the sealed `walOpenWF`) is gone, and so are
  `saveEntry`/`saveState`'s stream premise and `encode.specTail`'s (entry below).

## 2026-11-14: `wal.WAL.Save.spec` (the part's, over `fsExt`) -- the batch premise withdrawn: the model's file-size bound

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Save.lean` (premise
  `walBatchBytes Mr es < 2 ^ 40`); the internal `WAL__saveEntry.lean`, `WAL__saveState.lean` (premise
  `(tailStream Mr h.H h.md h.cuts).length ≤ 0xffffffff000`), `encoder__encodeTail.lean` (premise
  `o0 + |out| + |pend| + |frame| ≤ 0xffffffff000`, and the same of the result in its post); the sealed handle
  (`walHandleIn`'s `o0 + |out| + |pend| ≤ 0xffffffff000`, `walOpenWF`'s `< 2 ^ 43`).
- **Defect.** `SaveSnapshot` never cuts (S/wal.go:1137-1162), so `n` calls in a row grow the tail by `n`
  records, and no constant bound on the stream holds across them (`SaveSnapshot.wp_proof`'s `sorry`, W6 log,
  thirteenth session); the batch premise only moved the problem.
- **Evidence.** W6 log, thirteenth and fourteenth sessions; ext4's `s_maxbytes` (`ext4_max_size`,
  `generic_write_check_limits`, `inode_newsize_ok`, `vfs_fallocate`), measured on C (`TestMaxBytes`).
- **Change (made).** The model: `PWriteFinish` lands nothing at or past `maxBytes`; `FtruncateFinish`,
  `FallocFinish` land no target past it; `CrashFile`, `FsInit` sizes at most it (`OsWf.sizes`). Clients get
  it through `PwCut` (a write's landed end) and `wp_osMeta_size` (any `OsMeta`'s size, before a step). The
  WAL: `Save`'s premise back to `∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40`; the stream premises and the
  handle's stream-end fact removed (the handle keeps `o0 + |out| ≤ sz ≤ 0xffffffff000`, which the writes'
  success now gives). A client-visible weakening of `Save`'s premise; no new ghost state.
- **Decision.** Adopted provisionally (the coordinator's decision of 2026-11-14 for `wal-maxb14`), pending
  the user's review of the trusted semantics change.

## 2026-11-14: `wal.WAL.Close.spec` (the part's, over `fsExt`) -- the directory's `Close` error after everything is closed

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean` (`wal.WAL.Close.spec`, new: the
  main tree's axiom's first conjunct with plan §3's binders), post `(∃ d, Q d ∗ walSyncedLb dir |d.H| ∗
  walUnlockedTok ∗ osCallPerm 1) ∨ ⌜err ≠ nil⌝`.
- **Defect (of the main axiom).** Its success arm required `err = nil`, its error arm was `¬ walCloseOk`. The Go
  code (S/wal.go:1053-1077) returns `w.dirFile.Close()`'s error after the sync, every lock's close and the
  put-back: an error there leaves everything closed and released, so a spec giving only `err ≠ nil` would lose
  the lock token and the update's `Q` for no reason; and `¬ walCloseOk` cannot be proved from an errno (plan §6 Q6).
- **Evidence.** `WAL.Close.wp_proof` (`LinuxFs/Proof/.../wal/WAL__Close.lean`): the put-back (`WalCloseLaw`) runs
  before `dirFile.Close()`.
- **Change (made).** The success resources whatever `err` (the left disjunct does not constrain it); a failed
  sync (S/wal.go:1064-1066, returned before the locks) gives only `err ≠ nil` (the handle is lost, as `sync`'s
  error arm loses it). The main axiom's second conjunct (`Close` of an opening or failed handle) is not restated
  here: `Open`'s error arm takes `WAL.Close.specOpening` (a hypothesis), the failed handle (`walReadFailedF`) waits
  for `ReadAll`.
- **Decision.** Adopted (the W10 session, 2026-11-14; plan §6 Q6's honest error posts; no client of the part's
  `Close` yet).

## 2026-11-14: `wal.WAL.saveEntry.spec` (the part's, internal) -- no bound on the entry's encoding

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__saveEntry.lean`.
- **Defect.** `encoder.encode.specTail` (as every encode spec) needs the record's size below `2 ^ 47`
  (`recSize`, the frame's length word); `saveEntry.spec` gave no bound on `Mr.encEntry e` (the per-entry
  bound was withdrawn with the batch premise, 2026-11-14, and moved back to `Save`'s premise only).
- **Evidence.** `WAL.saveEntry.wp_proof` (W6, fifteenth session): the encode's premise.
- **Change (made).** `saveEntry.spec` takes `(Mr.encEntry e).length < 2 ^ 40` (`Save`'s premise for each of its
  entries, which `Save`'s proof passes); internal spec, no client-visible change.
- **Decision.** Adopted (minor, internal; W6 fifteenth session).
## 2026-11-14: `WalDecEnvSupply` and `decEnv`'s `isEofOk` (the part's WAL decoder, over `fsExt`) -- the readers' errors and `errors.Is`

- **Spec.** `WalDecEnvSupply` (`LinuxFs/Proof/.../wal/openAtIndex.lean`, a hypothesis of `openAtIndex.wp_proof`,
  hence of `Open`/`OpenForRead` through it) and the decoder's environment `decEnv`/`isEofOk` (`DecDefs.lean`).
- **Defect 1 (made, fixed).** The supply put every pointer error in the readers' errors `IoE`, while `isEofOk`
  needs `¬ IoE eof` and `io.EOF` is a pointer error (an `errors.New` `*errorString`, `io.eof_of_init`): the
  hypothesis proved `False` under `isPkgInit wal`, and `openAtIndex`/`Open`/`OpenForRead` were vacuous.
- **Change (made).** `IoE` holds of every `*PathError` (`∀ pe, IoE (mkOk *PathError #pe)`); `os.File.Stat.spec`'s
  error is the model's `*PathError` (was: some pointer error; its proof already knew it). Sanity check:
  `walDecEnv_eof_not` (`io`'s initialization: `io.EOF` is no `*PathError`), so the pure part `¬ IoE eof`,
  `∀ pe, IoE (PathError pe)` is met by `IoE` = the `*PathError`s.
- **Defect 2 (open, not mine to fix).** Even so the supply is not true of Go: `isEofOk` asks
  `errors.Is(e, io.EOF)` to answer `false` for every `IoE` error with no precondition, and `errors.Is` of a
  `*PathError` unwraps its `Err` field (heap), so it answers `true` for a `&PathError{Err: io.EOF}`. No pure `IoE`
  can hold of the `*PathError`s `os.File.Read`/`Stat` return (fresh allocations, `os.errnoPathErr`'s persistent
  fields) and of no other: the errors' evidence is a heap fact, and the decoder's readers pass errors through
  pure predicates only (`io.readerStream`'s `E`, `bufio.ownReader`, `decRdErr`, and the trust-boundary axiom
  `io.ReadFull.wp_proof`, `Spec/io/ReadFull.lean`).
- **Proposed change.** Carry the error's evidence with it: `io.readerStream ri S E` with `E` a persistent Iris
  predicate (`List w8 → GoInterface → IProp`), so `ReadFull`'s axiom, `bufio`, `readInt64` and the decoder pass
  it on; `decRdErr`'s I/O arm then `os.errnoPathErr e n` (`n ≠ 0`, which `Read.wp_eof`'s error arm gives with a
  small strengthening), and `isEofOk`'s I/O branch is provable from an `errors.Is` fact on `errnoPathErr`
  against an `*errorString` (as `errors.IsPathErrnoNotExist.spec`, `ExistCallees.lean`). Changing
  `io.ReadFull.wp_proof`'s statement is a trust-base change: **the user's decision**.
- **Decision.** Defect 1 fixed (2026-11-14, `wal-readall16`). Defect 2: **adopted provisionally** by the
  coordinator (2026-11-14, `wal-readall17`; a trust-boundary axiom's statement changed: **pending the
  user's review**, listed in `notes/wal-fsext-plan.md` §10; kept off `lean` until reviewed).
- **Change (made, `wal-readall17`).** `io.readerStream ri S E` takes `E : List w8 → GoInterface → IProp GF`
  and returns `nil` or an error with `□ E (r ++ ys) err` (`io.errAt`); `io.ReadFull.wp_proof`'s statement
  (`Spec/io/ReadFull.lean`) returns `io.readFullRes E eof ueof r0 ys m err`:
  `⌜ys.length = m ∧ err = nil⌝ ∨ ∃ e, ⌜ys.length < m ∧ e ≠ nil ∧ (e = eof ∧ ys ≠ [] → err = ueof) ∧
  (¬ (e = eof ∧ ys ≠ []) → err = e)⌝ ∗ □ E (r0 ++ ys) e` (the old pure `readFullOk` with the evidence
  made Iris; `io.readFullRes_pure` gives the old form back). `bufio.ownReader`/`Reader.Read`,
  `FileBufReader.Read`, `readInt64` pass it on. The decoder's readers return `decRdE bs eof IoE r e :=
  ⌜decRdErr bs eof IoE r e⌝ ∗ isEofAns e eof` (each error with `errors.Is(e, io.EOF)`'s answer), its
  `FileInfo` errors `decAns`; `isEofOk` asks the answer only on `nil`, `io.EOF`, `io.ErrUnexpectedEOF`.
  The `os.File` bridge proves the answer on the model's `*PathError`s (`os.File.Read.wp_eof`'s and
  `Stat.spec`'s errors now `os.errnoPathErr err e`, `e ≠ 0`) from the hypothesis
  `errors.IsPathErrnoEof.spec` (`LinuxFs/Spec/errors/IsPathErrnoEof.lean`; true of Go, as
  `IsPathErrnoNotExist.spec`: needs `(*PathError).Unwrap`, `Errno.Is` translated). `WalDecEnvSupply` is
  then true of Go but still a hypothesis: `errors.newVar` keeps no trace of the allocation, so `io.EOF`,
  `io.ErrUnexpectedEOF` and `walpb.ErrCRCMismatch` cannot be shown distinct from the packages' facts
  (`notes/perennial-changes.md`, 2026-11-14).
## 2026-11-14: `wal.WAL.renameWAL.spec` (internal, the part's) -- the spine law cannot open the invariant

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`, `RenameWALOk`'s third
  conjunct: `∀ x, Sp -∗ renDirOut … (some x) ={⊤}=∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`.
- **Defect.** The caller (`Create`) can discharge it only with the invariant's post-commit split
  (`walInv_splitNew`, `CreateSplit.lean`), which opens `walInv` (needs `notCrashed`) and takes the lock token
  `walLockedTok` that the committed update's result `U (some x)` (`walCreateQ`) holds; the conjunct gives
  neither.
- **Evidence.** The W1 log, fourteenth session, "Not done" (1); `walInv_splitNew`'s statement.
- **Change (made).** The conjunct is `∀ x, Sp -∗ notCrashed -∗ U (some x) -∗ renDirOut … (some x) ={⊤}=∗
  notCrashed ∗ U (some x) ∗ osPathS R dir dq J ∗ osPathS R dir dq J ∗ SpR x`; `renameWAL` applies it at a
  program step after the rename (`wp_notCrashed_acc`). `dq` is fixed by `Create`.
- **Decision.** Adopted (the coordinator's decision, 2026-11-14, `wal-path15` task 3; internal spec, no client).
## 2026-11-14: `wal.WAL.renameWAL.spec` (internal, the part's) -- no bound on the directory's length

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`, `RenameWALOk`.
- **Defect.** `newFilePipeline.spec` needs `dir.length < 2 ^ 61` (its `Join`s of `dir` and `0.tmp`/`1.tmp`);
  nothing in `RenameWALOk` bounds `dir` (`osPathS` gives no length).
- **Evidence.** `renameWAL.wp_proof`'s `newFilePipeline` step (`wal-create14`).
- **Change (made).** `RenameWALOk`'s second conjunct `dir.length < 2 ^ 59` (`Create.spec`'s premise, which
  `Create` passes on).
- **Decision.** Adopted (minor, internal; `wal-create14`).
## 2026-11-14: `wal.WAL.renameWALUnlock.spec` (internal, the part's) -- unprovable as stated

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWALUnlock.lean`.
- **Defects.** (1) Its `w.Close()` flushes the encoder, fdatasyncs the tail and closes the lock fds, but the pre
  (`walPreIn`) has neither `ownEncoder` nor the tail file's ownership (`os.ownFile`/`osFd`, its writer stream):
  `Create` gives the segment to the rename's update (`walCreateP`), so a generic `U` hides it. (2) Its `Open`/
  `ReadAll` need `walAreaRes jr`, `walUnlockedTok`, `osCallPerm 1` and an `AU` on `walDirIs dir`; after a
  committed rename the lock token is in `U (some x)` (`walCreateQ`) and the client's `walDiskAt` in its `Q`, so no
  generic law gives `Open`'s `AU`. (3) After a rename that committed with an error (`o = some x`), the second
  `os.Rename(nm.tmp, nm)` has an absent source: no `os.Rename` spec covers it (`wp_osRenameAbsentS` is internal
  to `Proof/os/Rename.lean`).
- **Evidence.** `renameWAL.wp_proof` (`wal-create14`) uses the spec as a hypothesis; `WAL.sync.specPreL`'s pre;
  `Open.spec`'s pre; `os.Rename.specDirSnc`'s premises.
- **Change.** Decided by the coordinator (2026-11-14) for (1): the pre carries what `Close` consumes (the
  encoder, the tail file, the lock fds) as `Create` holds them before the rename; the first `Close` proved inline
  over `os.File.Close`, `os.File.Close.specNil` and the encoder's flush spec, not through `WAL.Close.spec`.
  **Not yet made** (`wal-create14` stopped at its context budget; `Create`'s body has not reached the encoder, so
  the exact form is open). (2) and (3) need a design: proposed, a caller-supplied law (like `Sp`/`SpR`) from the
  committed result to `Open`'s pre, which `Create` discharges by releasing the fresh WAL's lock and merging the
  names back, or a `Create`-specific (non-generic) `renameWALUnlock` spec; and a public `os.Rename` spec for an
  absent source (`ENOENT`, no effect).
- **Decision.** (1) adopted (coordinator); (2), (3) pending the coordinator.

## 2026-11-14: `wal.Create.spec` (the part's, over `fsExt`) -- the initial snapshot record's bytes

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`.
- **Defect.** `Create` writes `&walpb.Snapshot{Index: new(0), Term: new(0)}` through `SaveSnapshot`
  (S/wal.go:181), whose bytes are protobuf-go's (`snapEnc snapC0`; `SaveSnapshot.specPre` writes
  `Mr.encSnap sm` of a `walSnapAt Mr sp sm cs`, which ties the object's encoding to `Mr.encSnap`). The
  committed state `walDurFresh md` has `Mr.snap0` there (`hdrDs`). Nothing relates `Mr.snap0`, `Mr.encSnap`
  and `snapEnc`: with an arbitrary marshaller the spec's commit is false.
- **Evidence.** `Create.wp_proof`'s `SaveSnapshot` step (`wal-create15`); `WalEncRecs.lean` (`hdrDs`).
- **Change (made).** Premise `WalMarshalCreateOk Mr` (`CreateSnap.lean`: `Mr.snap0 = snapEnc snapC0 ∧
  Mr.encSnap snapC0.model = Mr.snap0`), a pure fact of the client's marshaller parameter, which the
  server meets with the real one (as `walSnapAt`'s tie, ledger 2026-11-13).
- **Decision.** Adopted (minor: a pure premise on a parameter, no ghost state; `wal-create15`).

## 2026-11-14: `wal.WAL.renameWALUnlock.spec` (internal, the part's) -- (2) Create-specific: blocked on `Open`'s update

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWALUnlock.lean`, defect (2) of the
  entry above, and the coordinator's decision (b) (make `renameWAL`/`renameWALUnlock` `Create`-specific, naming
  `walAreaRes`, `walUnlockedTok` and the client's update on `walDirIs dir`).
- **Finding (`wal-create15`).** `Create`-specific statements give `walAreaRes jr` (`Create` holds it through
  `walAreaRes_open`'s parts, merged back by `walInv_merge2` after the unminting or the commit) and
  `walUnlockedTok` (the commit's `walCreateQ` returns `walLockedTok`; `Close` of the pre-rename `w` does not
  give it back, so the retry must release it first: `walLockedTok_unlock` needs the handle's
  `walOutFrag`/`walTailsFrag`/`walNamesFrag none`, which `walCreateQ (some x)` holds). **But `Open`'s update
  cannot be built**: after the second rename commits, the client's update (`walAbsent dir` to `walDiskAt dir
  (walDurFresh md)`) has been spent (its `COMM Q` is in `walCreateQ (some x)`), and `Open.spec` asks for an
  atomic update on `∃∃ o, walDirIs dir o`, which only the client's resources open. `Create` owns no
  `walDirIs`/`walDiskAt` fragment after the commit (they are the client's, inside `Q`). So the retry's
  `Open`/`ReadAll` are provable only if `Create.spec` takes a **second client update** for the reopen
  (`AU <{ ∃∃ o, walDirIs dir o }> @ walAuMask, ∅ <{ walDirIs dir (o.map …), COMM Q' o }>`, used only on the
  retry path; on every other path returned or dropped), or if `Create`'s success arm on the retry path
  returns without the reopened handle (not what the code does).
- **Evidence.** `Open.spec`'s pre (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean`); `walCreateQ`
  (`CreateAu.lean`); `Create.spec`'s pre.
- **Change.** None made: a second client update in `Create.spec` is a change to the client's contract (the
  coordinator's / the user's decision). (3) (the second rename's absent source) and (1) (the pre carries the
  encoder and the tail file) are independent of it.
- **Decision.** Pending the coordinator.

## 2026-11-14: `wal.Repair.spec` (the part's, over `fsExt`) -- the lock token taken (plan §6 Q7)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (`wal.Repair.spec`, new): the main
  tree's axiom (`Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean`) with plan §3's binders (`walAreaOk`, the
  area's spine and `walAreaRes`, `osCallPerm 1`, the update at `walAuMask`; `Open`'s premises, as `Repair` reads
  the same directory), and `walUnlockedTok` framed.
- **Defect (of the main axiom).** It promised that `Repair` blocks on the tail's lock while a handle holds it,
  then acts as with no handle. Over `fsExt` the file locks are bookkeeping (plan §6 Q1: no lock state), so
  `LockFile` waits for nothing and a concurrent appender would race the truncation: the axiom's statement
  without the token is not provable (and with Q1's model, not true of the model).
- **Evidence.** Plan §3 ("`Repair` takes `walUnlockedTok`") and §5/§6 Q7; both callers comply: the WAL tester
  calls `Repair` after a successful `Close` (examples/etcd/wal/wal.go:192-198), `openWALFromSnapshot` before
  any `Open`.
- **Change (made).** The token in the pre and the post (framed); the "blocks until the handle's `Close`"
  scenario dropped until the lock model. Otherwise the main tree's: committed as accessed, the boolean unconstrained.
- **Decision.** Adopted (the coordinator, plan §6 Q7, 2026-11-13; stated in the W7-W12 log's fifth session).

## 2026-11-14: `wal.WAL.sync.specC` (internal, the part's) -- the post says the tail is durable

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncC.lean` (a hypothesis of
  `WAL.Close.wp_proof`, for the `sync` owner): its success post's handle `walHandleC … h'` (tail facts
  `TailMeta`: `lo = size = hi`).
- **Defect.** Too weak for `Close`'s unregistration: the invariant now requires an idle WAL's tail to be synced
  (`TailSynced`, `TailIdle`'s third part: every byte durable, zeros known only past the end; plan's W7-W12 log,
  sixth session), so that `Close` of an unread handle can fdatasync an unregistered tail without changing the
  invariant. `TailMeta` says nothing of the bytes.
- **Evidence.** `sync`'s last step is `fileutil.Fdatasync(w.tail().File)`, whose success post is the synced
  `OsMeta` and the bytes `bs.map durB` (`fileutil.Fdatasync.wp_tail`, `TailFdatasync.lean`).
- **Change (made).** The post's handle is `walHandleC … h' TailMetaS` (`TailMetaS m bs := TailMeta m bs ∧ ∀ y ∈ bs,
  y = durB y.1`, `CloseHandle.lean`; `TailMetaS.of_sync` from `TailMeta m bs` to the synced pair). `WalCloseLaw`
  takes `TailMetaS`; `WAL.Close.wp_proof` unchanged.
- **Decision.** Adopted (the coordinator's `TailSynced` decision, 2026-11-14).

## 2026-11-14: `wal.WAL.cut.spec` (internal, the part's) -- the history nonempty at a cut

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cut.lean` (`WAL.cut.spec`, a hypothesis of
  `WAL.Save.wp_proof`, proved by `WAL.cut.wp_proof`).
- **Defect.** Too weak for `ReadAll`: its premise `walCutPos (h.H.map toM) |H|` allows `|H| = 0`, so a cut at
  position 0 could enter the invariant's layout; `ReadAll` from a cut file reads past a nonempty prefix
  (`readAll_ok_pure`'s `hk0`), and a cut at 0 would make that prefix empty (W3/W5 log, fourteenth to sixteenth
  sessions: the cuts' positivity).
- **Evidence.** `cut`'s only caller, `Save` (S/wal.go: `if curOff < SegmentSizeBytes { ... return nil }; return
  w.cut()`), cuts after appending a save record: its history is `H ++ [save]`, nonempty.
- **Change (made).** The premise `0 < h.H.length` after `walCutPos`; the invariant's `WalAbsD.cutPos` (every cut
  `> 0`, `CutLay` from the premise, the crash keeping the cuts). `WAL.Save.wp_proof` supplies it.
- **Decision.** Adopted (eighteenth W3/W5 session, minor: a premise its one caller meets; no client-visible
  change, `cut` is unexported).

## 2026-11-14: minibolt's `DB.init.spec`/`DB.init.specCrash` (the part's example) -- the post's `cz`; `os.File.WriteAt.specCrashS` -- the bytes written

- **Spec.** `LinuxFs/Spec/.../examples/osfs/bboltfs/DB__init.lean` (post: `({ m with size := max m.size 16384 }).synced`),
  `DB__initCrash.lean` (`initDoneMeta`, the same); `LinuxFs/Spec/os/CrashSt.lean`'s `os.File.WriteAt.specCrashS`
  (success post: the bytes written, the size, but not how far the loop got, `nn`).
- **Defect.** Since `wal-save16` (the extension's `pwCz`) a complete `pwrite` whose end reaches the zeros known
  raises `cz` to its end's page, so `init`'s first write (16384 bytes at 0) leaves `cz = pwCz m 0 16384 16384`,
  not `m.cz`; the later metas' writes (inside the first four pages, below the zeros a sync made known from the
  size on) leave it. The posts stated the old `cz`: false. `specCrash`'s proof also needs the loop's end state to
  be a completed `WReach` (`nn = |data|`), which `specCrashS`'s success post did not say (its proof had it, `hfk`).
- **Change (made).** Both posts' `OsMeta` is `({ m with size := max m.size 16384, cz := pwCz m 0 16384 16384 }).synced`;
  `specCrashS`'s success post gains `nn = data.length` (proved; `WReach.czInv`/`WReach.cz_done`: a completed
  `WriteAt`'s `cz` is one complete write's, `pwCz m off |data| |data|`; `pwCz_eq_of_lt`, `synced_zf_ge`, all in
  `CrashSt.lean`). Clients (`Open`, `OpenCrash`, `DB.commit.wp_proof_crash`) repaired; no other user.
- **Decision.** Made (`wal-save17`, the coordinator's task 1: the posts' `cz` as `pwCz m 0 16384 16384`).

## 2026-11-14: `WalDecEnvSupply` and `walReadH` -- no I/O error is `nil`

- **Spec.** `openAtIndex.lean`'s hypothesis `WalDecEnvSupply` (the decoder's environment: `∃ IoE eof ueof,
  decEnv IoE eof ueof ∗ ⌜∀ pe, IoE (*PathError pe)⌝`) and the sealed `walReadH` (`ReadDefs.lean`), which keeps
  the decoder's `IoE` existential.
- **Defect.** Too weak for `ReadAll`: `decoder.Decode`'s post (`decPostB`) has an I/O-error arm `⌜IoE err⌝` with
  the decoder no longer live; nothing excluded `IoE nil`, so at `err == nil` the loop (S/wal.go:523) would go on
  into its body with a dead decoder and an unknown record (the next `Decode` needs a live one): the loop's
  invariant is not provable.
- **Evidence.** The readers' errors are `*PathError`s (`os.File.Read`, `Stat`): `nil` is none of them. The
  decoder's own code returns a reader's error only under `err != nil`.
- **Change (made).** `WalDecEnvSupply`'s pure part `(∀ pe, IoE (*PathError pe)) ∧ ¬ IoE nil`; `walReadH`'s
  `decEnv IoE eof ueof` is `(decEnv IoE eof ueof ∗ ⌜¬ IoE nil⌝)`; `openAtIndex` passes it through. (The
  alternative, `err ≠ nil` in `decPostB`'s I/O arm, would reprove the decoder's specs.)
- **Decision.** Adopted (`wal-readall20`, minor: a hypothesis true of Go, and a sealed body; no client-visible change).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's; a hypothesis of `wal.Create.wp_proof`) -- nothing about the new directory's history

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `fileutil.CreateDirAll.specTmp`
  (not proved; `CreateDirAll.spec`, proved, is its `name`-absent case).
- **Defect.** Too weak for `Create`'s commit: `walCreate_osAUnc`'s `hJC` asks that after **any** crash of `J`'s
  claim (`hJ.valAfter J K`, every `K`) the only `.wal` file is the new segment's. The success post says only
  `hJ.cur = ∅`; a history with older `.wal` values of `J`'s names (an inode reused, or an existing `nm.tmp`
  emptied earlier in the generation) would make `hJC` false.
- **Evidence.** `Create.wp_proof`'s commit (`wal-create16`): `createJ_*` (`CreateJ.lean`) derive `hJC`, `hsn` and
  the layout's `walInos` from the merged claim of `J`, given that `J`'s claim, as `CreateDirAll` returns it, has
  no name at any crash (`valAfter … = none`).
- **Change (made).** The success post gains `∀ K b, hJ.valAfter J K b = none`. True of the directory `CreateDirAll`
  creates (its `mkdir`'s claim, `TreeShared`'s `hJ.cur = ∅ ∧ hJ.next = x + 1`: a fresh inode, nothing logged on
  it before the `mkdir`, which writes it empty), which the extension's `mkdir` law does not yet say (an allocator
  fact: `st.fs.nextIno` above every inode the log writes): **obligation for the extension's owner** (the `mkdir`
  law's post, then `CreateDirAll.spec`'s and `specTmp`'s). The existing-directory case of `specTmp` (an empty
  leftover `nm.tmp` that `Exist` missed) needs an argument too: the leftover's history in the generation must not
  hold a `.wal` value, or `walCreate_osAUnc`'s `hJC` be weakened to the crashes that keep `J`'s entries committed
  before the rename (`syncDir(nm.tmp)`'s `osCommitLb`, `Create`'s `Hcm1`, unused so far), which needs the
  invariant's commit bound compared with the program's. Open.
- **Decision.** Made, minor and internal (`wal-create16`): a hypothesis's post strengthened; its truth is an
  obligation recorded here and in the W4 log's eighteenth session.
  **Superseding direction (the coordinator, decided; `wal-create17`, not yet made)**: limit `hJC` to the
  crashes that keep `J`'s entries (`∀ y e E, (y, e, E) ∈ hJ.ents → K y`), under which `hJ.valAfter J K b =
  hJ.cur !! b`; `walCreate_osAUnc` then takes `osCommitLb m` with `J`'s entries below `m` (`syncDir(nm.tmp)`
  gives `osCommitLb n` for any `osLogLb n`: pass `J`'s claim's `next`) and raises the invariant's commit
  bound to `max n m` at the commit (`walsOk_mono`, `walsNamed_mono`, `absentNone_mono`, as `walInvBody_named`
  does), so every `RegionCrashedK` it quantifies over keeps them; then the post's `valAfter … = none` is
  dropped from `specTmp` (no allocator fact). Note also that `Create` removes an existing `nm.tmp` before
  `CreateDirAll`, so only `specTmp`'s `mkdir` case is reached.

## 2026-11-14: `wal.WAL.renameWAL.spec` / `renameWALUnlock.spec` (internal, the part's) -- the error arms lose the lock file and the spines

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean` (`renameWALPost`, arms 3 and 4),
  `WAL__renameWALUnlock.lean`; decisions (1) and 2b of the entries above.
- **Defect.** Too weak for `Create`'s exits after the call (`wal-create16`, which reaches them: `Create` now calls
  `renameWAL` with every `RenameWALOk` law discharged). On `renameWAL`'s error `Create` returns at once, and its
  deferred `f.Close()` (`retErr ≠ nil`) runs on the lock file: arm 3 (`walPreIn … ∨ emp`) and arm 4 (nothing)
  do not say whether `f` is still open (`os.ownFile`/`osFd`, as `Create` framed them around the call) or was
  closed by `renameWALUnlock`'s `w.Close()` (then the deferred close is a second close of a closed `*os.File`,
  which needs its own `os.File.Close` spec: `ErrClosed`, no effect; none exists). Arm 4 also drops the two spines
  to `dir` that the spine law made (`osPathS R dir dq J`, fractions of the area's spine and of `nm`'s claim), so
  `Create` cannot give back the area's spine fraction it lent (`osPathS R r (own qp) jr` in `Create.spec`'s post).
- **Evidence.** `Create.wp_proof`'s frontier `sorry` after `renameWAL` (`Create.lean`); `renameWALPost`.
- **Proposed change** (with (1), the pre carrying what `Close` consumes): the pre takes the encoder, the tail file
  (`os.ownFile f fd …`, `osFd`, `os.ownOff`) and the tail's lock (`fileutil.lockedFile lt f` is in `walPreIn`);
  arm 1 returns them; arms 3 and 4 return them open (the rename failed before `renameWALUnlock`'s `Close`, or
  `OpenDir` failed after a committed rename) or a closed-file token for the deferred `f.Close()` (a spec
  `os.File.Close.specClosed` to add: a closed `*os.File` returns an error and changes nothing); arm 4 returns the
  two spines (`osPathS R dir dq J ∗ osPathS R dir dq J`, for `osPathS_unchild`). Arm 2 (the retry's reopen) as
  decided in 2b: proved over `Create`'s held resources (`createU (some x)`: `walLockedTok`, `walOutFrag`,
  `walNamesFrag (some dir)`, the segment's halves), its `Open`/`ReadAll` through variants of `walInv_openAt`
  without the client's update (the open position of index 0 leaves `unl`, so no commit is needed; the
  state from `walCreateQ`'s `walPast`), and its success arm adding `walLenLb w' dir 0 ∗ walSyncedLb dir 0`
  (`Create.spec`'s success post). Not yet made.
- **Decision.** Adopted in part (`wal-create17`, the coordinator's task 1, decided). **Made**: the pre takes
  `walLockIn e f fd fname d c off` (the empty encoder, the segment's `*os.File`, its fd and descriptor, its
  offset); arm 1 returns it; arms 3 and 4 return `walLockLeft f fd fname d` (open: `os.ownFile f fd`,
  `osFd`; or closed by `renameWALUnlock`'s `Close`: `os.ownFile f (-1)`), and arm 4's case list names the
  retry's failed `Open`/`ReadAll`; `renameWALUnlock.spec`'s pre the same; `renameWAL` re-proved. The second
  close is `os.File.Close.specClosed` (`LinuxFs/Spec/os/File__CloseClosed.lean`): **not provable from the
  model** (`File.Close.impl` asks `FdKind(-1)`, stuck on a closed fd), a hypothesis of `Create.wp_proof`;
  proposed trusted change (pending the user): the model returns Go's `&PathError{"close", name,
  ErrClosed}` on fd -1. **Changed from the proposal**: arm 4 does not return the two spines (one stays
  with the pipeline `renameWAL` started, which an error leaves running, so `Create` could never give the
  caller's area spine back); instead their area part is the invariant's lend (`walInv_areaPath`,
  `AreaPath.lean`), and `Create`'s caller's spine is never lent. **Not made** (arm 2): as stated it is
  unprovable (`walOpenWF` holds `walNamed dir` and `walNamesFrag none`, which only `Create`'s parent fsync
  and registration give, after `renameWAL` returns; and `U (some x)` holds the lock token the handle holds
  too, so the arm is contradictory for `Create`, which does not use that). It needs a handle before
  naming (`walDirH` without `walNamed`, with `walNamesFrag (some dir)`), which `Create`'s arm 1 would build
  too, both then going through the parent fsync and the registration: not designed. `Create` leaves arm 2
  a `sorry`.

## 2026-11-14: `os.File.Truncate.specAu` (the part's, `LinuxFs/Spec/os/File__TruncateAu.lean`) -- the outcome's `tc` domain

- **Spec.** `os.ftDoneH`/`os.ftUndoneH`, the caller's halves of a truncate's outcome in `os.File.Truncate.specAu`'s
  post (and so in the fileutil `Au` specs over it: `preallocExtendTrunc.specAu`, `ZeroToEnd.specAu`): `∃ tc rz,
  osMeta ½ (… .withTc tc rz)`, the candidates known past the size existential.
- **Defect.** Too weak for the WAL's `os.File.Truncate.specWalTail`: its post's `TailMetaW` includes `TailZ` (the
  candidates of every byte between the size and the known zeros known, `wal-save16`), which the caller cannot
  derive from an unknown `tc`; the supply (`walInv`) knows it is `rsTail`, but nothing carries the fact out (an
  invariant opening outside an atomic step has no `notCrashed`). W1 log, nineteenth session, last item.
- **Evidence.** Every outcome the extension leaves for a file with no sync cut (the WAL's segments: `WalsOk`'s
  `cut = none`) has `tc = rsTail …` (`rsPostK true`, `rsUnMeta true`); `TcKnows.rsTail`.
- **Change (made, `wal-tc10`).** `os.ftDoneH p m tg zs` carries `⌜TcKnows m tg tg tc⌝`, `os.ftUndoneH p m tg xs'`
  `⌜TcKnows m tg m.size tc⌝` (`TcKnows m tg sz' tc := ∀ b, (rsTail true m tg sz' 0 [] !! b).isSome → (tc !!
  b).isSome`, `LinuxFs/Proof/os/TcKnows.lean`: the domain of the outcome's `rsTail`, landed at `tg` or not at the
  old size). A strengthening of the post; a supply (only the WAL's, not yet written) must prove it, which a supply
  for a file with a sync cut could not (its outcome keeps the announcement's `tc`): none exists. The retry loop
  carries it (`TcKnows.of_announce`, `TcKnows.of_rsPost`). The proposal had one `TcKnows m tg tc`; the not-landed
  outcome keeps no candidates of the bytes in `[tg, size)` (below its size), hence the size argument.
- **Decision.** Adopted (the coordinator's task list for `wal-tc10`, "decided").

## 2026-11-14: `fallocDoneH` (the part's `syscall.Fallocate` updates, `LinuxFs/Proof/syscall/FallocateAu.lean`) -- the growth's `tc` domain; `ZeroToEnd.specAu`'s post

- **Spec.** `fallocDoneH i m tg w` (the caller's halves of a growth landed with the size `w`, in `fallocOutH`, the
  share `fallocSup` hands back, and so in `preallocExtend.specAu`/`Preallocate.specAu`/`ZeroToEnd.specAu` through
  `preGrownH`): `∃ tc rz, osMeta ½ ((rsPost false m tg w).withTc tc rz) ∗ …`, `tc` existential, as `os.ftDoneH` was
  before `wal-tc10`.
- **Defect.** Too weak for `ReadAll`'s `ZeroToEnd` instance, whose post must give the tail's `TailZ` (the candidates of
  every byte between the size and the known zeros known): after the growth back to the size the caller cannot tell
  which bytes past it have known candidates (I3b, `wal-tc10` entry, last item).
- **Evidence.** The outcome the extension leaves for a file with no sync cut has `tc = rsTail false m tg w n []`
  (`rsDoneK true false`, `wp_osFallocFinishK`); `TcKnowsF.rsTail`.
- **Change (made, `wal-tc11`).** `fallocDoneH` carries `⌜TcKnowsF m tg w tc⌝` (`TcKnowsF m tg sz' tc := ∀ b,
  (rsTail false m tg sz' 0 [] !! b).isSome → (tc !! b).isSome`, `TcKnows`' growth form, in `FallocateAu.lean`). No
  supply exists yet (the WAL's, `fallocSup` at the tail, is the first); `fallocDoneH_preGrownH` drops it. The undone
  arm of `fallocOutH` is the exact announcement (`rsUndone false`), unchanged: see the obligation below.
- **Proposed, not made (needs `preGrownH`'s fact first): `ZeroToEnd.specAu`'s success post** gains
  `⌜ZteMeta m m'⌝`, `ZteMeta m m' := (∀ b, m.size ≤ b → (m.pc b).isSome → (m'.pc b).isSome) ∧ m.cz ≤ m'.cz ∧ ∀ z0,
  m.zf = some z0 → ∃ z', m'.zf = some z' ∧ z0 ≤ z' ∧ z' ≤ max z0 (pageEnd m.size)` (with `TailZ m` it gives `TailZ m'`,
  the size and `pageEnd m.size ≤ m'.cz` given). Its proof chains `TcKnows` (the truncate to `o`, landed), `TcKnowsF`
  (a partial or full `fallocate`) and `TcKnows` (the fallback's truncate): `preGrownH` (`DefsAu.lean`) must carry
  the pc-domain and `zf` facts through `preGrownH_trans` (`Preallocate.specAu`'s post), a change to
  `preallocExtend.specAu`/`Preallocate.specAu` and `filePipeline.alloc`'s use of `preGrownH`.
- **Decision.** `fallocDoneH`'s fact adopted (the coordinator's task list for `wal-tc11`, "decided"). `ZteMeta`
  adopted (the coordinator's task list for `wal-tc12`, "decided") and **made, simplified** (`wal-tc12`): `ZteMeta m m'
  := PcKeep m m' ∧ (m.ZfGe → m'.ZeroPg)` (`DefsAu.lean`; `PcKeep m m' := ∀ b, m.size ≤ b → m'.size ≤ b → (m.pc
  b).isSome → (m'.pc b).isSome`, `LinuxFs/Proof/os/PcKeep.lean`). `wal-save18`'s `ZeroPg` (zeros known from `z ≥ size`
  with `pageEnd z ≤ max size cz`) replaces the proposal's `zf` bound and `cz` clause: with `TailZ m` (which gives
  `ZfGe m`, and `m.pc` known at every byte past the size) and `m'.size = m.size`, `ZeroPg m'` and `PcKeep` give `TailZ
  m'`. Carried by **`preGrownH i m w Z`** (as `wal-save18`'s `preGrown`: `PcKeep m m'` always, `Z → m'.ZeroPg`),
  so `preallocExtend.specAu`'s post is `preGrownH … (err = nil ∧ m.ZeroPg)`, `preallocExtendTrunc.specAu`'s `(err = nil
  ∧ m.ZfGe)`, `Preallocate.specAu`'s (`preallocPostH`) `(err = nil ∧ m.ZeroPg)`, as the whole specs'. `PcKeep` from each
  outcome's `TcKnows`/`TcKnowsF` (`PcKeep.of_tc`); the undone `fallocate` arm of `fallocOutH` became `∃ tc rz,
  ⌜TcKnowsF m tg m.size tc⌝ ∗ osMeta ½ ((m.announce …).withTc tc rz)` (the extension's `rsOutF` undone arm
  `rsUndoneK m.cut.isNone false`, `wal-tc12`), which the obligation above asked for.

## 2026-11-14: `fileutil.Preallocate`/`preallocExtend`/`preallocExtendTrunc` (the part's) and `os.OpenFile.specCreateTruncS`'s `trFile` -- the zeros known on success

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/{Preallocate,preallocExtend,preallocExtendTrunc}.lean`
  (posts: `preGrown i m w`); `LinuxFs/Spec/os/OpenFileTruncS.lean`'s `trFile i P` (the new or `O_TRUNC`-truncated file).
- **Defect.** Too weak for `filePipeline.alloc` (`pipeFile`'s `ZeroPg`, W6 log, sixteenth session): neither post said
  anything of the zeros known (`zf`) or the page cache known zero (`cz`), so `alloc`'s `ZeroPg` was a `sorry`. It was not
  provable from stronger posts alone either (seventeenth session): a `fallocate` landing left `cz` behind the zeros
  it announced, and an `O_TRUNC` of an arbitrary leftover gave no zeros fact.
- **Evidence.** Linux keeps no page past the size's last page (the page cache reads zeros there); the extension now
  says so (`MetaOk.ce`, untrusted ghost), and a landed resize raises `cz` (`rsCz`: an `ftruncate` to past the zeros
  known and its announcement's end; `fallocate`'s growth when the old size's page was known zero). Then an
  `ftruncate` landed makes `ZeroPg` (from `ZfGe`), `fallocate`'s growth landed keeps it; a resize that did not land
  keeps neither (its `OsMeta` is the announcement's, unchanged, so that the WAL's layouts stay `rsUnMeta`).
- **Change (made).** `preGrown i m w Z` (a condition `Z`: the grown `OsMeta` has `ZeroPg` if `Z`; `GrowMeta` keeps
  `ZfGe`): `Preallocate`/`preallocExtend` post `Z := err = nil ∧ m.ZeroPg`, `preallocExtendTrunc` `Z := err = nil ∧
  m.ZfGe`. `trFile i P` gains `m.ZfGe ∧ (P → m.ZeroPg)` (not unconditional `ZeroPg`, as proposed: a leftover from
  `alloc`'s error path after a `fallocate` that did not land has none). `alloc`'s `ZeroPg` proved; `zerosA_trFile`
  takes `ZfGe` (`filePipeline.run`, from `pipeFile`'s `ZeroPg`).
- **Decision.** Made (`wal-save18`, the coordinator's task 1, `rsCz`; the shape adjusted as above and logged).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- the `valAfter` clause and `.touch`

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `fileutil.CreateDirAll.specTmp`
  (the success post's `∀ (K : Nat → Prop) (b : GoString), hJ.valAfter J K b = none`, added by the 2026-11-14 entry
  above).
- **Defect.** False, also in the case the entry above took for true (`CreateDirAll` makes the directory):
  `CreateDirAll` runs `TouchDirAll`, whose `IsDirWriteable(J)` writes `J/.touch` and removes it
  (`fileutil.go`), through `J`'s claim (`IsDirWriteable.spec` takes `osNames J (.only [.touch]) 1`), so the returned
  `hJ.ents` hold the create and the remove of `.touch`; with `K` keeping the create's index and not the remove's,
  `hJ.valAfter J K .touch` is the file, not `none`. The clause quantifies over every `K`, and the claim's history
  cannot be dropped, so no proof exists.
- **Evidence.** `NamesH.valAfter` (`GooseLang/Ext/Fs/NamesGhost.lean`: the last kept entry writing `b`);
  `IsDirWriteable.spec`'s post (`LinuxFs/Spec/.../fileutil/IsDirWriteable.lean`). Found proving the inventory's leaf
  specs (`wal-leaf1`, plan §8 "Leaf specs log").
- **Proposed change.** None new: the coordinator's superseding direction in the entry above (limit `hJC` to the
  crashes keeping `J`'s entries, drop the clause from `specTmp`) removes the false clause; this entry is one more
  reason for it (a clause restricted to `b ≠ .touch` would instead need the extension's allocator fact).
- **Decision.** Recorded only (`wal-leaf1`); the restatement is `wal-create17`'s.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the files left behind are lost

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean`, `decoder__decodeRecord.lean`,
  through `decPostB` (`LinuxFs/Proof/.../wal/DecDefs.lean`): the record and stop arms give the decoder live over
  `fs.drop k`, the files it has not left.
- **Defect.** Too weak: the `k` files the decoder leaves (`d.brs = d.brs[1:]`, decoder.go's `decodeRecord` at a
  file's end) are dropped from the post with their readers' stream states (`F.S`, for the WAL's segments
  `walFileS`: the open file, its offset and the program's halves of the segment). At `io.EOF` the decoder has left
  every file (`goDecode`'s last-file `.eof` stop returns `[]`), so `ReadAll` (S/wal.go:622-670) cannot `Seek` its
  tail, `ZeroToEnd` it or build the encoder on it, and cannot give the other segments' halves back to the invariant.
- **Evidence.** `decPostB`'s `∃ k, … ownDecoder d IoE eof (fs.drop k) …`; `goDecode_eof_last`; found at `ReadAll`'s
  phase 3 (`wal-readall22`, W3/W5 log, twenty-second session).
- **Proposed change.** `decPostB`'s first arm `∃ k, ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ match …`: the left files'
  streams given back (no change to the I/O and `GoFail` arms, whose decoder is dead). Callers: `ReadAll`'s loop keeps
  them (`fs.take kD`).
- **Decision.** Made (`wal-readall22`): no client-visible ghost state (the streams are the caller's own resources,
  lent to the decoder by `NewDecoder`'s spec).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` / `walCreate_osAUnc` (internal, the part's) -- the clause dropped, the commit bound raised

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean` (`specTmp`'s success post);
  `walCreate_osAUnc` (`CreateAu.lean`), `walsNamed_create` (`CreateKeys.lean`), `createFresh_osAUnc`, `createU_none`,
  `createJ_claims` (internal lemmas).
- **Defect.** The two entries above: `specTmp`'s `∀ K b, hJ.valAfter J K b = none` is false (`.touch`), and was there
  only for `walCreate_osAUnc`'s `hJC` over every crash of `J`'s claim.
- **Evidence.** The entries above; `ClaimCoh` (`Cut.lean`: with every entry kept, `valAfter = cur`).
- **Change (made, `wal-create18`, the coordinator's direction).** The clause is dropped from `specTmp` (nothing
  relies on it). `walCreate_osAUnc` takes `osCommitLb m` (a wand argument) with `J`'s entries below `m` (`hJm : ∀ xe
  ∈ hJ.ents, xe.1 < m`) and raises the invariant's commit bound to `max n m` at the commit (`walsOk_mono`,
  `absentNone_mono`, `walsNamed_mono`, the new `dirKeysOk_mono`); `hJC` is now `SegsNamedC lay.segs hJ.cur` (the
  claim's names now), and `walsNamed_create` gets every crash's `J`-names from `ClaimCoh` (each crash the claims
  allow at the raised bound keeps `J`'s entries). `Create` passes `syncDir(nm.tmp)`'s `osCommitLb` at `max
  (J's claim off the segment's name).next (x0 + 1)` (`osNames_next`, `crOut_logLb`), and `createJ_claims` returns
  the entries bound of the claim off the pipeline's names (`ClaimCoh` of the merged claim, `osNames_merge`'s
  `next`) instead of `createJ_val` (deleted).
- **Still open for `specTmp`'s proof** (the `wal-leaf1` finding): a narrower error post, and the existing-directory
  case: it stays, since `Create`'s `RemoveAll(nm.tmp)` returning `nil` gives only `tmpDirH` (`wp_removeAllTmp`,
  `os.RemoveAll.specDirS`), not the name's absence; restricting `specTmp`'s pre to an absent name would need
  `RemoveAll`'s success post to give absence (arguable since the extension's `ENOENT` decision, not made).
- **Decision.** Made (the coordinator's, decided; internal, no client-visible change).

## 2026-11-14: `os.truncSup` / `os.File.Truncate.specAu` (the part's, Lean-first) and `walTailW` -- the caller's property of the start state

- **Spec.** `LinuxFs/Spec/os/File__TruncateAu.lean` (`os.truncSup`, `os.File.Truncate.specAu`); `walTailW`
  (`LinuxFs/Proof/.../wal/Handle.lean`, the handle's tail, internal).
- **Defect.** The truncate at the tail's write position (`cut`'s, `os.File.Truncate.specWalTail`, whose pre is a tail
  that may be in a window) needs `lo ≤ wr` of a window for its first step's crash condition (`crashOkA_rzStart`):
  the crashes of size in `[wr, lo)` are new. The invariant kept it (`WalAbsD.winLo`), but it is false of a write past
  the size from an exact tail (W6 log, twentieth session, finding 1), so the writer past the size could not be
  proved. The supply (`os.truncSup`) quantifies over every state and could not be told the handle's fact.
- **Evidence.** W6 log, twentieth and twenty-first sessions (findings 1 and B); option (A).
- **Change (made, `wal-save22`).** `os.truncSup K p tg P` (`P` defaults to `True`) tells the supply `m0.lo ≤ tg ∨ P
  m0` of each attempt's state; `specAu` takes `P` and `P m` of the state it starts from (every later attempt starts
  from a state an attempt announced or landed, `lo ≤ tg`: `os.announce_lo_le`, `os.rsPost_lo_le`). The four fileutil
  AU specs keep the default (their proofs pass `fun _ => True`). `walTailW`'s pure facts gain `LoWr m (o0 + |out|)`
  (no window open, or `lo ≤` the write position); `walTail_truncSup` takes `P := LoWr · wr`. The invariant's
  window branch (`WinLast`) has `WinHead` in place of `lo ≤ wr` (internal).
- **Decision.** Made (the coordinator's option (A), decided; internal, no client-visible change).

## 2026-11-14: `os.ftDoneH` / `os.ftUndoneH` (the part's, Lean-first) -- the candidates' values past the old size (`TcFrom`)

- **Spec.** `LinuxFs/Spec/os/File__TruncateAu.lean` (`os.ftDoneH`, `os.ftUndoneH`, the caller's halves of a
  truncate's outcome); `TcFrom` (`LinuxFs/Proof/os/TcKnows.lean`).
- **Defect.** The caller learns only which bytes past the size have known candidates (`TcKnows`), not what they
  are, so after `cut`'s truncate the handle cannot know that nothing but zeros is known past `hi` (`PastZ`, W6
  log, twenty-second session), which the writer past the size needs of the bytes it grows over.
- **Evidence.** `rsTail`: past the old size a truncate's outcome knows `m.pc b ++ [(0, n)]` or the announcement's
  `tc` (a subset of `m`'s); the caller cannot see either through its half.
- **Change (made, `wal-save22`).** Both posts' pure fact is `TcKnows … ∧ TcFrom m (max m.size tg) tc rz`: `rz`
  keeps `m.rz`, and each candidate of `tc` from `max size tg` on is one `m.pc` knew or a zero stamped 0 or with a
  stamp of `rz`. Proved for the WAL's supply (`TcFrom.rsTail`) and carried by the retry loop (`TcFrom.trans`);
  consumers (`DefsAu`, `ZeroToEndAu`, `preallocExtendTruncAu`, `TruncWalTail`) take `.1`. `fallocDoneH` unchanged
  (no user needs it yet).
- **Decision.** Made (internal, weaker-or-equal knowledge given to the caller; no client-visible change).

## 2026-11-14: `os.File.Close.specClosed` (the part's, `LinuxFs/Spec/os/File__CloseClosed.lean`) -- the package's initialization

- **Spec.** `os.File.Close.specClosed` (a closed `*os.File`'s `Close`), and `wp_lockedCloseLeft`
  (`CreateLockedLeft.lean`, internal), which calls it.
- **Defect.** Over the closed-file model (`File.Close.impl` returns `&PathError{"close", name, ErrClosed}` on fd -1,
  `wal-create18-closewip`), the result loads `os.ErrClosed`, whose points-to (and the error's `fmtErrorOk`) only
  `isPkgInit pkg_id.os` gives (`os.errClosed_of_pkgInit`); the pre had none, so the spec was unprovable over the new
  model too.
- **Evidence.** The proof attempt (`LinuxFs/Proof/os/File__CloseClosed.lean`); `os.File.Close.specNil`, which returns
  `os.ErrInvalid`, takes the same premise.
- **Change (made, `wal-create19`).** The pre gains `isPkgInit pkg_id.os` (persistent; `Create` has it from `wal`'s
  dependencies, `Hos`); `wp_lockedCloseLeft`'s pre the same. The spec is proved (`os.File.Close.wp_proofClosed`).
- **Decision.** Made (internal, no client-visible change).

## 2026-11-14: `wal.WAL.renameWAL.spec` / `renameWALUnlock.spec` (internal, the part's) -- arm 2 over the handle before naming

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean` (`renameWALPost`'s arm 2),
  `WAL__renameWALUnlock.lean`; the "error arms" entry above, its "Not made (arm 2)".
- **Defect.** Arm 2 (`renameWALUnlock`'s retry returned a reopened WAL) was `U (some x) ∗ SpR x ∗ walOpenWF P Mr w'
  dir ∗ walNamed dir ∗ walPurgeW w' dir`: contradictory for `Create` (`createU (some x)`'s `walCreateQ` and the
  handle's `walOpenW` both hold `walLockedTok`) and unprovable (`walNamed` needs the parent's fsync, which
  `Create` does after `renameWAL` returns), and not where arm 1 leads `Create` (a handle it must still name).
- **Evidence.** `Create.wp_proof`'s arm-2 `sorry` (`Create.lean`); `walCreateQ` (`CreateAu.lean`); `walOpenW`
  (`Ghost.lean`).
- **Change (made, `wal-create20`).** The handle before naming, `walOpenWFU P Mr w dir` (`Handle.lean`, sealed):
  `walOpenWF` with `walDirH`'s naming fact a parameter (`nmd`, default `walNamed dir`; `emp` here), the
  registration done (`walNamesFrag none`: `walInv_register` needs no naming, and the retry's `Open` needs the lock
  token back, which needs the registration first). Laws (`HandleUnnamed.lean`): `walOpenWF_unnamed`,
  `walOpenWFU_named` (with `walNamed dir`), `walOpenWFU_dirAcc`. Arm 2 is `∃ x, UH x ∗ walOpenWFU P Mr w' dir ∗
  walPurgeW w' dir`, `UH : Nat × Nat → IProp GF` a new parameter of `renameWALPost`, `renameWAL.spec`,
  `renameWALUnlock.spec`: the caller's residue once the handle holds its share. `Create`'s is `createUH`
  (`CreateRename.lean`: `Q`, the fresh past state, a fraction of the new name's claim with the rename its last
  writer, `osLogLb (x.1 + 1)`, the absent `nm.tmp`'s claim, the area's split record with `nm`), which arm 1
  reaches too; `createSpR` now carries the last-writer fact and the log bound (from `renDirOut`'s `logOut`,
  `lastWrite_log_restrict`). Supersedes the "error arms" entry's suggestion (`walDirH` with `walNamesFrag (some
  dir)`).
- **Obligation.** `renameWALUnlock`'s proof needs a `RenameWALOk` law turning `U (some x) ∗ SpR x` (and what
  `Create` lends through `Sp`: the split record, for the registration) into `UH x` and the reopen's resources
  (`walUnlockedTok` after the registration and `walLockedTok_unlock`): to design with its `Open`/`ReadAll`
  variants (the "(2) Create-specific" entry above).
- **Decision.** Made (internal, no client: `renameWAL` is `Create`'s; the coordinator's task 1, `wal-create20`).

## 2026-11-14: `wal.WAL.SaveSnapshot.specPre` (internal, the part's) -- the indices after the call

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__SaveSnapshotPre.lean`.
- **Defect.** The post returned `walPreIn … snapi' enti'` for some `snapi' enti'`, nothing said of them; `Create`'s
  handle (`walHandleIn`) needs `max enti snapi + 1 < 2^64` of the fields it returns.
- **Evidence.** The pinned `SaveSnapshot` raises `w.enti` and `w.snapi` each to the snapshot's index if below it
  (the translation, `WAL.SaveSnapshot.impl`). `Create.wp_proof`'s arm 1 (`wal-create21`).
- **Change (made, `wal-create21`).** The post adds `⌜(snapi' = snapi ∨ snapi' = sm.Index') ∧ (enti' = enti ∨
  enti' = sm.Index')⌝` (every arm); the proof unchanged but for the fact.
- **Decision.** Made (internal; strengthening a post).

## 2026-11-14: `walCreateQ` / `walDirH` (internal, the part's) -- the tail registered at the commit; the tail's name

- **Definitions.** `walCreateQ` (`CreateAu.lean`), `walDirH` (`Handle.lean`).
- **Defect.** (1) `walCreateQ`'s committed arm gave `walTailsFrag ∅`, the handle to register its tail later. A
  later registration (`walTailsRes_register`, inside `walInv`) finds the invariant's history and layout only up to
  `WalAbsD` (no step after the commit pins them to the fresh WAL's), while the handle's encoder CRC and file offset
  are the fresh WAL's: the tail record's `H`/`md`/`cuts`/`wr` could not be shown to match. (2) `walDirH` asked the
  tail file's name to be `child dir nm0`; `Create`'s segment was opened as `dir.tmp/0000…0000.wal`, and Go's
  `f.Name()` keeps that path after the rename.
- **Change (made, `wal-create21`).** (1) The commit registers the tail (`walTailsRes_register` on the new layout,
  `createLay_tailBound` its record boundary): `walCreateQ`'s committed arm holds `walTailReg dir t` (the holder's
  half of the tails' authority `{dir ↦ γ}`, the key, the tail record's half `t`), `t` a new parameter
  (`createTailG Mr md jr nm J g` from `createU`). (2) `walDirH`'s name fact is `∃ pd, name = child pd nm0` (`cut`'s
  `w.seq()` reads only the base, `baseModel_child_walFileName`).
- **Obligation.** `renameWALUnlock`'s `RenameWALOk` law (the retry's `w.Close()` and the reopen) now unregisters the
  tail too (`walTails_unregister`, `Close`'s).
- **Decision.** Made (internal, no client-visible change).
## 2026-11-14: `pbutil.MustMarshalMessage.specWalSnap` (internal, the part's) -- the size premise

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustMarshalMessageWalSnap.lean`.
- **Defect.** No bound on the encoding's size: `proto.Marshal` allocates it, and an allocation above Go's
  `maxAlloc` panics (`proto.MarshalPb.spec`'s premise `size c < 2 ^ 48`); `walSnapAt` bounds nothing, so the
  triple is unprovable over the part's `MarshalPb.spec`.
- **Evidence.** The proof (`wal-leaf3`): `wp_Marshal pbSnapC pbSnapC_reg sp c trivial ?_` has no argument.
- **Change (made, `wal-leaf3`).** The premise `(Mr.encSnap sm).length < 2 ^ 48`. Both callers have it:
  `SaveSnapshot.spec`'s pre gives `< 2 ^ 40`; `SaveSnapshot.specPre`'s frame bound `≤ lim < 2 ^ 47` (the record's
  data within its encoding, `recSize`). The non-nil result is derived (the encoding is non-empty, `Index` set:
  `snapEnc_ne_of_index`), not assumed.
- **Decision.** Made (internal, minimal, no client-visible change).

## 2026-11-14: `pbutil.MustUnmarshalMessage.specWalSnap` (internal, the part's) -- `U` says nothing of protobuf-go (proposed, not made)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean`.
- **Defect.** (1) The premise `U.decSnap bs = some s` is about the client's parameter `U : WalUnmarshal`, which no
  hypothesis ties to protobuf-go (`WalUnmarshal.Ok` ties it to `Mr` only): `bs` need not be any snapshot's
  encoding, `proto.Unmarshal` may fail (the code panics) and the decoded index/term need not be `s`. (2) The pre
  lacks `isPkgInit pbutil` (the call to `proto.Unmarshal` needs `proto`'s, which comes from it).
- **Evidence.** `proto.UnmarshalPb.spec` (part copy) at `pbSnapC`: success only when `bs = snapEnc c₀` for a
  `c₀` with valid unknown fields; the decoded content is `c₀` only then.
- **Proposed change.** A premise on `U` (a `ReadAll` hypothesis the client discharges for its codec, as
  `walSnapAt` ties `Mr` to `snapEnc`): `∀ bs s, U.decSnap bs = some s → ∃ c : WalSnapC, (∀ p ∈ c.levels,
  ufWire p.1 p.2) ∧ bs = snapEnc c ∧ (c.model.Index', c.model.Term') = s`, and `isPkgInit pbutil` in the pre.
  Then the proof is `MustUnmarshalMessagePb.wp_proof`'s over the part's `UnmarshalPb.spec`, with
  `snapOwnC_freeze` for the read-only snapshot.
- **Decision.** Open: it adds an obligation to `ReadAll`'s callers (`U`'s coherence with protobuf-go), the
  coordinator's call. **Adopted** (the coordinator, decided; made on `wal-leaf4`): the law is
  `WalEnc.WalUnmarshal.SnapCoh U` (`ReadAllCallees.lean`, a pure `def`, for C6 to discharge with the client's
  codec), a premise of `specWalSnap U` itself (`U.SnapCoh → ∀ sp d dq bs s, …`), and `isPkgInit pbutil` in the
  pre. Proved (`MustUnmarshalMessage.wp_proofWalSnap`). `WAL.ReadAll.wp_proof` takes `hUs : U.SnapCoh` next to
  `hU : U.Ok Mr`. (A canonical-only `U`, one decoding exactly the `snapEnc` images, satisfies both `Ok` and
  `SnapCoh` when `Mr.encSnap` is `snapEnc` of a valid content, as `walSnapAt` already requires.)

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- the commit bound on an existing directory

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/CreateCallees.lean`, `specTmp`'s success post
  (`h'.next ≤ n ∧ … ∗ osCommitLb n`: every entry that wrote `name` committed).
- **Defect.** False when `name` already holds a directory (the case `specTmp` adds): `TouchDirAll` (the fork's,
  F-N2) syncs `name`'s parent only in its `Exist` branch and, in the other, for each directory its climbing loop
  collected (`created`). `Exist(d)` is `Stat(d) == nil`, and `Stat` of an existing directory may fail (any errno:
  `os.Stat.wp_dirS`, the extension's environmental failure); after such a failure the loop's `Exist(d)` may
  succeed, so `created = []`, `MkdirAll` returns `nil` on the directory, nothing is synced, and `CreateDirAll`
  returns `nil` with `name`'s entries possibly uncommitted (the leftover `nm.tmp`'s `mkdir` from earlier in the
  generation). No premise `Create` can give rules it out (its `RemoveAll(nm.tmp)` leaves `tmpDirH` of any history).
- **Evidence.** The translation of `TouchDirAll` (`LinuxFs/Code/.../fileutil.lean`, fileutil.go:49); found
  designing `specTmp`'s existing-directory proof (`wal-leaf4`). Recorded as a durability gap of the fork's F-N2
  patch: `nonissues/etcd-fork-touchdirall-stat-error-no-parent-sync.md`.
- **Change (made, `wal-leaf4`).** The success post drops `h'.next ≤ n` and `osCommitLb n` (`∃ h' hJ J, ⌜h'.cur !!
  name = some (.dir J) ∧ hJ.cur = ∅⌝ ∗ …`). `Create` never used them (since `wal-create18` its commit bound comes
  from `syncDir(nm.tmp)` and the later parent fsync); its pattern loses `%n0`/`#Hcm0` and `hJs.2.2` becomes `hJs.2`.
- **Decision.** Made (internal, weaker post nobody used; no client-visible change).

## 2026-11-14: `fileutil.CreateDirAll.specTmp` (internal, the part's) -- a leftover `.touch` needs its file

- **Spec.** `specTmp`'s pre (`tmpDirH jp name h`: `name` holding nothing or a directory of files, the claims
  whole) and `tmpSub` (`CreateCallees.lean`).
- **Defect.** Too weak for the existing-directory case: the directory may hold a leftover `.touch` (a crash, or an
  error, between `IsDirWriteable`'s create and remove), and `IsDirWriteable`'s `os.WriteFile(dir/.touch, "",
  O_TRUNC)` then truncates that file, a step on its `OsMeta` and bytes (`os.OpenFile.wp_truncS` takes `trFile i
  False`). `tmpSub` holds only claims (names), no file's `OsMeta`; neither does any producer of `tmpDirH`
  (`walAreaRes`'s `TmpOk`, `os.RemoveAll.specDirS`'s `rmAllOut`, `TouchDirAll`'s error arms: `specEmptyS` drops the
  probe's `trFile`). So the case is unprovable: nobody owns the file the truncation changes.
- **Evidence.** `IsDirWriteable.specFile` (`wal-leaf4`, proved) needs `trFile i False` of `.touch`'s file;
  `walAreaRes` (`CreateDefs.lean`); `rmAllOut` (`Spec/os/RemoveAll.lean`).
- **Proposed change.** `tmpSub`'s directory arm also holds each file whole: `∃ hJ, ⌜FilesOnly hJ.cur⌝ ∗ osNames J
  (.except []) 1 hJ ∗ [∗map] c ↦ n ∈ hJ.cur, (∃ i, ⌜n = .file i⌝ ∗ trFile i False)` (or only `.touch`'s). Its
  producers then give the files: `RemoveAll.specDirS` (its pre's files, minus the unlinked ones), `TouchDirAll`'s
  error arms (`os.WriteFile.specEmptyS` returning the probe's `trFile`), and `walAreaRes`'s `TmpOk` for a leftover
  from before a crash (the crash rebuild's file ownership: the deep part). Alternatively restrict `specTmp` to a
  directory with no `.touch` (`Create` cannot show it).
- **Decision.** Open: the coordinator's call (the change reaches `walAreaRes` and the crash rebuild).
  **Adopted** (the coordinator, decided; made on `wal-leaf5`), in its "only `.touch`'s" form: `tmpSub`'s
  directory arm holds `WalFs.tmpEnt (hJ.cur !! .touch)` (nothing, or the file whole, `trFile i False`;
  never a directory). Only `.touch`'s file, because it is the one a callee changes (the probe's
  truncation); the other files of a temporary directory are only unlinked (`RemoveAll.specDirS`, which
  takes no file), and holding them all whole would make `Create`'s unminting give back the new WAL's
  first segment as a `trFile` (`walCreateP` holds its `OsMeta` and bytes but not `trFile`'s facts:
  `ZfGe`, `cut = none` after the writes), for no consumer. Producers: `walAreaRes` (`areaCls`: each
  tagged claim with `tmpClTouch`, the `.touch` of a whole claim under a WAL name's `nm.tmp`;
  `area_takeTmp`/`area_give`), `RemoveAll`'s wrapper (`rmAllOut_tmpDirH`: the file if `.touch` is still
  there), `TouchDirAll`'s error arms (`IsDirWriteable.spec`'s error post now gives the probe's file back,
  over `os.WriteFile.specEmptyS`'s `crTr False o`), `Create`'s exits (the directory has no `.touch`:
  `segClaim_back`, `create_Jback` keep the fact), and at boot the crash's `osFileStart`
  (`osFileStart_trFile`, `Crash.lean`; the area's establishment is C6's).

## 2026-11-14: `decoder.Decode.spec`/`proto.UnmarshalWalRecord.spec` (internal, the part's) -- an empty metadata read back as `nil`

- **Spec.** `LinuxFs/Spec/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean` (its success is `ownRec l r`,
  `walpb/Defs.lean`), and through it `decoder.decodeRecord.spec`/`Decode.spec` (`decPost`); `walHandleIn`'s
  `recBytes mds (some h.md)` (`Handle.lean`), which `ReadAll` must establish for the slice it read
  (`wal-readall26`, obligation (c) of `walOpenWF`).
- **Defect.** `ownRec` says `v.Data' ↦* r.data` only: with an empty metadata (`d.metadata = []`) the slice the
  loop keeps (`metadata = rec.Data`, S/wal.go) may be `nil` for all the spec says, and then the handle's `cut`
  would write a metadata record without the data field (`Record{Data: nil}`), not the model's `recOf` bytes (the
  field present, empty), so `walHandleIn`'s `recBytes … (some md)` (`ds ≠ nil`) is unprovable. Not a Go bug:
  protobuf-go decodes a present bytes field to a non-nil slice (`internal/impl/codec_gen.go`, `consumeBytes`:
  `*p.Bytes() = append(emptyBuf[:], v...)`), and `TestRecordEncoder` measured `proto.Unmarshal(recEnc c)` giving
  back exactly `c`, `Data`'s presence included. The specs drop it: `proto.UnmarshalPb.spec` gives the exact
  content (`c = c₀` when `bs = pbEncC I c₀`), `UnmarshalWalRecord.wp_proof` forgets it (`recOwnC_ownRec`).
  With a non-empty metadata the slice is non-nil from its points-to (its length), so only `[]` is affected.
- **Evidence.** The proof of `ReadAll`'s success arm (`ReadAllWFPure.lean`: `readAll_md_some` gives `st.md = some
  md`, not the slice's non-nilness); `Create.spec` takes the metadata non-nil but may take `[]`; `walInv_alloc`
  admits a WAL found at boot with any metadata below `2 ^ 41`.
- **Proposed change.** Either (A, no client change) the decoder keeps the content's presence: `ownRec l r`
  gains `⌜∀ r₀, bs = walRecEnc r₀ → (recOf r₀).data.isSome → v.Data' ≠ slice.nil⌝` over the frame's bytes
  `bs` (from `UnmarshalPb`'s exactness), carried by `decodeRecord`/`Decode` and the reader's model (`goDecode`'s
  accepted frames are the encoder's for the WAL's files, `walReadFiles_running` at the byte level); or (B) the
  metadata non-empty: `Create.spec` takes `md ≠ []` (the server's is a marshalled `etcdserverpb.Metadata` with
  both ids set, never empty) and `WalsBounded` carries `0 < |d.metadata|` (and `walInv_alloc` takes it of the
  WALs found at boot), so the slice's length gives `≠ nil`. (B) is a few lines; (A) is the faithful one.
- **Decision.** Open: (B) adds a client premise to `Create` and an assumption on the WALs found at boot; the
  coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry` (`hmdnn`).
  **Decided 2026-11-14 (coordinator; `wal-readall27`): (B).** The coordinator's first choice, relaxing
  `walHandleIn` to accept a `nil` slice at `md = []`, is not sound: `cut` encodes `Record{Type: …, Data:
  w.metadata}` as is (S/wal.go:842) and `record.proto`'s `data` is a proto2 `optional bytes`, so protobuf-go
  omits the field for a `nil` slice and writes it, empty, for `[]byte{}` (`recEnc`'s `optBytesField`, measured by
  `TestRecordEncoder`); a handle with a `nil` metadata would write a metadata record other than the model's
  `walRecEnc (recOf ⟨metadataType, _, []⟩)` (the field present), which the segments' byte model (`tailStream`,
  `WalAbsD`'s streams, the reader) fixes. Accepting it would need that model to admit both encodings of an empty
  metadata record, or (A). Made: `Create.spec` takes `md ≠ []` (beside `mp ≠ nil`; the server's metadata is a
  marshalled `etcdserverpb.Metadata` with both ids set); `WalsBounded` keeps `d.metadata ≠ []` (`Create`'s
  commit from the premise; no other step changes a metadata; `walInv_alloc`'s caller for the WALs at boot,
  none at the run's start); `ReadAll` gets the slice non-nil from its points-to's length.

## 2026-11-14: `walHandleIn`'s index bound (internal, the part's) -- `ReadAll` cannot bound `max(enti, snapi) + 1`

- **Spec.** `walHandleIn`'s `max (uint.nat h.enti) (uint.nat h.snapi) + 1 < 2 ^ 64` (`Handle.lean`), which
  `ReadAll` must establish (`wal-readall26`, obligation (d) of `walOpenWF`).
- **Defect.** `w.enti`/`w.snapi` after the loop are indices read from the WAL; nothing bounds them below
  `2 ^ 64 - 1`: `Save`/`SaveSnapshot` take `< 2 ^ 64 - 1` of what they write (their premises), but the
  invariant does not record it, so a WAL read back (or found at boot) may hold index `2 ^ 64 - 1` for all
  `ReadAll` knows, and `cut` would then name its next segment with a wrapped index.
- **Evidence.** `WalsBounded` (`Inv.lean`) bounds only the metadata; `WalAbsD.nameBound` bounds the indices
  before each segment by its name's `ix < 2 ^ 64`, not those of the last segment.
- **Proposed change.** An invariant fact, framed as `WalsBounded` (or a conjunct of it): `∀ dir d, s.wal !! dir
  = some d → ¬ walHasMaxIdx (histM d)`; kept by `Save`/`SaveSnapshot` from their premises, by `Create` (index 0),
  by crashes and cuts (histories' prefixes / unchanged), taken by `walInv_alloc` of the WALs found at boot. No
  client-visible change but the boot assumption.
- **Decision.** Open (an invariant change touching `Save`'s commit steps, which `wal-save*` owns): the
  coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry`.
  **Decided 2026-11-14 (coordinator; `wal-readall27`): as proposed**, as a conjunct of `WalsBounded`
  (`¬ walHasMaxIdx (histM d)`): `walInvBody_append` (and `walTail_append`, `walHandleIn_append`) take
  `¬ walHasMaxIdx [o.toM]` of the appended operation, which `Save` and `SaveSnapshot` give from their index
  premises; `Create` starts empty; the other steps keep the history. `ReadAll` bounds `max(enti, snapi) + 1`
  by it (`readAll_idxD`: every index the loop writes is one of the history's, or 0).

## 2026-11-14: `walDirH`'s sequence bound (internal, the part's) -- `ReadAll` cannot bound the tail's sequence

- **Spec.** `walDirH`'s `∃ sq ix, nm0 = walFileName sq ix ∧ sq < 2 ^ 63 + k` (`Handle.lean`), `k` the files
  the handle's pipeline handed over (0 at `ReadAll`), which `ReadAll` must establish for the tail's name
  (`wal-readall26`, obligation (f) of `walOpenWF`).
- **Defect.** Nothing bounds a read-back tail's sequence: `WalAbsD.nameBound` gives the name's form and
  `ix < 2 ^ 64`, not `sq`. `Create` starts at 0 and each `cut` adds one under the handle's receipt bound
  (`walPc_bound`), but receipts do not survive a crash, so across generations the sequence is bounded by
  nothing the invariant keeps (a WAL found at boot, or cut `2 ^ 62` times per generation over two
  generations, may hold `sq ≥ 2 ^ 63`). Then `cut`'s `seq + 1` could wrap (`w.seq()` is a `uint64`).
- **Evidence.** The assembly of `walOpenWF` in `ReadAll` (`wal-readall26`).
- **Proposed change.** Either an invariant fact (every `.wal` segment's sequence `< 2 ^ 63`, kept by `cut`
  with a premise `sq + 1 < 2 ^ 63` that its caller takes from a bound the invariant then must keep: no
  natural source) or, simpler, `walDirH`'s bound weakened to what `cut` needs, `sq + k < 2 ^ 64 - 1`-style
  against `uint64` wrap, with the tail's `sq < 2 ^ 64` from the name's 16 hex digits and the remaining room
  as a premise on `ReadAll` (the same shape as the index bound above: `sq < 2 ^ 63` of the tail an
  assumption on the WALs found at boot, kept by `cut` only while receipts bound it). Needs the coordinator's
  design: no option is free.
- **Decision.** Open: the coordinator's call. Until then `ReadAll`'s `walOpenWF` takes it as a marked `sorry`.
  **2026-11-14 (`wal-readall27`): the coordinator chose a receipts budget; designed, not made.** The sketch (a boot
  premise `sq < 2^63` on `walInv_alloc`, each cut consuming an exclusive receipt) does not close across generations
  (the handle's `⧗` vanish at a crash; the next boot's premise is not implied). Design (`notes/bounds-plan.md`, "The
  WAL's segment sequence"): crash-stable persistent receipts `⧖` of the global step counter, `WalAbsD.nameBound` with
  sequence `first + k`, the invariant holding `⧖ |lay.cuts|` per WAL (deposited by `cut` after a counted step), or `⧖
  |d.H|` (deposited at `Save`'s commit; a crash keeps a prefix). No statement of `walDirH` changes. `ReadAll`'s `hsq`
  stays a marked `sorry` until it is made.
  **2026-11-14 (`wal-readall28`): made, the alternative** (`⧖` of every history's length in the invariant's ghost
  state, `walStepsLb`; `WalAbsD.seqName`; `notes/bounds-plan.md`, "Made"). No client-visible statement changed; the
  `sorry` is gone.

## 2026-11-14: the resize supplies' `P` (internal, the part's) -- a growth's supply cannot bound the crash size

- **Spec.** `os.truncSup K p tg P` (`LinuxFs/Spec/os/File__TruncateAu.lean`) told `m0.lo ≤ tg ∨ P m0`;
  `fallocSup K i tg` (`Proof/syscall/FallocateAu.lean`) told only `m0.size ≤ tg`; `preallocExtend(Trunc).specAu`,
  `Preallocate.specAu`, `ZeroToEnd.specAu` passing supplies with the default `P`.
- **Defect.** The WAL's growth supplies (`ZeroToEnd`'s growth of the lent tail back to its size, `wal-tc19`)
  need `min lo tg ≤ wr` of the state they start from (`rzGrow_pure`: the growth's crash sizes from `lo` on are
  the window's), and the truncate's also `size ≤ tg`; `lo ≤ tg` (the old second disjunct) is too weak for a
  growth (`tg` the size), and the default `P` says nothing. The supplies see only the state's `OsMeta`.
- **Evidence.** `walTail_fallocSup`/`walTail_truncSupG` (`GrowSup.lean`).
- **Change (made, `wal-tc19`).** `os.truncSup` told `⌜P m0⌝`; `os.File.Truncate.specAu` takes `P m` and `∀ m',
  m'.lo ≤ min m.lo sz → m'.size ≤ max m.size sz → P m'` (every later attempt starts from an announced or landed
  state, `lo := min lo tg`); `fallocSup … P` told `⌜P m0⌝`; `preGrownH` carries `m'.lo ≤ m.lo`; the
  `preallocExtend(Trunc)`/`Preallocate` specAu take `P` with `∀ m', m'.lo ≤ m.lo → m'.size ≤ sz → P m'`;
  `ZeroToEnd.specAu` takes `P` (the truncate to `o`) and `Q` (the growth) with `P m` and `∀ m', m'.lo ≤ min m.lo
  o → m'.size ≤ m.size → P m' ∧ Q m'`, and its success post gains `m'.lo ≤ min m.lo o` (the handle's `LoWr`).
  The WAL passes `LoWr · wr` (truncate, as before) and `lo ≤ wr ∧ size ≤ tg` (growth). Lean-first specs,
  proved; no trusted change.
- **Decision.** Made (internal; the only instances are the WAL's).

## 2026-11-14: `ZeroToEnd.specWalTail` and `TailMetaZ` (internal, the part's)

- **Spec.** `ZeroToEnd.specWalTail` (`ReadAllTailCallees.lean`, a hypothesis of `WAL.ReadAll.wp_proof`):
  post `TailMetaZ` (`TailMetaW` without `PastZ`, so `TailZ` of the zeroed tail); pre without `isPkgInit errors`.
- **Defect.** `TailZ` of the zeroed tail is not provable: a crashed tail (`initMeta`: `zf = pageEnd size`,
  `cz = 0`) or a synced one need not know the candidates of its last page past the size, and `ZeroToEnd`
  (`ZteMeta`) does not make them known; what the fdatasync after it needs is only the page cache known zero to
  the end of the size's page (`TailZ.synced_of`), which `ZeroToEnd.specAu` gives. `ZeroToEnd.specAu` needs
  `isPkgInit errors`.
- **Change (made, `wal-tc19`).** `TailMetaZ m bs := |bs| = size ∧ maps = ∅ ∧ pageEnd size ≤ max size cz`;
  `specWalTail`'s pre gains `isPkgInit errors` (`ReadAll`: `iPkgInit`, adapted), its post `sz' = sz`. Proved:
  `ZeroToEnd.wp_specWalTail` (`ZteWalTail.lean`, over `ZeroToEnd.specAu`).
- **Decision.** Made (internal).

## 2026-11-14: `wal.Create.spec` (the part's) -- the success arm is false when the parent's fsync fails and its close succeeds

- **Spec.** `wal.Create.spec`'s first arm: `err = nil` gives `walOpenWF P Mr w dir`, `walNamed dir`, `Q`, ...
- **Defect.** Not the spec's: the code's. After a failed `fileutil.Fsync(pdir)`, `Create` calls `dirCloser()`,
  which assigns `pdir.Close()`'s result to `perr`; a successful close makes `Create` return `(nil, nil)` and skip
  its deferred `cleanupWAL`. Over `fsExt` the fsync may fail (`Fsync.specDirS`) and the close succeed, so no
  spec with an honest success arm holds (`nonissues/etcd-wal-create-parent-fsync-nil-nil.md`; etcd's
  `bootstrapNewWAL` would dereference the nil WAL).
- **Evidence.** The continuation after `renameWAL` (`wal-create22`).
- **Proposed change.** None to the spec: the fork fix `notes/wal-fsext-fork/0005-...diff` (`pdir.Close()` on
  that path), then retranslate; the spec stays as it is.
- **Decision.** Pending the user (a fork change). Until then `Create.wp_proof` keeps a marked `sorry` on that
  path only.

## 2026-11-14: `wal.Repair.spec` (the part's, over `fsExt`) -- the `false` arm after a failed `Truncate` or `Fsync` cannot return the lock token

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Repair.lean` (`wal.Repair.spec`): every arm's post
  returns `walUnlockedTok` (framed, the entry "the lock token taken" above).
- **Defect.** Unprovable on two of the `false` arms. `walUnlockedTok`'s `walTailsFrag ∅` makes `Repair` unregister
  the tail it registered (the pending token, kind `true`, for its truncate at `wr`), which needs the tail idle
  (`WalTailIdle`: exact). After a failed `f.Truncate(lastOffset)` (`os.ftUndoneH`: the truncate's window open,
  `lo = wr`) or a failed `fileutil.Fsync(f.File)` after it (the window open, landed or not), the Go code returns
  `false` with no sync, and nothing the program can do closes the window. The state is crash-safe
  (`crashOkA_tailRep`: the window of a `RepOld` tail); only the unregistration fails.
- **Evidence.** The W7-W12 log, twelfth session ("Finding", option (b)); S/repair.go:83-97. Every client stops
  on `false`: the WAL tester's `restartRead` returns `readFail` (examples/etcd/wal/wal.go:200-202), etcd's
  `openWALFromSnapshot` calls `lg.Fatal` (server/etcdserver/bootstrap.go). Plan §6 Q6 (honest error posts: a
  client stops on these errors; `Sync`'s error arm already loses the handle).
- **Proposed change.** The post's token becomes `walUnlockedTok ∨ ⌜b = false⌝`: on `true` the token comes back;
  on `false` it may not (the proof returns it on every `false` arm but the two above). Nothing else moves
  (`∃ o, Q o`, the area's resources and the call permission are returned on every arm). The tester's proof
  (`restartRead`) uses `Repair`'s token only on `true` (the retried `Open`).
- **Decision.** Accepted (the coordinator, under plan §6 Q6, 2026-11-14: option (b) of the twelfth session's
  finding); applied by `wal-repair24` (the W7-W12 log, thirteenth session).

## 2026-11-14: `wal.WAL.sync.specC` (internal, the part's) -- the error arm keeps the lock token; `WAL.Close.specU`

- **Spec.** `WAL.sync.specC`'s error arm `⌜err ≠ nil⌝` (the handle and the lock token lost).
- **Defect.** `Create`'s cleanup (`cleanupWAL` after a committed rename whose parent fsync failed) runs `w.Close()`;
  when its `sync` fails, `Close` returns before unlocking, and `Create` must still merge `nm.tmp`'s claim back to
  the area (`create_areaBack`, which needs a token excluding the free one): `walLockedTok`, which the failed
  `sync` still holds (`walOpenW`: its flush failure leaves it, the fdatasync returns the pending-cut flag).
- **Evidence.** `cleanupWAL`'s design (W4 log, twenty-fourth session, (b)); `wal-create23`.
- **Change (made, `wal-create23`).** `sync.wp_core`'s error arm returns `walOpenW w dir`; `specC`'s error arm
  `⌜err ≠ nil⌝ ∗ walLockedTok` (`walOpenW_lockedTok`); `sync.spec`/`specCut` unchanged (they drop it). New:
  `WAL.Close.specU` (the cleanup's `Close`: over `walOpenWFU`, no update, the commit-free put-back
  `walCloseLawU`), post `(walUnlockedTok ∗ osCallPerm 1) ∨ (⌜err ≠ nil⌝ ∗ walLockedTok)` (the left arm whatever
  `err`: the directory's close failed after everything else).
- *Obligation, not made*: `Create`'s deferred `f.Close()` after the cleanup needs the segment's lock file: closed
  (`os.ownFile f (-1)`) when `Close` succeeded, open when its `sync` failed. Both need the handle's tail lock to be
  `Create`'s `f` (`walOpenWFU` hides it: a parameter `lt`, from a copy of `walHandleIn` with `lt` free), and the
  failed arm needs the tail file back from `sync`'s error arms (through `wp_tailWriteAtW`, `wp_tailWriteW`,
  `wal.tailWriterW`'s `B`, `flush`), and `renameWALPost`'s arm 2 must return `walLockLeft f …` (the retry's
  `w.Close()` closed it, or its `sync` failed and left it open).
- **Decision.** Made (internal).

## 2026-11-14: `time.Time.Format.spec` (trusted, an axiom) -- its result unconstrained; `cleanupWAL`'s rename

- **Spec.** `time.Time.Format.spec` (`Spec/time/Time__Format.lean`, axiom `Proof/time/Time__Format.lean`): post `True`.
- **Defect.** `cleanupWAL` renames the WAL to `fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format("20060102.150405.999999"))`;
  with nothing known of the timestamp the target may hold `/` (a path under some other directory) or be any length,
  and no `os.Rename` spec (nor ownership) covers an arbitrary target.
- **Evidence.** `cleanupWAL`'s proof (`wal-create23`; W4 log, twenty-fifth session).
- **Proposed change.** A spec of `Format` for that layout: the result's characters are digits and `.`, its length at
  most 22 (Go's layout: `yyyymmdd.hhmmss` and a fraction of up to six digits, trailing zeros and a bare `.` dropped).
  Until then `cleanupWAL`'s proof takes it as a callee hypothesis. Separately an `os.Rename` spec over `fsExt` for a
  target name past 255 bytes (`ENAMETOOLONG`, nothing changed).
- **Decision.** Pending the user (a trust-boundary change).

## 2026-11-14: `os.File.WriteAt.specLong` (the part's) -- the failure arm's `OsMeta` and page cut are false past 1 GiB

- **Spec.** `LinuxFs/Spec/os/WriteLong.lean`, `os.File.WriteAt.specLong` (no `SpecPlan` counterpart); its
  callers' error posts restate it: `os.File.Write.wp_long` (`LinuxFs/Proof/os/OffLong.lean`) and `os.fileB`
  (`LinuxFs/Proof/os/WriterStream.lean`).
- **Defect.** Unprovable past `maxRW` (1 GiB), failure arm. (1) The `OsMeta` `pwPost m off A j`: an attempt
  that lands its whole chunk `[nn, E)` raises `cz` to `pageEnd (off + E)` (`pwCz`, when the zeros known start
  at or below `off + E`); if a later chunk is then announced (`A > E`) and the write fails before reaching `A`,
  the file's `cz` keeps that raise, but `pwPost m off A j`'s is `m.cz` (`j ≠ A`), and no other `A`, `j` gives
  the announcement (dirty range, `zf`, `tc`, `hi`) the later chunk made. (2) `PwCut off len j`: a whole chunk
  of `2^30` bytes from an offset off a page boundary lands and the next attempt fails with nothing written:
  `j = 2^30`, `off + j` is not on a page boundary.
- **Evidence.** The Löb step of `os.File.WriteAt.wp_proof_long` (`LinuxFs/Proof/os/WriteLong.lean`): the
  `cz` of `pwPost (pwPost m off A A) (off + A) c 0` is `pwCz m off A A`, not `pwCz m off (A + c) A = m.cz`;
  the page cut: `PWriteFinish`'s `PwCut (off + nn) c k` with `k = c` says nothing of `off + nn + c`'s page.
- **Proposed change.** The post gains the end `E` of the last chunk that landed whole (`E ≤ j`, `j = A → E = A`;
  `0` if none): the `OsMeta` is `os.pwPostE m off A j E` (`pwPost m off A j` with `cz := pwCz m off E E`), the
  cut `os.PwCutE off len j E` (`PwCut off len j`, or `j = E` within `maxBytes`). Up to `maxRW` (`E = 0` or
  `E = j = A`) and on success (`E = j = A = len`) both are `pwPost`'s and `PwCut`, definitionally or by a
  lemma; the callers' error posts take the same change (both callers drop that arm's resources).
- **Decision.** Made (internal to the part: only the failure arm of a write past 1 GiB moves; no client-visible
  ghost state; the success arm unchanged). `wal-wlong1`.
## 2026-11-14: `wal.ValidSnapshotEntries.spec` (the part's, W8) -- restated over `fsExt`

- **Spec.** The main tree's axiom `Spec/.../wal/ValidSnapshotEntries.lean` (`walUnlockedTok` framed, the AU over
  `walDirIs` unchanged, success `walSnapsAt ps (walValidSnaps (d.H.map toM) d.cut)`), restated over `fsExt`:
  `LinuxFs/Spec/.../wal/ValidSnapshotEntries.lean`.
- **Defect.** None of the main tree's statement: only plan §3's binders change (`walAreaOk walCodec Mr`, the
  area's spine `osPathS R r qp jr` and `walAreaRes jr` framed, `osCallPerm 1` framed, the update at
  `walAuMask`; premises `InArea r dir nm`, `NameOk nm`, `cleanAbsPath r`, `dir.length < 2^59`), as `Repair`'s
  and `OpenForRead`'s, which read the same directory the same way.
- **Evidence.** `Repair.spec`, `OpenForRead.spec` (the same binders); S/wal.go:698-791.
- **Change (made, `wal-vsnap1`).** The restated spec; the update commits unchanged where the proof pins the
  segments (before the retry loop: every attempt reads the same pinned files, so the retry needs no second
  commit).
- **Decision.** Made (the restatement plan §3 prescribes).

## 2026-11-14: `decoder.Decode.spec` (the part's) -- no `errors.Is(err, io.ErrUnexpectedEOF)` answer on an I/O error

- **Spec.** `decPost`'s I/O arm (`⌜IoE err⌝`, `DecDefs.lean`) and `decAns` (only `errors.Is(err, io.EOF)`).
- **Defect.** Too weak for read mode's callers: `validSnapshotEntries` (W8) and `ReadAll` in read mode accept
  `errors.Is(err, io.ErrUnexpectedEOF)` as the end; on an `IoE` error the proof knows no answer, so a `true` would
  make a partial read a success. In Go the readers' errors are `*PathError`s of an errno, for which it is `false`.
- **Evidence.** S/wal.go:772-776 (VSE's exit test); `ReadBridge.lean` (the readers' errors are `errnoPathErr`).
- **Proposed change.** Carry the `io.ErrUnexpectedEOF` answer as the `io.EOF` one: `decRdE` and `decAns` gain
  `isEofAns e ueof` (with `e ≠ ueof` for an `IoE` error, as `¬ IoE eof`), `walDecFiles_mk` proves it from an
  `errors.IsPathErrnoEof`-style spec for `ueof`.
- **Decision.** Pending (internal; `validSnapshotEntries.specPinned` stays a hypothesis of VSE until it is made).
  **2026-11-14 (`wal-vsnap2`): adopted, refined.** A general `decide (e = ueof)` answer is false of `Decode`'s
  own errors (a `fmt.Errorf("%w ...", io.ErrUnexpectedEOF)` is not `ueof` but `errors.Is` finds it), so the
  answer is carried only on the I/O errors, which are the ones `Decode` passes on: `notUeof e` (`errors.Is(e,
  io.ErrUnexpectedEOF)` returns `false`, for the value the global holds; no new parameter), `ioUeof IoE e`
  (`e` nil or not `IoE`, or `notUeof e`) in `decRdE` and in `decFile`'s and `ownFbr`'s `FileInfo` result,
  and `notUeof err` in `decPostB`'s I/O arm. The readers' evidence: `errors.IsPathErrnoEof.spec` (a
  hypothesis) now also covers `io.ErrUnexpectedEOF`'s value (the same argument: a fifth `errors.New`
  allocation), `walPathErr_ueof` (`ReadBridge.lean`).

## 2026-11-14: `openWALFiles.spec` (internal, the part's) -- the closer not specified

- **Spec.** `LinuxFs/Spec/.../wal/openWALFiles.lean`: the success arm said nothing of the closer `cl`.
- **Defect.** Too weak for `validSnapshotEntries`/`Verify` (`defer func() { if closer != nil { closer() } }()`):
  the call needs a triple.
- **Evidence.** S/wal.go:494 (`closer := func() error { return closeAll(lg, rcs...) }`); W8 session's gap 2.
- **Change (made, `wal-vsnap2`).** The success arm adds `wal.walCloser write frs lfs cl` (`CloseDefs.lean`):
  `cl` non-nil, and `□` a triple of `cl()` over each reader's file again closable (`wal.walClosable write fr
  lf`: the `*fileReader`'s file, its fd whole, in write mode the lock's `lockedFile`), returning some error.
  Write mode (`openAtIndex`) drops it.
- **Decision.** Made (internal; no ghost state).


## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the I/O arm loses the files' streams

- **Spec.** `decPostB`'s I/O arm (`LinuxFs/Proof/.../wal/DecDefs.lean`): `⌜IoE err⌝ ∗ ownRecAny rp ∗ ∃ fs' off' c',
  ownDecoder d IoE eof fs' off' c' false`.
- **Defect.** Too weak for `wal.Repair` (S/repair.go:30-106): on a reader's I/O error its `default` arm returns `false`
  and the deferred `f.Close()` runs, which needs the segment's `*os.File` (`os.File.Close.spec`: `os.ownFile`, `osFd`),
  held in the segment's stream (`walFileS`) inside the decoder; the arm's decoder is over unknown files `fs'`, so
  the stream cannot be taken out (`ownDecoder_streams`).
- **Evidence.** `RepairLoop.lean`'s `repair_decNorm` (the I/O arm, `sorry`); the decoder only ever leaves files at
  their end (`d.brs = d.brs[1:]`), so its files are always a suffix of `fs` (as the record and stop arms say).
- **Proposed change.** The I/O arm as the first arm's files: `∃ k off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗
  ownDecoder d IoE eof (fs.drop k) off' c' false` (`decodeRecord`'s I/O exits build it with `k = 0`,
  `decPost_cons_eof` adds one). Implies the old arm; `ReadAll` (the only other caller) drops it.
- **Decision.** Pending (internal; to be made after `wal-vsnap2`'s change of the same arm lands, to avoid a conflict).
  **2026-11-14 (`wal-vsnap2`): adopted** (the coordinator's decision), as proposed: the I/O arm is `⌜IoE err⌝ ∗
  notUeof err ∗ ownRecAny rp ∗ ∃ k off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ownDecoder d IoE eof (fs.drop k)
  off' c' false`.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- no `errors.Is(_, io.ErrUnexpectedEOF)` termination on `Decode`'s own errors

- **Spec.** `decPost` (`LinuxFs/Proof/.../wal/DecDefs.lean`): `decPostB ∗ decAns eof err`; only the I/O arm carries
  `errors.Is(err, io.ErrUnexpectedEOF)`'s answer (`notUeof`).
- **Defect.** Too weak for `wal.Repair` (S/repair.go:64: `errors.Is(err, io.ErrUnexpectedEOF)` on every non-`EOF`
  error) and `validSnapshotEntries`/`ReadAll` read mode: on a stop's or a failed `Unmarshal`'s error the call has no
  spec (`RepairLoop.lean`'s `errUeAns_end`, `sorry`).
- **Evidence.** The stop errors are `io.EOF`, `io.ErrUnexpectedEOF`, `fmt.Errorf("%w ...", io.ErrUnexpectedEOF|err)`
  (decoder.go:110-150) and `proto.Unmarshal`'s; `errors.Is` terminates on each in Go.
- **Change (made, `wal-vsnap3`).** `decPost := decPostB ∗ decAns eof err ∗ decUe err`, `decUe err := ⌜err = nil⌝ ∨
  errIsTerm err ∨ notUeof err`, `errIsTerm e` (`LinuxFs/Spec/fmt/ErrorfErrsNot.lean`): `errors.Is(e, u)` returns for
  every pointer target `u`. The hypotheses it comes from carry it: `fmt.ErrorfErrsNot.spec` (pre: each error argument's
  `errIsTerm`; post: the result's), `walpb.Record.Validate.spec` (pre: `ErrCRCMismatch`'s; post: its error's),
  `proto.UnmarshalWalRecordE.spec` (post: its error's), `decEnv` (`ErrCRCMismatch`'s; a part of the hypothesis
  `WalDecEnvSupply`); `io.EOF`'s and `io.ErrUnexpectedEOF`'s are proved (`*errorString` leaves, `errors.wp_Is_leaf`).
  **Deviation from the coordinator's wording** ("the `%w`-wrapped `io.ErrUnexpectedEOF`: true; `io.EOF`: false"):
  only termination is given, no answer. `true` on `fmt.Errorf("%w ...", io.ErrUnexpectedEOF)` is Go's answer but false of
  Perennial's `fmt.Errorf` model (`errors.New(format)`, a fresh leaf), so the hypothesis `ErrorfErrsNot` could not be
  discharged from the model if it claimed it; and no caller needs an answer (`Repair` needs `true` only at the end of the
  frames, where the stop is, `RepairAt`; `validSnapshotEntries`' error arm takes any error). `io.EOF`'s `false` follows
  from `wp_Is_leaf` where a caller needs it.
- **Decision.** Made (internal; no ghost state; the hypotheses' strengthening is true of Go and of the models).

## 2026-11-14: `openLast.spec` (internal, the part's) -- the last segment's name not known valid

- **Spec.** `walLastOpen` (`LinuxFs/Proof/.../wal/OpenLastDefs.lean`), `openLast.spec`'s success arm: the pin of the
  last segment `gL`, its file open at `child dir gL.name`, with pure facts on the layout.
- **Defect.** Too weak for `wal.Repair`'s `createNewWALFile(f.Name() + ".broken", true)` (S/repair.go:62): the open
  specs take `NameOk` of the created name, `repBroken gL.name`, which follows from `NameOk gL.name`; nothing in
  `walLastOpen` gives it (the segments' facts say `.wal` suffix and the entries, not validity).
- **Evidence.** `openLast.wp_proof` has it (`hbok`, from `ReadDir`'s output) and drops it; `Repair.wp_proof`'s
  `io.ErrUnexpectedEOF` arm (`wal-repair26`).
- **Change (made, `wal-repair26`).** `walLastOpen`'s pure facts add `NameOk gL.name` (last). A strengthening;
  `Repair` is the only client.
- **Decision.** Made (internal; no ghost state).

## 2026-11-14: the WAL's raftpb laws (`WalPbIn.*Law`, `WalHsOwn`) -- unprovable for real raftpb as stated (W4c U4)

- **Spec.** The model laws the WAL's `Link.lean` results take of the client's `P : WalPbIn GF`, `U`, `HsO`
  (`LinuxFs/Spec/.../wal/{WAL__Save,WAL__cutPre,WAL__saveEntry,ReadAllCallees}.lean`,
  `LinuxFs/Proof/.../wal/HandleUnnamed.lean`), to be discharged by the raftpb instance (U4).
- **Defects** (the laws are true of Go; they are not provable from this repository's trusted facts):
  1. **No package initialization in the pre.** `WalPbIn.UnmarshalEntLaw` and `WalHsOwn.unmarshal` (pre
     `d ↦*{dq} bs` only) call `pbutil.MustUnmarshalMessage`, whose specs (`MustUnmarshalMessagePb.spec`,
     `specWalSnap`) and `proto.UnmarshalPb.spec` take `isPkgInit pbutil`/`proto`; `WalPbIn.CloneHsLaw` calls
     `proto.Clone` (`ClonePb.spec`: `isPkgInit proto`) on any `P.hsIn` object, including a fresh zero one
     that `WalPbIn.ZeroLaw` makes from nothing; `WalPbIn.IsEmptyLaw` runs `raft.IsEmptyHardState`, which
     reads raft's package variable `emptyState` (node.go:32, :122-124), known only from `isPkgInit raft`,
     again on a fresh zero object. `P.hsIn` cannot carry the initialization: `WalPbIn.NilLaw` (`⊢ P.hsIn null
     hsZero`) and `ZeroLaw` produce it from no resource. (`MarshalEntLaw`/`MarshalHsLaw` can be met by
     putting `isPkgInit pbutil` into `P.entIn` and into the non-empty arm of `P.hsIn`, a workaround.)
  2. **`raftpb.HardState` has no trusted wire model.** It is not a registered `PbTypeC` (its schema is `[]`,
     `Proof/google_golang_org/protobuf/proto/PbSchema.lean`, "a type not listed here"), so no `proto` spec
     says what `pbutil.MustMarshalMessage`, `pbutil.MustUnmarshalMessage` or `proto.Clone` do on a
     `*raftpb.HardState`: `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal` are unprovable without a new
     registration (two axioms, as `walpb.Snapshot`'s `snapEncC_ok`/`pbSnapC_reg`).
  3. **`HardState.Reset` has no body.** raftpb's `Reset` is names-only (`Code/go_etcd_io/raft/v3/raftpb.toml`:
     `!*.Reset`), with no spec: `WalHsOwn.reset` needs a trusted model (as walpb's `Record.Reset.impl`).
  4. (Minor, worked around.) `WalUnmarshal.Ok.entry` is a round trip for **every** entry, but the entry
     encoder's trusted fact (`entryEncC_ok`) says nothing at sizes `≥ 2^63`; the instance uses stand-in bytes
     for entries of `2^48` bytes or more (`RaftModel/EntCodec.lean`), which no `Save` writes (its premise is
     `< 2^40`).
- **Evidence.** W4c U4 log (`notes/wal-fsext-w4c-plan.md`); the instance `walRaftMr`/`walRaftU` and its pure
  laws (`LinuxFs/Proof/.../wal/RaftModel/Marshal.lean`).
- **Proposed change.** (1) Add `isPkgInit pbutil` to the pres of `UnmarshalEntLaw`, `WalHsOwn.unmarshal`,
  `MarshalEntLaw`, `MarshalHsLaw`; `isPkgInit proto` to `CloneHsLaw`'s; `isPkgInit raft` (the part's
  `go_etcd_io.raft.v3`) to `IsEmptyLaw`'s. Their callers (`ReadAll`, `saveEntry`, `saveState`, `Save`, `cut`) hold
  `isPkgInit wal`, which gives the three (the WAL imports pbutil, proto and raft). (2)+(3) [user]: register
  `raftpb.HardState` in the part (`WalHsC`, `hsEnc` as in `RaftModel/Codec.lean`, a schema
  `[(1,[0]),(2,[0]),(3,[0])]`, `hsEncC_ok`, `pbHsC_reg`; Go-tested as `walpb.Snapshot`'s) and give
  `HardState.Reset` a trusted model -- or keep the three laws as hypotheses of the closed result.
- **Decision.** (1) taken (coordinator, 2026-11-14, branch `wal-u4b`): `isPkgInit pbutil` in the pres of
  `MarshalEntLaw`, `MarshalHsLaw`; `isPkgInit proto` in `CloneHsLaw`'s; `isPkgInit raft` (the part's root
  package) in `IsEmptyLaw`'s; **`isPkgInit wal`** (not pbutil) in `UnmarshalEntLaw`'s and `WalHsOwn.unmarshal`'s,
  as every spec of a `wal` function (`MustUnmarshalEntry`/`MustUnmarshalState` are `wal`'s; wal's
  initialization gives pbutil's). `WAL.saveState.specPre` (`cut`'s) gains `isPkgInit wal` in its pre (it had
  none, and its two laws now need raft's and pbutil's). The part's raft root fact gains `emptyState` (the
  main tree's conjunct, word for word), which `IsEmptyLaw`'s proof reads. (2)+(3) stay out (the user's call,
  W4c U4 task 3): `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal`, `WalHsOwn.reset` remain hypotheses of
  the closed result, listed in §10 of `notes/wal-fsext-plan.md` as pending the user.

## 2026-11-14: `fileutil.ReadDir.spec`/`specAbsent`, `readWALNames.spec`/`specAbsent`, `openWALFiles.spec` (internal, the part's) -- no `errors.Is` termination on their errors

- **Spec.** Their error arms give only `fmtErrorOkOrNil`/`errOk`: `errors.Is` on the error has no spec.
- **Defect.** Too weak for `validSnapshotEntries` (`specPinned`/`specAbsent`), whose errors must carry `wal.vseErrIs`
  (`ValidSnapshotEntries`' retry test `errors.Is(err, os.ErrNotExist)`, S/wal.go:639, on every error the attempt
  returns: `readWALNames`', `openWALFiles`', the decoder's, `ErrCRCMismatch`). Found in `wal-vsnap3` (W8, third
  session).
- **Evidence.** The errors are `*PathError`s of an errno (`os.errnoPathErr`, the part's `os` models: `ReadDir`'s
  every error, `os.OpenFile`'s), `fmt.Errorf("...: %w", e)` of them, and `errors.New` leaves (`ErrFileNotFound`,
  `ErrCRCMismatch`); `errors.Is` terminates on each in Go (`*PathError` has no `Is`; its `Unwrap` gives the `Errno`,
  whose `Is` compares the target with four pointer errors; `*wrapError` unwraps to its argument).
- **Change (made, `wal-vsnap4`).** `errIsTerm` (`errors.Is(e, u)` returns for every pointer target `u`) on: the
  error arms of `ReadDir.spec`/`specAbsent`, `readWALNames.spec`/`specAbsent`, `openWALFiles.spec` (read mode: write
  mode's `TryLockFile` errors are not needed), `notUeof` (the decoder's I/O errors); the wal package's error
  variables (`wal.errVar`) and `walpbInit`'s `ErrCRCMismatch` (`*errorString` leaves, proved). The `os`/`io/fs`
  package facts record `ErrNotExist` as an `*errorString` (proved from `internal/oserror`'s `errors.New`), so that
  `vseErrIs` follows from `errIsTerm`. Two new hypotheses, true of Go (as `errors.IsErrno.spec`,
  `fmt.ErrorfErrsNot.spec`): `errors.IsPathErrnoTerm.spec` (`errIsTerm` of an `os.errnoPathErr`) and
  `fmt.ErrorfErrsTerm.spec` (`fmt.ErrorfErrs.spec` passing `errIsTerm` from the error arguments to the result).
- **Decision.** Made (internal; no ghost state).

## 2026-11-14: `walInvBody` (internal, the part's) -- the crash boot's files-only fact `hfo` not derivable (W4c U3)

- **Spec.** `walInvBody` (`LinuxFs/Proof/.../wal/Inv.lean`) and what `walInv_crash` returns of the crashed tree.
- **Defect.** The crash boot (`walBootCrash`) must give the next generation `walTmpsRes J` (`0.tmp`/`1.tmp` absent or
  files), `walOthersL` (a WAL directory's non-segment entries files), `walAreaRes`'s `TmpOk` (a leftover `nm.tmp` holds
  only files, for `os.RemoveAll.specDirS`) and `tmpClTouch` (its `.touch` no directory). A crash leaves at a name what
  one of its claim's versions held (`RegionCrashed`), and only for the claims the invariant holds when the crash comes;
  the pipeline's names (while a write handle holds them), `Repair`'s lent names, `Create`'s `nm.tmp` directory and its
  contents are under claims the program holds whole, and the invariant's own WAL-directory claims record no fact about
  their past versions. So the fact is the crash boot's premise `hfo` (U3 log, second session), true of the Go code (the
  WAL creates no directory there) but dischargeable by no one.
- **Evidence.** U3 log, second session, (d); `BootFilesOnly.lean` (the crash-side lemma, proved).
- **Proposed change (decided by the coordinator, 2026-11-14).** A new framed conjunct of `walInvBody` (its own
  predicate, `walFoRes`): a list `fl` of claims held at half, and pure facts: every claim of `fl`, and every
  WAL-directory claim of `cl`, has a history holding no directory at its names (`HistNoDir`, all versions); and every
  version of an area claim of `cl` holding a directory `J` at a WAL name or at `nm.tmp` has every name of `J` covered by
  such a claim. Then `RegionCrashed (cl ++ fl) n V'.now` gives `hfo` (`regionCrashed_filesOnly`), narrowed to WAL names
  and `nm.tmp` (the `nm.broken.<t>` directories need only `SubCover`, which the boot's whole claims give). Every update
  under a claim of `fl` becomes an invariant step (`osAU`/`osAUnc` with the invariant's half: the os specs are already
  shaped for it). Condition checked: `walAreaRes` is unpacked by no client (outside the WAL's proofs only comments and
  the WAL's own specs name it; its body is exposed, not `@[no_expose]`-sealed). No client-visible ghost state: `fl` is
  inside the invariant.
- **Decision.** Adopted (internal), in progress: the design's open points are in the U3 log, third session.

## 2026-11-14: the part's WAL handle specs (`wal.Create.spec`, `WAL.ReadAll.spec`, `walOpenWF`) -- the client keeps no call permission while a WAL is open (W4c U5)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean` (success arm: `walOpenWF` alone, no
  `osCallPerm` back), `Open.lean` (`walOpeningF` holds the client's `½`), `WAL__ReadAll.lean` (moves it into the
  handle's `walDirH`), `WAL__Close.lean` (gives back `osCallPerm 1`); `Handle.lean:457` (`walDirH` holds `osCallPerm ½`)
  and the pipeline (`walPipeH`) the other half.
- **Defect.** While a WAL is open the handle and its pipeline hold the whole call permission, so the client can make
  no `os` call until `Close`. The tester (`examples/etcd/wal/wal.go`) calls `storeOracle` (`durable.Write`: `os`
  calls, `osCallPerm qc` with `qc > 0`) between WAL calls with its WAL open (`save`, `saveSnap`, `sync`, `opOwnSnap`,
  `restartRead`'s `Open` loop, `Boot` after `Create`), and so would etcd (its snapshotter and backend write files
  while the WAL is open). The W4c U0 audit assumed the client kept `osCallPerm ½` while a WAL is open (plan §2, the
  table's `Open` row); the two ledger entries of 2026-11-14 that moved the halves into the handle and the pipeline
  (`Create`'s, `Open`'s "the call permission counted twice") left the client none.
- **Evidence.** `member.sync`'s proof (W4c U5, second session): after `Create`/`ReadAll` nothing supplies
  `storeOracle.spec`'s `osCallPerm qc`.
- **Proposed change.** The handle and its pipeline hold a quarter each and `Create`'s success arm (and `ReadAll`'s)
  gives the client `osCallPerm ½` back (`Open` keeps taking `1`: it hands `¼` to the pipeline, `¼` in
  `walOpeningF`, `½` back); `Close` gives back the handle's and the pipeline's `½`, the client recombining to `1`.
  A resource placement (fractions only, no new ghost state); the WAL's own proofs change only where they split or
  join the permission (`openAtIndex`, `Create`'s commit, `ReadAll`, `Close`). Interim (made): the tester's member
  state (`TP/Member.lean`) holds the client's `osCallPerm qc` as a parameter, so the member operations' proofs stand
  once the WAL's arms give it back; only `Boot`/`restart` (which take it from `Create`/`ReadAll`) wait.
- **Decision.** Adopted (the coordinator's decision of 2026-11-14; made on branch `wal-u5c`, W4c U5 third
  session). As proposed, with `Open`'s fractions placed thus: `openAtIndex`'s write arm returns `osCallPerm ¼ ∗
  osCallPerm ½` (the pipeline's `pipeRes` the other quarter), `Open` puts the quarter in `walOpeningF` and
  returns the half (`walOpeningF w dir s ∗ osCallPerm ½`); `ReadAll` moves `walOpeningF`'s quarter into the
  handle's `walDirH` (no change to its spec: the client's half came from `Open`). `Create`'s success arm (and
  `renameWAL`'s two committed arms, so `renameWALUnlock`'s hypothesis too) carries `osCallPerm ½`. `Close`,
  `Close.specU` and `Close.specOpening` return the half the handle and its pipeline held (`osCallPerm ½`;
  `specOpening` takes the quarter of `walOpeningF`); the client recombines with `osCallPerm_halfJoin`
  (`Pipe.lean`). Every error arm unchanged (`Create`'s after-rename arm `Q ∗ osCallPerm ½`). The tester's
  `member.close.spec` returns `Close`'s `osCallPerm ½`.

## 2026-11-14: `decoder.Decode.spec`/`decodeRecord.spec` (internal, the part's) -- the failed-`Unmarshal` arm loses the files' streams (W4c U5, fourth session)

- **Spec.** `decPostB`'s third arm (`GoFail`, `LinuxFs/Proof/.../wal/DecDefs.lean`): `∃ k s off' c', ⌜GoFail … ∧
  stopErr …⌝ ∗ ownDecoder d IoE eof (fs.drop k) off' c' false`.
- **Defect.** The streams of the `k` files the decoder left before the frame `proto.Unmarshal` rejected are dropped
  (`decPost_cons_eof` frames them away), as the I/O arm's were before the entry above. `Close` of the handle a failed
  `ReadAll` leaves (`WAL.Close.specFailed`, this session) closes every file (`l.Close()`, `os.File.Close.spec`: the
  file's `os.ownFile`/`osFd`, in its stream `walFileS`) and puts the segments' halves back (`walInvBody_unpin`), so
  `ReadAll`'s decoder-error exit must keep every file's stream.
- **Evidence.** `decPost_cons_eof`'s third case (`DecLemmas.lean`): `HF` unused.
- **Proposed change.** The arm as the other two: `∃ k s off' c', ([∗list] F ∈ fs.take k, ∃ q, F.S q) ∗ ⌜…⌝ ∗
  ownDecoder d IoE eof (fs.drop k) off' c' false` (`decPost_fail` with `k = 0`, `decPost_cons_eof` adds one).
  Implies the old arm (its users drop the new conjunct).
- **Decision.** Adopted (internal, the agent's; the same change as the I/O arm's, already adopted).

## 2026-11-14: `ZeroToEnd.specWalTail`/`Fdatasync.specWalPend` (internal, the part's) -- the error arms lose the tail (W4c U5, fourth session)

- **Spec.** `LinuxFs/Spec/.../wal/ReadAllTailCallees.lean`: both posts' error arm is `⌜err ≠ nil⌝` (resp. `⌜e ≠
  0⌝`) alone.
- **Defect.** `ReadAll`'s two exits after these errors (S/wal.go, the `ZeroToEnd` and the fdatasync after it) leave a
  handle whose `Close` (`WAL.Close.specFailed`, stated this session) runs `w.sync()`, i.e. `fileutil.Fdatasync` of the
  tail, and closes its lock's file: it needs the tail's `os.ownFile`/`osFd` and halves, and the generation's lock
  token comes back only if the tail can be put back into `walInv`. With the tail lost, `Close.specFailed` is
  unprovable on those exits.
- **Evidence.** `ZeroToEnd.wp_specWalTail` (`ZteWalTail.lean`): `ZeroToEnd.specAu`'s error arm returns the file, the
  fd, the key and record (`growTie`), the `OsMeta` and the bytes past the offset; the proof drops them.
- **Proposed change.** (a) The error arms return the tail (`∃ o' m' bs`, file, fd, offset `o'`, the lent token, the
  halves, the record), with a law putting back a tail left in a resize window or after a failed fdatasync (none
  exists: the same gap as `Repair`'s failure arms); or (b) leave them, and `Close.specFailed`'s post may lose the
  lock token after these two exits (as `Repair.spec`'s `false` arm), which the tester's `restartRead` (it calls
  `Repair` after a `nil` `Close`) cannot meet.
- **Decision.** (a), the coordinator's (2026-11-14, W4c U5 fifth session). Made (branch `wal-u5e`): the error arm
  of `specWalTail` returns `walTailPE` (`HandlePend.lean`: file, fd, some offset, the lent token of kind
  `false` (`ZeroToEnd`'s first step made it), the halves of some `OsMeta` and bytes with `TailMetaE o0`: all the
  bytes, no mappings, at least `o0` long, the length word at `o0` zero; and the record), over the entry below on
  `ZeroToEnd.specAu`; `specWalPend`'s error arm returns its `walTailP` unchanged (`wp_tailFsyncP` already gave
  it back). `ReadAll` still drops both (the ten exits' `walReadFailedF` body is task 4). The invariant steps
  for `Close` to put such a tail back are not made yet (W4c U5 log, fifth session: the lent tail's fdatasync in
  a window with no zeros past `wr`, `TailPend`).
  And `specWalPend`'s success arm gives `walTailW … TailMetaS` (was `TailMeta`; the synced bytes are durable),
  for the put-back of the exits after it (`walInvBody_untail` takes `TailMetaS`); `ReadAll` weakens it at once
  (`walTailW_mono`). Internal, the agent's.

## 2026-11-14: `ZeroToEnd.specAu` (`fileutil`, the part's) -- the error arm says nothing of the bytes (W4c U5, fifth session)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ZeroToEndAu.lean`, the error arm: some offset,
  `OsMeta` `m'` (`o ≤ m'.size`, the mappings) and `m'.size - o` bytes `ys` from `o`, nothing of their values.
- **Defect.** `Close` of the handle `ReadAll` leaves after a failed `ZeroToEnd` (entry above, option (a)) must
  sync the tail and put it back; the tail's layout may have no F-Z (`TailPend`: a torn frame past `wr`), and the
  synced layout's `tailStop` then needs the length word at `wr` zero, which only the handle's bytes show.
- **Evidence.** `ZeroToEnd.wp_proofAu`'s four error exits: the seek's (bytes unchanged), the truncate's not
  landed (`ftUndoneH`: `xs'.map Prod.fst = xs.map Prod.fst`), the truncate's landed (no bytes past `o`), the
  growth's (`osZerosA`).
- **Proposed change.** The arm's pure part gains `ys.map Prod.fst = xs.map Prod.fst ∨ ∀ y ∈ ys, y.1 = 0`.
- **Decision.** Adopted (internal, the agent's: a proved spec, its only user `ZeroToEnd.wp_specWalTail`); made.

## 2026-11-14: `WAL.Close.specFailed` (the part's, stated W4c U5 fourth session) -- the token back whatever `Close` answers (W4c U5, fifth session)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__CloseFailed.lean`: post `walUnlockedTok ∗
  osCallPerm ½` for every `err`, as `Close.specOpening`.
- **Defect.** With option (a) above, a failed `ReadAll` may leave its tail in a resize window (`ZeroToEnd`'s
  truncate or growth failed) or unsynced (the fdatasync after it failed); `Close`'s `w.sync()` is then the only
  step that can make it exact, and the unregistration needs the WAL's `TailIdle` (`walTailsRes`'s
  `WalTailIdle`). When that fdatasync fails, `Close` returns its error before the locks and the tail stays lent
  in its window: the token cannot come back. Unprovable as stated.
- **Evidence.** `walTailsRes_close`/`walTailsRes_closeL` (`CloseLaw.lean`, `UnregLent.lean`) take `TailIdle`;
  `WAL.Close.spec` loses the token on `sync`'s error for the same reason.
- **Proposed change.** Post `(walUnlockedTok ∗ osCallPerm ½) ∨ ⌜err ≠ nil⌝`. Its client, the tester's
  `restartRead` (`examples/etcd/wal/wal.go:195-197`), fails the read on a non-nil `Close` and calls `Repair`
  (which takes the token) only after a nil one, so it needs only the left arm on `nil`.
- **Decision.** Adopted (the agent's: the spec is stated, unproved, not in the Link; no client proved over it);
  made.

## 2026-11-14: `walOpenWFU`, `WAL.Close.specU`, `WAL.sync.specC`, `renameWALPost` arm 2 (internal, the part's) -- `Create`'s name registered only at success (design P; unit `create`)

- **Spec.** `walOpenWFU` (`Handle.lean`, sealed), `LinuxFs/Spec/.../wal/WAL__CloseU.lean`, `WAL__syncC.lean`'s
  error arm, `WAL__renameWAL.lean`'s `renameWALPost` arm 2 (so `renameWALUnlock.spec`'s too).
- **Defect.** `Create`'s cleanup renames `nm` aside, which `os.Rename.specDirAnySnc` allows only with the whole
  claim on `nm`; but `walOpenWFU` held the name registered (`walNamesFrag none`), whose registration lent a
  fraction to `nameShare` that is never given back whole (borrowers drop what they borrow): no state after
  `Close.specU` lets `Create` call the rename (W4 log, twenty-sixth and twenty-seventh sessions).
- **Evidence.** `nameShare`'s `∃ q`, `walInv_dirPath`; `Close.specU`'s proof dropping the handle's and the
  pipeline's paths.
- **Change (made).** Design P (`notes/wal-units/create.md`): the handle before naming carries the pending
  registration (`walDirH`'s new names-fragment parameter `nf := some dir`) and its two paths to `dir` pinned at
  `Create`'s spine-law roots and fraction (`walOpenWFU P Mr w dir Rp qp`; `walDirH`'s naming fact a function of
  the path's roots and fraction, `walPipeH`'s new pin `pp`; all defaulted, so every other handle is unchanged).
  `Close.specU` returns `walUnlockedTokX` (the free token less its names fragment), `walNamesFrag (some dir)`
  and the two pinned paths (error arm: `walLockedTok ∗ walNamesFrag (some dir)`); `sync.specC`'s error arm
  returns the handle's names fragment `nf` too; `renameWALPost` arm 2 returns the pinned pending handle
  (`∃ x qd, ⌜dq = own qd⌝ ∗ UH x ∗ walOpenWFU P Mr w' dir R qd`). `Create` registers the name at its success
  exit, after the parent's close (`walInv_named`, `walInv_register`, `walOpenWFU_seal`).
- **Decision.** Made (internal: no client spec moves; `Create.spec` unchanged).
## 2026-11-14: `member.save.spec` (the tester's, W4c U5) -- the post drops the handle's written length, which `sync` takes (W4c U5, ops)

- **Spec.** `LinuxFs/Spec/github_com/mit_pdos/etcd_grove/examples/etcd/wal/member__save.lean` (and `MemberRep`'s
  `memSaveRes`/`memSavePost`): the true arm gives the handle, `tMemOk`/`tMemHs` of the new WAL state `d'` and
  the candidate's synced mark, not `walLenLb w dir |d'.H|`.
- **Defect.** `member.sync.spec` and `WAL.Sync.spec` take `walLenLb w dir |d.H|` of the current state, so no
  member operation after a `save` can call `sync` (`opRecvSnap`'s last call; `step`'s `sync`).
- **Evidence.** `WAL.Save.spec`'s success arm returns `walLenLb w dir (|d.H| + 1)` (`Hlen1` in
  `member.save.wp_proof`), which the proof dropped; the empty save keeps `d`, for which no length was in the
  precondition.
- **Proposed change.** The precondition (and `memSaveRes`) gains `walLenLb w dir |d.H|`, the true arm (and
  `memSavePost`) `walLenLb w dir |d'.H|`. Its provider at a restart or `Create` is the open handle's
  (`Open`/`ReadAll`, `Create`): an obligation of `restart`/`Boot`.
- **Decision.** Adopted (internal, the agent's: a strengthening of a proved spec of our own example, its only
  clients `opTerm`/`opCommit`/`opEntries`/`opResend`/`opRecvSnap`, all re-proved); made.

## 2026-11-14: `tOpWf` and `member.save.spec` (the tester's, W4c U5) -- a save's hard-state term unbounded, so a restart cannot re-establish the member's fields (W4c U5, restart)

- **Spec.** `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/Defs.lean`'s `tOpWf` (a save's entries
  `tEntWf`, a snapshot's index and term below `2^63`; nothing on a save's hard state) and
  `TS/member__save.lean` (premises `tMemOk`, `tMemHs`, the entries' `tEntWf`, the sizes).
- **Defect.** After a restart the member's term is the read hard state's (`resume`), and `memLive` (`MemberInv`,
  the form the operations take) asks it below `2^63` (`tMemFields`); the read's hard state is the history's last
  save's, whose term nothing bounds, so `restart` could not give `memLive`.
- **Evidence.** `notes/wal-units/ops.md`, "For `restart`'s author"; `tMemFields_read` (`RestartLive.lean`) needs
  the bound (`tLastHS_term`).
- **Proposed change.** `tOpWf` gains a third clause, `o.snap = false → uint.nat o.hs.term' < 2 ^ 63`;
  `member.save.spec` the premise `uint.nat h.term' < 2 ^ 63`; its callers supply it: `opEntries` (its `t <
  2^63`), `opRecvSnap` (`memLive`'s `tMemFields`), and new premises `uint.nat t < 2 ^ 63` of `opTerm`/`opCommit`
  and `tMemFields t M` of `opResend` (all three implied by `memLive`, the form `step` will take).
- **Decision.** Adopted (internal: the tester's own definitions and specs, recommended by the ops agent and
  delegated to the restart path by the coordinator); made, every client re-proved.

## 2026-11-15: `WAL.cleanupWAL.spec` (new, internal, the part's) and `wal.Create.wp_proof`'s callees (unit `create`, session 3)

- **Spec.** `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cleanupWAL.lean` (new); the binders of
  `wal.Create.wp_proof` (`LinuxFs/Proof/.../wal/Create.lean`).
- **Defect.** `Create`'s error exits after its commit run the deferred `cleanupWAL`, which had no spec.
- **Evidence.** S/wal.go `cleanupWAL` (the fork's fix: it returns its error); `Create`'s deferred closure.
- **Change (made).** `cleanupWAL.spec` over the handle before naming (`walOpenWFU`), with a caller law
  (`cleanupLaw`) for the rename (`os.Rename.specDirAnySnc`'s precondition at the timestamp, and a continuation
  from its post, both with `notCrashed`); three outcomes (sync failed; `Close` returned an error; the law's
  `Fin err`). Proved over `Close.specU`, `time.Now`, `time.Time.Format.specBroken`, `fmt.SprintfBroken.spec`,
  `os.Rename.specDirAnySnc`, zap. `wal.Create.wp_proof` takes `cleanupWAL.spec` and `fmt.ErrorfAny.spec` (both
  proved; in the Link `wal.wp_Create` now reaches the pending hypotheses `h_fmt_SprintfBroken` and
  `h_time_Time_FormatBroken`). `Create.spec` unchanged.
- **Decision.** Made (internal). The law's proof (`create_cleanupLaw`, `sorry`) is blocked on two invariant
  changes (a pin for the rename's area claim; the moved-aside step with the pending WAL known unnamed):
  `notes/wal-units/create.md`, session 3; left to the coordinator.

## Proposed by specgap (2026-11-15; unit `specgap`, `notes/wal-units/specgap.md`; nothing made)

Draft entries, in priority order, from comparing the part's `fsExt` WAL specs with what etcd's server needs
(SpecPlan's storage and boot specs, `examples/specreq/etcdserverboot/`, the Go at `0b50f0426`). Each waits for the
coordinator, and those marked [user] for the user. `Sp/` = `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`,
`S/` = `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`, `SP/` = `SpecPlan/Spec/go_etcd_io/etcd/server/v3/`,
`RI` = `notes/wal-crash-handoff/restart-wal-interface.md`; Go paths are in the fork's server module.

## 2026-11-15: the server's storage specs (`SP/storage/storage__{Save,SaveSnap,Sync,Release,Close}.lean`) and etcd's `lg.Panic` on WAL errors -- `diskOk` cannot refute an `fsExt` error arm (P1)

- **Spec.** `SP/storage/storage__*.lean` (`RET #GoInterface.nil` under `⌜diskOk⌝`); the part's `wal.Create.spec`,
  `WAL.{Save,SaveSnapshot,Close,ReleaseLockTo}.spec` (honest error arms).
- **Defect.** SpecPlan too strong over `fsExt`: every system call may fail with any errno (`GooseLang/Ext/Fs/Impl.lean`,
  "Environmental failure"), so the WAL's error arms are reachable and a pure premise `⌜diskOk⌝` refutes none of them.
  Where the server `Fatal`s (raft loop `etcdserver/raft.go:257,264,279`; `openWALFromSnapshot`) honest arms are
  enough. Where it `lg.Panic`s, a no-panic theorem is false in the model: `bootstrapNewWAL`'s `Create`
  (`bootstrap.go:719`), `snapshot()`'s `SaveSnap`/`Release` (`server.go:2147,2151`), `applySnapshot`'s `Release`
  (`:1111`), `onStop`'s `Close` (`raft.go:441`), and `Reopen` (`storage/wal/wal.go:284`).
- **Evidence.** The Go sites above; `notes/wal-fsext-plan.md` §5 Q6 ("the server keeps `walSaveOk` as its own premise
  at C6"), which no Iris proof can use against an error the spec returns.
- **Proposed change.** [user] One of: (a) a failure ledger in `fsExt` (a ghost flag set by any failing call; the
  adequacy theorem conditioned on it staying unset), a trusted change; (b) fork changes `lg.Panic` → `lg.Fatal` at the
  five sites; (c) a closed theorem that exempts a panic after an I/O error. Then SpecPlan's storage specs get error
  arms (handle lost) and `diskOk` keeps only what (a) makes checkable.
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.{Save,SaveSnapshot,ReleaseLockTo,Sync}.spec` -- an exclusive handle, but the server calls them concurrently under a read lock (P2)

- **Spec.** `Sp/WAL__{Save,SaveSnapshot,ReleaseLockTo,Sync}.lean` (each takes `walOpenWF P Mr w dir`, exclusive);
  `SP/storage/Api.lean` (`isStorage` persistent, `storageOpen` fractional).
- **Defect.** Too weak for the server. `storage`'s methods take `st.mux.RLock` (`storage/storage.go`). The raft loop
  (`Save`, `SaveSnap`, `Sync`) and the apply thread (`snapshot()`'s `SaveSnap`/`Release`, `applySnapshot`'s
  `Release`) call them concurrently, and the WAL serializes them with `w.mu`. No client can thread an exclusive
  handle through read locks. `WAL.Sync` takes no lock at all (`wal.go:994`), and races with `ReleaseLockTo`'s write
  of `w.locks` (`wal.go:1039`), which `sync()`'s `tail()` reads: a candidate Go data race (specgap §3.1).
- **Evidence.** `etcdserver/raft.go:257-279`, `server.go:1111,2147-2151`, `server.go:990-1002` (the apply thread
  snapshots after `raftAdvancedC`, while the raft loop moves on to the next `Ready`).
- **Proposed change.** A shared-handle layer: `walOpenS w dir q` (fractional), with the handle in `w.mu`'s invariant.
  `Save`/`SaveSnapshot`/`ReleaseLockTo` take a fraction (their AUs already commit right after `w.mu.Lock()`), and
  `Close` takes all. For `Sync`: a fork fix (`Sync` takes `w.mu`) [user: the fork], after a `-race` test; or
  `storage.Sync` takes the write lock (also a Go change).
- **Decision.** Proposed.

## 2026-11-15: `walAreaOk`/`walAreaRes`/`AreaSlot`/`walBoot0`/`walBootCrash` (the part's) -- the area's slots and root do not fit etcd's member directory (P3)

- **Spec.** `S/Inv.lean:518` (`AreaSlot`: every `walNameOk` name and `nm.<sfx>`), `S/CreateDefs.lean:146`
  (`walAreaRes`), `S/Boot0.lean:89` (`hr`: the area a root; `hslots`), `S/BootCrash.lean:395` (`bootWals`),
  `DirsRoots`.
- **Defect.** Too strong for the server (W4c U1 mismatches 1 and 4):
  - `snap` is a slot, so `member/snap` (created by `bootstrapSnapshot`'s `TouchDirAll`, `bootstrap.go:211`, before
    the WAL) breaks `hslots`; `walBootCrash` would take it for a WAL; and the invariant holds half the area's claim
    on it.
  - The area must be an existing root, yet the first start creates `member/` (`bootstrap.go:68`) and probes
    `DataDir` above it (`:64`).
  - Durable directories must be roots, so `member/snap` cannot be durable.
  - `IsDirWriteable(WALDir)` (`:85`) writes `member/wal/.touch`, whose claim the invariant owns (`walOthersL`).
- **Evidence.** The definitions above; `GooseLang/Ext/AbsDisk/Paths.lean:34` (`walNameOk`); `notes/wal-fsext-w4c-plan.md`
  U1 log, mismatches 1 and 4; U3 log, premise 3.
- **Proposed change.** `AreaSlot` and `walAreaRes` take the WAL's name `nm` (slots `nm`, `nm.<sfx>`); every other
  name of the area goes to the client at boot. Allow a durable directory below a root through spine claims (or make
  the data directory the root, the area below it). Add a law lending a WAL directory's `.touch` to a client probe.
  World premises of the server's closed theorem: the data directory exists, clean and absolute; `DedicatedWALDir = ""`.
- **Decision.** Proposed (statement changes to the WAL's client vocabulary: the coordinator's; the boot premises: the
  user's at C6's closed theorem).

## 2026-11-15: the part's `wal.{Exist,ValidSnapshotEntries,Open,OpenForRead,Repair}.spec` -- `osCallPerm 1` with no directory operation (P4)

- **Spec.** `Sp/{Exist,ValidSnapshotEntries,Open,OpenForRead,Repair}.lean` (each takes `osCallPerm 1`).
- **Defect.** Too strong for the server. Once bbolt runs over `fsExt`, the backend's commit goroutine holds a share
  of the permission from `bootstrapBackend` on, and the server calls VSE (`recoverSnapshot`, inside
  `bootstrapBackend`), `Open`, `Repair` and `Create` after the backend is open. Only `Create` does a directory
  operation (a rename, `mkdir`, `RemoveAll`).
- **Evidence.** `bootstrap.go:77-89, 451, 675, 689, 717`; `LinuxFs/Spec/os/{Rename,Mkdir,RemoveAll}.lean` (the
  operations that need `osCallPerm 1`).
- **Proposed change.** The five take `osCallPerm q` for any `q` (`Open`: a third or a quarter each to the pipeline
  and the handle, the rest back). `Create` keeps `1`: the server must make the backend quiescent at
  `bootstrapNewWAL`, by a backend-side protocol returning its share, or by a fork reordering [user].
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.Save.spec`/`WAL.SaveSnapshot.spec` (through `walEntsIn`, `walSnapAt`, `Mr`) -- canonical contents only; raft's entries and the restarted server's conf state are not canonical (P5)

- **Spec.** `Sp/WAL__Save.lean` (`walEntsIn P`, `Mr.encEntry`), `Sp/WAL__SaveSnapshot.lean` (`walSnapAt Mr sp md cs`:
  bytes `= Mr.encSnap md`), U4's instance `S/RaftModel/{Codec,Pb}.lean` (`walCsCanon`: `AutoLeave` set).
- **Defect.** Too strong for the server:
  - Entries: already recorded by U4b (`notes/wal-fsext-w4c-plan.md`, U4 b log, task 4). Raft's entries keep the
    proposal's presence.
  - New here, the conf state: after a restart `ep.confState` is `buildConfStateFromV3store`'s
    `ConfState{Voters, Learners}`, with `AutoLeave` nil (`bootstrap.go:145`, `server.go:804`). The apply thread's
    first `snapshot()` before any conf change saves it (`CreateSnapshot(…, ep.confState, …)`, `storage.SaveSnap`
    → `walpb.Snapshot{ConfState: …}`). Its bytes are not `walCsCanon`'s, so `walSnapAt` fails.
- **Evidence.** The Go above; `walSnapCanon`/`walCsCanon` (`S/RaftModel/Codec.lean:42`).
- **Proposed change.** [user: the representation] `Mr.encEntry`/`Mr.encSnap` (or `P.entIn` and `walSnapAt`) over
  wire contents (`EntryC`, `WalSnapC`), the history keeping only what readers decode (the index and term for
  snapshots). Narrow alternative for the conf state: a fork fix setting `AutoLeave` in `buildConfStateFromV3store`.
- **Decision.** Proposed.

## 2026-11-15: the part's `wal.Create.spec` (with `wal.Exist.spec`) -- `Exist`'s `false` does not give `Create`'s `walAbsent` (P6)

- **Spec.** `Sp/Create.lean` (AU from `walAbsent dir`), `Sp/Exist.lean` (`b = false → ExistFalseOk o`: none, or fresh
  and unnamed).
- **Defect.** Too weak, composed: `bootstrap` calls `Create` exactly when `Exist` returned `false`
  (`bootstrap.go:77` → `bootstrapNewWAL`). A fresh unnamed WAL survives a crash (`walCrash` keeps `named = false`
  images), so `ExistFalseOk`'s second case cannot be excluded at a boot, and `Create`'s AU cannot be fired.
- **Evidence.** `GooseLang/Ext/AbsDisk/Impl.lean:223` (`walCrash`); the two specs.
- **Proposed change.** `Create`'s AU starts from `walDirIs dir o ∗ ⌜ExistFalseOk o⌝` (an existing fresh WAL at `dir`
  makes `Create`'s own `Exist` check return `ErrExist`, uncommitted; a moved-aside one is replaced). Alternatively,
  `Exist`'s `false` gives `o = none` once the ENOENT model fix lands and the moved-aside state is in the invariant
  (the `create` unit's cleanup design).
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.Close.specFailed` with `wal.Repair.spec` -- `openWALFromSnapshot` ignores `Close`'s error, then needs the token (P7)

- **Spec.** `Sp/WAL__CloseFailed.lean` (`(walUnlockedTok ∗ osCallPerm ½) ∨ ⌜err ≠ nil⌝`), `Sp/Repair.lean` (takes the
  token).
- **Defect.** The server's restart cannot be proved on this path: after a failed `ReadAll` it calls `w.Close()`,
  ignores the error, and calls `wal.Repair` (`bootstrap.go:683-689`). On `err ≠ nil` the token is lost. In Go,
  `Close` returns before unlocking (`wal.go:1053-1066`) and `Repair`'s blocking `LockFile` hangs: a hang, which
  only a lock model could show.
- **Evidence.** The Go above; ledger 2026-11-14, "`WAL.Close.specFailed` … the token back whatever `Close` answers".
- **Proposed change.** [user] Either the lock model (Q1), with `Repair` not needing the token; or a fork fix:
  `openWALFromSnapshot` `Fatal`s on `Close`'s error (specgap §3.2, to report).
- **Decision.** Proposed.

## 2026-11-15: the server's purge (`SP/etcdserver/EtcdServer__purgeFile.lean`) and `storage.MinimalEtcdVersion` -- no `fsExt` statement without locks (P8)

- **Spec.** `SP/etcdserver/EtcdServer__purgeFile.lean`, `SP/storage/storage__MinimalEtcdVersion.lean`; the part's
  `WAL.ReleaseLockTo.spec` (`unl` bookkeeping).
- **Defect.** `purgeFile` (`fileutil.PurgeFileWithDoneNotify`, `server.go:608`) deletes the oldest unlocked
  segments. `fsExt` has no lock state, so neither the purge nor `ReleaseLockTo`'s `unl` has content (`RI` gate 8).
  `Reopen` (`MinimalEtcdVersion`) releases every lock while the purge runs (suspected window, specgap §3.3).
- **Proposed change.** [user, `notes/wal-fsext-plan.md` §5 Q1] The lock model. Until then C6 states the purge as a
  hypothesis or drops it from the closed theorem.
- **Decision.** Proposed.

## 2026-11-15: the part's `WAL.ReleaseLockTo.spec` -- the post does not exclude an error, and the server panics on one (P9)

- **Spec.** `Sp/WAL__ReleaseLockTo.lean` (post `walOpenWF ∗ ∃ d, Q d` for every `err`).
- **Defect.** Too weak: `storage.Release`'s callers `lg.Panic` on any error (`server.go:1111,2151`). The only error
  is `parseWALName` rejecting a lock's file name, which the invariant rules out (every lock is a segment at a
  `walNameStr` name).
- **Proposed change.** Post `⌜err = GoInterface.nil⌝ ∗ walOpenWF ∗ ∃ d, Q d` (the proof's error exit refuted by
  `WalDirClaim`).
- **Decision.** Proposed (internal strengthening; no client yet).

## 2026-11-15: the part's `WAL.ReadAll.spec` -- the hard state and the entries come back read-only, and `ForceNewCluster` mutates them (P10)

- **Spec.** `Sp/WAL__ReadAll.lean` (`P.hsIn hp σ.hs`, `sl ↦*□ esL`).
- **Defect.** Too weak for `bootstrapWALFromSnapshot`'s `ForceNewCluster` path: `bwal.st.Commit = …`
  (`bootstrap.go:640,787`), and `append(wal.ents, ents...)` (`:781`) may write into the slice's capacity. `ReadAll`'s
  `state` is a fresh unmarshalled object (`w.state` is a clone, `wal.go:649`), so the client may own it.
- **Proposed change.** The success arm gives `HsO hp σ.hs` (owned; `WalHsOwn.freeze` turns it into `P.hsIn`) and the
  slice's ownership with its capacity.
- **Decision.** Proposed (low priority: `ForceNewCluster` only).

## 2026-11-15: `SP/storage/wal/Api.lean` (`Wal.Recs`, `walRecs`, `walWriting`, `walCreating`, `walPurgeRight`) and `SP/storage/storage__Close.lean` -- the trusted record model against the proved WAL (P11)

- **Spec.** SpecPlan's WAL vocabulary and its crash laws (`walRecs_crash`, `walWriting_crash`, `walCreating_crash`);
  `storage.Close.spec` (returns `walPurgeRight`).
- **Defect.** The model is trusted, yet the WAL is now proved. Its σ-level `Recs` updated by `save` is not
  compositional for the real read (`RI` §2: `walKeep` uses the history's final commit). `walWriting` and
  `walCreating` are two-step shapes that `fsExt`'s single commit replaces. `Close` returning the purge right is
  stronger than any user needs, and `fsExt` consumes it.
- **Proposed change.** `walRecs wd R := ∃ d, walDiskAt wd d ∗ ⌜view d = R⌝`, `walWriting` a mark below `|H|`, and
  `walCreating md := walDiskAt wd (walDurFresh md)` (`named = false`). The crash laws become lemmas: `walImg` with
  the invariant "every op past the mark is a commit-only `Save` or the write in flight" gives `Recs.crashed` and
  `crashedMid`. `storage.Close` consumes `walPurgeRight`. Coordinated with P1 (error arms).
- **Decision.** Proposed.

## 2026-11-15: `SP/storage/storage__Save.lean`, `storage__SaveSnap.lean` -- missing the WAL's premises (P12)

- **Spec.** As named, against `Sp/WAL__Save.lean`, `WAL__SaveSnapshot.lean`.
- **Defect.** SpecPlan too weak in its premises: the WAL needs every entry index `< 2^64-1`, every encoding
  `< 2^40`, the snapshot's index `< 2^64-1`, and its conf state set unless the index is 0. Raft's room fact and
  proposal limits must supply them, and a received snapshot's index has no bound yet (`RI` gate 5).
- **Proposed change.** Add them as premises of `storage.Save`/`SaveSnap`, discharged in `raftNode.start` from raft's
  invariants.
- **Decision.** Proposed.

## 2026-11-15: the part's WAL -- no specs of `WAL.LatestSnapshotEntry`, `WAL.Reopen`, `wal.MinimalEtcdVersion` (P13)

- **Spec.** None yet; `SP/storage/storage__MinimalEtcdVersion.lean` is the user.
- **Defect.** `storage.MinimalEtcdVersion` (downgrade, `schema.UnsafeMigrate`) calls them. `LatestSnapshotEntry`
  calls `ValidSnapshotEntries`, whose spec takes `walUnlockedTok`, which the open handle holds.
- **Proposed change.** A VSE spec over an open handle (the handle pins the segments), then the three. Low priority.
- **Decision.** Proposed.
## 2026-11-15: `os.File.WriteAt.specExt` (lean's chunked `WriteAt`) -- its post's `OsMeta` is false under the WAL track's page cache known zero (`OsMeta.cz`) (the `lean`/`wal-int` merge, branch `wal-lean`)

- **Spec.** `Spec/os/File__WriteAt.lean`'s `specExt` (lean `6342dfeb5d`, for the bbolt port): the post's
  `osMeta d.ino 1 (pwPost m off a j)`.
- **Defect.** `wal-int`'s change to the per-byte extension's program logic (P1 of
  `notes/axiom-review/eof-page.md`, pending the user's review: the page cache known zero `OsMeta.cz`, raised by a
  `pwrite` that lands all its data, `pwCz`) makes the `OsMeta` a chunked write
  leaves remember the last chunk that landed whole: after a first chunk landed whole and a later one short,
  the ghost `cz` is the first chunk's raise, not `pwPost`'s (`pwCz m off a j`, no raise unless the whole write
  landed). Lean's `specExt` was proved over the base semantics, without `cz`.
- **Evidence.** `Proof/os/WriteChunks.lean`'s `pwPost_chunk` leaves the goals
  `(pwPost (pwPost m off a j) (off + nn) cs k).cz = (pwPost m off (nn + cs) (max j (nn + k))).cz` (false when
  `j = a < nn + cs` and the first write raised `cz`) and the same for `rz`; the WAL track met the same in its own
  chunked spec and states it with `os.pwPostE m off A j E` (`Spec/os/WriteLong.lean`, `specLong`: `cz :=
  pwCz m off E E`, `E` the last whole chunk's end).
- **Proposed change.** `specExt`'s post as `specLong`'s: `∃ E, E ≤ j ∧ (j = a → E = a) ∧ ...` and
  `osMeta d.ino 1 (os.pwPostE m off.toNat a j E)` (and `rz` likewise, to check); `WriteChunks`' chunk lemma
  as `WriteLongStep.pwPostE_step` over `pwrite` anywhere; the bbolt port's six users of `specExt`
  (`Proof/go_etcd_io/bbolt/{Tx__write,Tx__write_ext,Commit/WriteRun,Commit/PwMeta,Commit/WriteExtRun,
  Commit/MetaBytes}.lean`) re-proved over `pwPostE`. Meanwhile `specExt`'s proof is split to
  `Proof/os/File__WriteAtExt.lean` (it does not build) so that the WAL does not wait on it.
- **Decision.** Restated as specLong's post; coordinator, 2026-11-15. Done on `wal-lean`: `specExt`'s post is
  `∃ j a E ys, ... E ≤ j ∧ (j = a → E = a) ∧ ...` with `osMeta d.ino 1 (os.pwPostE m off a j E)` (`rz` needed
  nothing: `pwPost` keeps it); `WriteChunks.pwPost_chunk` (false) is gone, replaced by
  `File__WriteAtExt.pwPostE_chunk` (with `pwCzE_stepG`, `pwCzE_step` for a write anywhere); the bbolt
  port's users (`Tx__write`, `Commit/WriteExtRun`, `Commit/PwMeta`'s `pwPostE_inside`) take the `E`; the
  others (`Tx__write_ext`, `Commit/WriteRun`, `Commit/MetaBytes`) needed nothing.

## 2026-11-15: `SP/storage/storage__MinimalEtcdVersion.lean` -- no panic under `diskOk`, false while the purge runs

- **Spec.** `storage.MinimalEtcdVersion.spec` (SpecPlan): returns without panicking under `diskOk`.
- **Defect.** `MinimalEtcdVersion` reopens the WAL (`w.Reopen`), releasing every segment lock, while the server's
  purge (`fileutil.PurgeFileWithDoneNotify`, `--max-wals`) may delete or lock segments the reopen needs; the
  reopen then panics.
- **Evidence.** `issues/etcd-storage-downgrade-reopen-purge-panic.md` (test reproduces the panic 5/5 at upstream
  main `260e4e0457aa`, 3/3 at the fork `3df9b265f`).
- **Proposed change.** Either the spec takes "no purge runs" (a premise the server's downgrade path would have
  to establish), or the fork reads the entries through `wal.OpenForRead` instead of reopening (the issue's
  proposed fix, untested), after which the spec stands.
- **Decision.** Proposed (with specgap's P8, the lock model, and P13).

## 2026-11-15: `LinuxFs/Spec/.../examples/etcd/wal/restartRead.lean`, `member__restart.lean` -- `m` not known non-nil

- **Spec.** `restartRead.spec`, `member.restart.spec` (the WAL tester).
- **Defect.** Unprovable: `restartRead` tests `m != nil`, and the field points-tos `m.[member, f] ↦ _` do not
  give `m ≠ null`.
- **Evidence.** `restartRead.wp_proof` (branch `wal-c-tester2`) needs it at the `if m != nil`.
- **Proposed change.** Premise `m ≠ null` on both (every caller allocated `m`: `Boot`'s `&member{...}`).
- **Decision.** Made (branch `wal-c-tester2`, `notes/wal-units/tester.md`, ninth session).
## 2026-11-15: the WAL invariant for `Create`'s cleanup (unit `create`, session 4; the coordinator's decisions)

- **Spec.** `LinuxFs/Proof/.../wal/Inv.lean` (`walNamesRes` takes `s`, the pending WAL unnamed; `WalsAt`
  weakened; `CreatingOk`'s `CreatingNew` guarded by `dir ≠ cleanKey`), `Ghost.lean` (`walCreatingAuth`'s
  cleanup pin, `walCreating` carrying `dir ≠ cleanKey`, `walCleanPin`), `CreateDefs.lean`/`CreateArea.lean`
  (`walAreaRes`/`AreaOk` exempt `BrokenSlot` names); the internal step lemmas `walInvBody_named`/`walInv_named`,
  `walInvBody_namedBy`/`walInv_namedBy` (take and return `walNamesFrag none`), `walInvBody_register`/
  `walInv_register` (premise `∃ J, hn.cur !! nm = some (.dir J)`), `walInvBody_mint`/`walInv_mint`
  (`dir ≠ cleanKey`), the area steps' `hT` (against `walUnlockedTokX`).
- **Defect.** `create_cleanupLaw` could not be proved: the rename's update could not find the invariant's half
  of its area claim (no pin), and a rename that took effect broke `WalsAt`, `walAreaRes`'s `SubCover` and, with
  the WAL possibly named, `CrashTo`.
- **Evidence.** `notes/wal-units/create.md`, sessions 3 and 4.
- **Change (made).** As listed; `Create` registers before it names. No client-facing spec changed.
- **Decision.** The coordinator's (decisions 1 and 2 of session 3); made, every importer rebuilt, both `sorry`s
  proved.

## 2026-11-15: the conf-state half of "canonical contents only (P5)" above -- withdrawn: the restarted server's `ep.confState` has `AutoLeave` set

- **Spec.** The entry above (`WAL.SaveSnapshot.spec`'s `walSnapAt`/`walCsCanon`), and the SpecPlan's
  `confStateFull` for `ep.confState` (`ApiApply.lean`'s `applyThread`, `raftNode__ApplyConfChange`,
  `EtcdServer__createMergedSnapshotMessage`, `EtcdServer__snapshot`).
- **Defect.** None: the reported one does not exist. `buildConfStateFromV3store`'s `ConfState` (`AutoLeave` nil)
  reaches the apply thread only through the `MemoryStorage`: `bwal.MemoryStorage()` → `ApplySnapshot`
  (`EnsureSnapshot`, then `proto.Clone`), and `run`'s `ep.confState` is `raftStorage.Snapshot()`'s
  (`EnsureSnapshot` again, a clone). `CreateSnapshot` clones it, so `SaveSnap` hands the WAL a full conf state.
- **Evidence.** `bootstrap.go:107-115, 571, 741-753`; raft `storage.go:119-126, 208-214, 218-237, 243-262`;
  `server.go:755, 803-809, 1175, 2053, 2132`. Measured against the pinned raft (`565c2bd`): bootstrap's `cs`
  has `AutoLeave` nil, `MemoryStorage.Snapshot()`'s and `CreateSnapshot`'s have it set
  (`notes/wal-units/autoleave.md`).
- **Proposed change.** None to the specs. P5 stays for entries only. The user's decision of 2026-11-15
  (generalize, do not insist on `AutoLeave`) was taken on the false reading: reopened as options in
  `notes/wal-units/autoleave.md` (recommended: keep the specs).
- **Decision.** Proposed (unit `autoleave`).

## 2026-11-15: `applyInit_ep.spec` (`SpecPlan/.../etcdserver/ApiApply.lean:724`) -- `ep.confState` from nowhere

- **Spec.** `applyInit_ep.spec`: `applyInit s γ p c ∗ ep's five fields ↦ … ∗ ep.confState ↦ cs ⊢ |==> applyThread s γ ep p`.
- **Defect.** Unprovable: `applyThread`'s realization holds `ep.confState` as a `RaftPb.confStateFull` listing the
  configuration at the consistent index (`confAt γ.raft ci m`), but `cs` is arbitrary and nothing is given about
  it. `run` has the `MemoryStorage` snapshot's `snapshotPts` (step 1) and drops it (step 5).
- **Evidence.** `ApiApply.lean:51, 97, 724-732`; `EtcdServer__run.lean` steps 1 and 5; Go `server.go:755, 803-809`.
  That the snapshot's conf state lists the configuration at `c` is bootstrap's doing (rebuilt from the backend,
  at `c`; `bootstrap.go:107-115`), which no SpecPlan statement carries to `run`.
- **Proposed change.** `applyInit_ep` also takes the conf state's holding, `RaftPb.confStateFull cs dq csm`
  (from `MemoryStorage.Snapshot`'s `snapshotPts` by `snapshotPts_unfold`), and a tie of `csm` to the configuration
  at `c`: either `applyInit` gains the membership (`applyInit s γ p c m`, with `⌜csm.Is m⌝` here; `start`'s
  `srvRunTok_intro` and `NewServer` supply `m` from bootstrap), or `applyInit` holds the `MemoryStorage`
  snapshot's model and the law takes `snapshotPts` itself. For batch 2d/2e's owners.
- **Decision.** Proposed (unit `autoleave`, found while answering where `ep.confState` comes from).
## 2026-11-15: error-free WAL specs under `NoIoErr` (unit `noioerr`) -- three obstacles

- **Spec.** The planned `WAL.SaveSnapshot`/`ReleaseLockTo`/`Close`/`Create` `.specNoErr` variants (none
  stated yet); `encoder.flush.specP`, `encoder.encode.specG`; `os.File.Write.wp_empty`.
- **Defect.** (1) `flush.specP`'s error arm is `B out pend` for any `pend`: with nothing pending (no write
  made, Go's `PageWriter.flush` returns `0, nil`) the spec still allows an error, so an error-free `sync`
  cannot be derived from it; `encode.specG`'s error arm likewise allows `b = []`. (2) An empty
  `(*os.File).Write`'s errno is arbitrary with no `fsExt` step (trusted model), which `NoIoErr` cannot
  exclude. (3) `ReleaseLockTo`'s only error is `parseWALName` on a lock's name, which the handle does not
  record as a WAL name: not an I/O error.
- **Evidence.** `notes/wal-units/noioerr.md`, "What is left".
- **Proposed change.** (1) Add "`pend = [] → err = nil`" to `flush.specP` (and "nothing written → `nil`" to
  `encode.specG`), proved from the page writer. (2) For the user (trusted model). (3) A handle fact: each
  lock's name is `walName seq idx`.
- **Decision.** Proposed.
- **Resolved (2026-11-15, unit `noioerr`, second session, `wal-c-noioerr2`).** (1) and (2) together, without
  changing a statement: new specs over a writer called only with bytes (`io.writerStreamPNE`;
  `PageWriter.flush/Flush/Write.specNE`, `encoder.flush.specPNE`, `write.specNE`, `encode.specGNE`,
  `saveCrc.specNE`), the old ones their instances. The page writer never writes an empty slice (Go:
  pagewriter.go:107-111, 86-88), so the trusted empty-`Write` branch is never reached on the WAL's paths: (2)
  needs no model change. (3) open (after `wal-c-locks`, which rewrites `walLockH`).

## 2026-11-15: `wal.Create.spec` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`) -- the update from `walAbsent` only

- **Spec.** `Create(lg, dir, md)`: `AU <{ walAbsent dir }> … <{ walDiskAt dir (walDurFresh md), COMM Q }>`.
- **Defect.** Too strong a precondition for its clients: after `Exist` answers `false`, the state is
  `ExistFalseOk` (none, or a fresh unnamed WAL), and a generation may start with a fresh unnamed WAL (the
  trusted `walCrash` keeps `named = false`; `Create` failed after its rename, `cleanupWAL`'s move aside not
  fsynced). The tester's `Boot` then calls `Create` and cannot give `walAbsent` (the tenth session's B3, whose
  premise "a crash maps an unnamed WAL to absent" is false).
- **Evidence.** `LinuxFs/GooseLang/Ext/AbsDisk/Impl.lean:230-236` (`walCrash`); `Exist.lean`'s `ExistFalseOk`;
  `examples/etcd/wal/wal.go` `Boot`; S/wal.go `Create` (its `Exist` check before any effect, `renameWAL`'s
  `RemoveAll`).
- **Proposed change.** The update from `∃∃ o, walDirIs dir o ∗ ⌜wal.ExistFalseOk o⌝` (`wal.Create.specFresh`,
  stated as a hypothesis in `CreateFresh.lean`, taken by `Boot.wp_proof`); `Create.spec` is its `o = none` case.
  Proved by the WAL layer (the creating update generalized; the invariant lets the commit replace an unnamed,
  empty WAL whose directory is not at its name). Alternatives in `notes/wal-units/tester.md`, eleventh session.
- **Decision.** Proposed (unit `tester`); until then a hypothesis of `Boot`.

## 2026-11-15: `wal.Create.spec` generalized (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Create.lean`) -- the update from any view

- **Spec.** `Create(lg, dir, md)`; follows the entry "the update from `walAbsent` only" above.
- **Defect.** The update from `walAbsent dir` only was stronger than needed; and `wal.Exist.spec`'s
  `false` arm, `ExistFalseOk o` (none or a fresh unnamed WAL), is weaker than what its proof shows
  (`o = none`: with the lock token held every present WAL is registered and `Exist` finds its segment).
- **Evidence.** `wal.Exist.wp_core`'s `b = false → od = none` (real state); `existFalseOk_of_le` only
  produces `o = none`; `notes/wal-units/fresh.md`.
- **Change made.** `Create.spec` takes `Pv : Option WalDur → Prop` and its update is from `∃∃ o,
  walDirIs dir o ∗ ⌜Pv o⌝` (given back by the error arm that commits nothing); `Create` finds the real
  state empty from its own `Exist` (`walAreaResFree`) and the lock token (`walCreating_absent`).
  `Create.specFresh` is its instance at `ExistFalseOk`, proved (`wal.Create.wp_specFresh`), no longer a
  hypothesis of `Boot`. Proposed, not made: `Exist.spec`'s `false` arm strengthened to `o = none`
  (closes specgap P6).
- **Decision.** Made (unit `fresh`, coordinator's option (a)); the `Exist` strengthening proposed.

## 2026-11-15: the WAL's internal file predicates and callee specs -- the lock semantics (unit `locks`, session 2)

- **Spec.** Internal to the part's WAL: the tail (`walTailW`, `walTailP`, `RepairTailDefs`, `tailWB`, `WAL.sync`'s
  error post), `walLockH`, `wal.rcFile`, `walClosable`, `walFileS`, `walOpenedFile`, `pipeFile`, `walLastOpen`,
  `walLockLeft`/`walLockIn` (`WAL__renameWAL`), the leftover-file posts of `WAL__syncC`, `WAL__cleanupWAL`,
  `WAL__CloseU`, and `RepairCallees` (`Truncate.specRepTail`, `Fsync.specRepTail`).
- **Defect.** Stated over 3-field descriptions and unlocked fds: false once `fsExt` has lock state (a locked
  segment's description has a lock field; `os.File.Close` takes its tokens).
- **Evidence.** The lock semantics (`notes/wal-units/locks.md` §2); the WAL did not build after it.
- **Change.** Each file a WAL predicate holds carries `fdLocks fd d` (its tokens, `lockToks`, and `fdKindOk d`:
  each lock it holds is of `fileutil`'s kind); the tail's description is `⟨i, rd, true, lo, lk⟩`; a segment opened
  by `openWALFiles` is `walSegFd write lo lk i`. No client-facing WAL spec changed.
- **Decision.** Made (unit `locks`, session 2).

## 2026-11-15: `WAL.Close.specFailed`'s error arm for the boot path's `Repair` (P7, continued)

- **Spec.** `Sp/WAL__CloseFailed.lean` (error arm `⌜err ≠ nil⌝`), `wal.Repair.specHeld` (new, proved).
- **Defect.** With the lock model, `Repair` on the held lock is provable (`Repair.specHeld`: `false`, nothing
  changed), but it needs what the failed handle still holds: the directory claim's share at the layout's names
  and the last segment's lock token (`osLock k gL.ino fd`, `fileutil.lockKind k`). `Close.specFailed`'s error
  arm gives nothing, and the spec is itself unproved (`walReadFailedF` is a stub).
- **Proposed change.** `Close.specFailed`'s error arm gives those resources (a `walCloseLeft`); with it, the server's
  restart (C6) composes `Close.specFailed` and `Repair.specHeld` on this path.
- **Decision.** Made (unit `locks`, session 3; the coordinator's approval, internal): the post is
  `(walUnlockedTok ∗ osCallPerm ½) ∨ (⌜err ≠ nil⌝ ∗ walCloseLeft R dir)` (`CloseLeft.lean`: the shared invariant
  and a path to `dir`, the claim's half at the layout's names with `Repair.specHeld`'s facts, the last segment's
  lock and `lockKind`, the call permission's half); the composition `wal.Repair.wp_afterCloseFailed`
  (`CloseFailedRepair.lean`, proved over `Repair.specHeld`). The tester's `restartRead` drops the new resources.
  `Close.specFailed` itself is still unproved (`walReadFailedF` a stub).

## 2026-11-15: the no-error WAL specs (unit `noioerr`, second session) -- `EFBIG` at `maxBytes` needs room

- **Spec.** The new `WAL.sync.specNoErr`/`specCNoErr`, `encoder.encode.specTailNoErr`, `WAL.Close.specNoErr`,
  `WAL.SaveSnapshot.specNoErr` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/*NoErr.lean`).
- **Defect (of the first statement tried: `Close.specNoErr` from `walOpenWF`).** False: a flush whose bytes
  reach `maxBytes` (ext4's `s_maxbytes`, `fsExt`'s file size bound) fails with `EFBIG`, which `NoIoErr` keeps
  (no success exists at that offset), and `walOpenWF` bounds only `o0 + |out| ≤ sz ≤ maxBytes`, not the
  pending bytes; `SaveSnapshot` adds a frame.
- **Evidence.** `GooseLang/Ext/Fs/Premises.lean` (`NoIoErr`: a covered call succeeds when a success exists);
  `examples/osfs/semantics/data_maxbytes.go`; the ledger's 2026-11-14 entries (the stream-end fact withdrawn).
- **Change (made).** The no-error specs that write take a sealed handle with room, `walOpenWFR P Mr w dir k`
  (`HandleRoom.lean`: `o0 + |out| + |pend| + k ≤ maxBytes`; `walOpenWFR_wf`); `sync`'s internal no-error
  specs take `o0 + |out| + |pend| ≤ maxBytes`. Existing specs unchanged.
- **Decision.** Open, for the user: how a client obtains the room (`notes/wal-units/noioerr.md`, second
  session: room from `Create`'s and `Save`'s posts, a public measure of the tail, or a history-size premise).

## 2026-11-15: `WAL.Close.specFailed`'s proof (unit `closefailed`) -- `walCloseLeft`'s roots and `dir` bound, the lent tail's lock

- **Spec.** `walCloseLeft R dir` (`CloseLeft.lean`, `Close.specFailed`'s error arm), `CloseLeftOk`; the internal
  `walReadFailedF w dir` (sealed), `walTailP`/`walTailPE`/`walOpenedFile`/`walFileS`/`walLastOpen` (internal).
- **Defect.** (1) The path to `dir` the failed handle can give is the area's (`walInv_dirPath`, roots `R` of
  `walAreaOk`) only through an invariant look; the pipeline's path has its own roots and an arbitrary fraction,
  so `walCloseLeft R dir` with the spec's `R` is provable but only by that look, and nothing needs `R` fixed
  (`Repair.specHeld` is generic in it). (2) `CloseLeftOk`'s `dir.length < 2^59` is `Open`'s premise, which
  `walOpeningF`/`walReadFailedF` do not record: `ReadAll` cannot supply it. (3) The lock `walCloseLeft` hands
  over is the tail's, but no WAL file predicate recorded that a writable description holds a lock (`fdLocks`
  keeps the tokens of the locks it has, possibly none).
- **Evidence.** `WAL__CloseFailed.lean`'s error arm; `Spec/.../Repair.lean` (`specHeld` generic in `R`, takes
  the bound as a premise); `openWALFiles`/`openLast` (every writable WAL file is a `TryLockFile`/`LockFile`
  success, `lkFd_lk`).
- **Change (made).** (1) `walCloseLeft dir`: the roots existential (`Close.specFailed`'s post `walCloseLeft
  dir`). (2) The bound out of `CloseLeftOk`; `wal.Repair.wp_afterCloseFailed` takes it as a premise (its caller
  called `Open` with it). (3) `fdLocksW fd d := fdLocks fd d ∗ ⌜d.writable → d.ofd = some true ∨ d.flk = some
  true⌝` (`LockLemmas.lean`) in `walOpenedFile`, `walOpenedRc`, `walFileS`, `walLastOpen`, `walTailP`,
  `walTailPE` (`lkFd_openW`, `fdLocksW_held`); internal predicates only. Also: `walReadFailedF Mr w dir` (the
  marshaller, for the lent tail's write position), the ReadAll/Close.specFailed statements updated with it.
- **Decision.** Made (internal; the client-facing change is the error arm's `walCloseLeft dir`, which only
  `restartRead` (drops it) and `wp_afterCloseFailed` use).

## 2026-11-15: the WAL's trusted protobuf specs under `lean`'s trust gates (unit `lean-integration`, session 4)

- **Spec.** `proto.MarshalAppendCachedRecord.spec` (trust boundary); `pbSchemaOf` (`PbSchema.lean`, trusted);
  `WalEnc.recSchema`, `WalEnc.walSnapSchema`, the WAL's `walCsSchema`; `pbRecordC_reg`, `pbSnapC_reg`.
- **Defect.** None of substance: the WAL's registrations and trusted specs were written in the part `LinuxFs/`,
  outside the model-param, pbschema and axiom-tok gates. (1) `MarshalAppendCachedRecord.spec` keyed the
  registration premise by the constant `walpb.Record.ty`, which rule 1 does not read as tying the model `I` to a
  Go type (it wants `pbModelOf GF I.data.ty = some I`). (2) The WAL's schemas were not in `pbSchemaOf`'s table
  (the descriptor check could not read them), and `walCsSchema` duplicated raft's `csSchema` word for word.
  (3) No `Sat` theorem for `pbRecordM`/`pbSnapM` (rule 7).
- **Evidence.** `etc/model-param-check.py` (6 findings), `etc/pbschema-check.py`, at `033a5eafda`
  (`notes/wal-units/lean-integration.md`, session 3).
- **Change (made).** (1) `∀ I, pbModelOf GF I.data.ty = some I → I.data.ty = walpb.Record.ty → ...`: the same
  statement (its one user passes `pbRecordC_reg rfl`). (2) `pbSchemaOf` gains `walpb.Record ↦ recSchema`,
  `walpb.Snapshot ↦ walSnapSchema` (both moved into `PbSchema.lean`, same names and lists; `record.proto` at the
  pin), `walCsSchema` replaced by `csSchema`; `pbMsg` of a walpb type (none exists) now reads the real schema
  instead of `[]`. The descriptor check reads both roots (and `raftpb.ConfState` through `Snapshot.conf_state`)
  and runs `examples/stdlib/walpb`'s encoder and schema tests. (3) `pbRecordM_sat`, `pbSnapM_sat` proved.
- **Decision.** Made (no statement weakened or strengthened; the schema table's two entries are trusted text,
  for the user's review with the WAL's other trusted specs).

## 2026-11-15: the handle's half of the lock tie (unit `locks`, session 5) -- `WAL.ReadAll.spec`'s premise, the handle's locks

- **Spec.** `WAL.ReadAll.spec` (client-facing: the atomic precondition); internal: `walDirH` (new arguments: the
  non-tail lock list and the cuts), `walHandleIn`/`walHandleC` (the lock slot moved into `walDirH`), `walTailW`,
  `walLockIn` (`renameWAL.spec`), `wp_createSeg`, `walTailReg`, `walInv_readCommitReg`, `readAll_splitLeft`,
  `walInv_untailPend`/`walInv_untailKey`/`readAll_failPend`/`readAll_failSynced`/`walInv_readGive` (any range).
- **Defect.** `ReleaseLockTo`'s `unl` raise was bookkeeping (nothing tied the handle's locks to it), so the purge
  could not be proved: a purger must know that a segment it can lock ends at or before `unl`. The handle has to
  register its locked range (`walLksAuth`'s `b ≤ unl`, session 4) at the point it can show the range is within
  `unl`. For a restarted handle that point is `ReadAll`: `Open(s)` raised `unl` to `walOpenPos H s`, but nothing
  the proof holds between `Open` and `ReadAll` records it (`unl` is not in `absLe`, the history is not frozen by
  anything until the tail record is registered); only the client, which did that `Open`, knows it.
- **Evidence.** `OpenAtPin.lean` (`walInv_openAt` raises `unl` and keeps no witness); `ReadAllRegCommit.lean`
  (the registration's look sees the client's `d`); the tester's `restartRead` holds `tWalOwn γ (some
  (walOpenRaise pr dc))`, i.e. exactly `Open`'s raised state, at `ReadAll`.
- **Change (made).** (1) `WAL.ReadAll.spec`'s atomic precondition: `some s = walNewestPair … ∧ walOpenPos (d.H)
  s.1 ≤ d.unl` (the tester proves it from `walOpenRaise`, `restartRead.lean`). (2) Internal: `walDirLks` /
  `LkRel` / `walLockHI` (`Handle.lean`): the handle's non-tail locks with their segment names and inodes,
  exclusively locked, and its registered range; `walTailW` (and `walLockIn`, `wp_createSeg`'s post) carry
  `fdLocksW` (the tail's description is locked); the registration laws above. `WAL.ReleaseLockTo.spec{,NoErr}`
  unchanged: now proved with the raise meaning what its docstring said (the released locks' segments end at or
  before `walReleasePos`, `cutStart_le_releasePos`).
- **Decision.** Made (the client-facing change is a premise every caller meets by calling `Open` first; the
  server's `openWALFromSnapshot` does the same, not translated in the part).

## 2026-11-16: `purgeRound` restored in the tester (unit `locks`, session 10) -- `member.opOwnSnap.spec` takes the `lg`/`walDir` fields

- **Spec.** `etcd_wal.member.opOwnSnap.spec` (the tester's; `LinuxFs/Spec/.../examples/etcd/wal/member__opOwnSnap.lean`).
- **Defect.** With `purgeRound` restored (the user's approval, `notes/decisions.md` "WAL tester over fsExt: `purgeRound`
  restored"), `opOwnSnap` calls `purgeRound(m.lg, m.walDir, …)`, which loads the member's `lg` and `walDir` fields;
  `memLive` does not hold them (as for `member.restart`, whose spec takes them), so the old precondition does not
  allow the call.
- **Evidence.** `wal.go`'s `opOwnSnap`; `member.step.spec`, its only caller, holds both fields
  (`m.[member, "lg"] ↦ lg ∗ m.[member, "walDir"] ↦ tWalDir e.area`).
- **Change (made).** A binder `lg`; the precondition and the postcondition (both outcomes) take
  `m.[member, "lg"] ↦ lg ∗ m.[member, "walDir"] ↦ tWalDir e.area`, as `member.restart.spec`'s. `member.step`'s proof
  passes them through. New spec: `etcd_wal.purgeRound.spec` (the handle `walOpenWF`, the caller's repeatable commit
  `walPurgeAcc dir Pc` and its token `Pc`, `max < 2^63`; back the handle and `Pc`).
- **Decision.** Made (the tester's internal spec; the call needs the fields).

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

## 2026-11-15: a delivered watch event's pointers are not known to be non-nil (k8s 7f-5a-P, B)

- **Spec.** `EtcdGrove.eventAt` (`Proof/go_etcd_io/etcd/cache/v3/InvStore.lean`, exported through the client's
  `eventsAt`/`respAt`/`watchStateElemP`).
- **Defect.** It drops `ev ≠ null ∧ e.kv ≠ null`, which its producer has (`mvcc.evRd`), so the etcd3 watcher's
  `parseEvent` cannot be called on a delivered event: its `e.IsCreate()` reads the type and revisions through the
  getters, which answer defaults on a nil pointer (with `p = null` the model's `IsCreate` is `true`).
- **Proposed change.** `eventAt ev e` gains `⌜ev ≠ null ∧ e.kv ≠ null⌝`; produced by `WatchContent.evIs_facts`;
  `eventAt_elim` keeps its statement (a weakening).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, (B)).

## 2026-11-15: a codec's decoding of empty data (k8s 7f-5a-P, C)

- **Spec.** `ObjCodec` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Contract.lean`), hence `kvWfHist`'s `dec v ≠ none`.
- **Defect.** Nothing excludes an empty stored value that decodes; for one, the watcher's `prepareObjs` drops the
  previous object (`len(e.prevValue) > 0` fails) and `transform` calls `filter(nil)`, where `kEvOfL` decodes it.
- **Proposed change.** A field `dec_nil : ObjCodec.dec [] = none` (Kubernetes codecs reject empty data), discharged
  for the examples' codec.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, (C)).

## 2026-11-15: the client watch's close error has no known dynamic type (k8s 7f-5a-P, E2)

- **Spec.** `WatchResponse.Err.spec` (`Spec/go_etcd_io/etcd/client/v3/WatchResponse__Err.lean`; proved).
- **Defect.** Its post gives a non-nil error only nil-iff and `errStrOk`; the etcd3 watcher's `sendError` needs
  its type facts (`kErrOk`: `etcdError`/`grpcError`/`APIStatus` assertions, comparability).
- **Evidence.** `client/v3/watch.go:123-135`: `v3rpc.Error(closeErr)`, `ErrCompacted`, `v3rpc.Error(status.Error(
  FailedPrecondition, reason))`, `ErrFutureRev`; `rpctypes.Error`'s post keeps `clientErr`; the close error's
  sources carry it (`cliStreamErr`, `errorsNewOk`, `ctxErrClientAllW`), but for `io.EOF` (`eofIs` only) and
  `*status.Error`'s `isLeafError` (gaps). Review: `notes/k8s-7f5a-draft.md` §11.1.
- **Proposed change.** The post gains `clientErr err ∗ statusErrOk err` of a non-nil result (only conjuncts added;
  its six callers untouched; no `Results`/`Adequacy*`/`MainLinked` names it).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E2).

## 2026-11-15: GetCurrentResourceVersion's error arm is bare (k8s 7f-5a-P, E4)

- **Spec.** `store.GetCurrentResourceVersion.spec` (proved).
- **Defect.** Its error arm is `err ≠ nil` only; `startWatching` hands it to `sendError` (`watcher.go:456-460`, when
  `initialRev > 0 ∧ forceInitialEvents`), which needs `kErrOk`.
- **Evidence.** `store.go:741-742`: the client `Get`'s error, or `fmt.Errorf("the current resource version must be
  greater than 0")`; both branches in the proof.
- **Proposed change.** The arm gains `(clientErr err ∗ statusErrOk err) ∨ kFmtErr err` (the E3 form, an
  `*errors.errorString`, once E3's text is approved).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E4).

## 2026-11-15: interpretListError is specified only when not paging (k8s 7f-5a-P, E5)

- **Spec.** `interpretListError.spec` (proved; `paging` fixed to `false`).
- **Defect.** `syncPaginated` calls it with `paging = true`.
- **Evidence.** `errors.go:66-89`: paging and `ErrCompacted` go to `handleCompactedErrorForPaging` (`EncodeContinue`,
  whose error branch calls the untranslated `HandleError`, avoided when the caller shows `encOkL`).
- **Proposed change.** One triple over any `paging` (premise `paging = true → encOkL …` of the keys), post `listErr c e`.
- **Decision.** Approved (etcd-grove-81, 2026-11-15, E5).

## 2026-11-15: auth on implies no lease granted (auth-lease S3c; Draft `notes/auth-lease-s3c-draft.md` rev 6)

One entry for the frozen, exported and hub texts S3c changes (Draft §10's table); the evidence of each is the Draft's section.

- **Spec.** `srvGrantGuard` (+ `_expired`), `lease.bootCfg` (hub) and its laws, `lease.srvInvAt`'s body, `srvUberOn`,
  `srv_uberKVL(_on)` and the exported `server_uber_kvl(_on)`, the apply specs' `srvLessorNilM` premise, the auth component's
  `acLessor` (frozen, 2026-11-04) in `Start`/`start`/`applyAll.spec`, `isServerRunC`, `isServerBuilt_offC`;
  `EtcdServer.revokeExpiredLeases.spec`; `srvClusterBootOn_alloc` (+ exported restatement); etcdstart's `grpcUpOn`; the v3rpc
  lease handlers' specs and `quotaLeaseServer.LeaseGrant.spec`.
- **Defect.** Four couplings make "auth on" imply "no lease granted" (the guard `False` at auth on, `bootCfg`'s `on → m =
  none`, `srvInvAt`'s `srvLessorNil`, the apply specs' `srvLessorNilM`), though Go serves grants with auth on and the apply
  layer no longer reads `srvLessorNil` since S2 (`UberOn.lean:134`); the gRPC lease contracts are auth off only (S3b D6).
- **Proposed change.** Draft §1–§7: C1 guard `⌜lg = true ∧ (on = true → leasesNoExpiry)⌝`; `bootCfg`'s row `on = true → m =
  revocable → leasesNoExpiry`; `srvLessorNil(M)`, `acLessor` and their conjuncts deleted; `revokeExpiredLeases.spec` takes
  `E.authOn = false`; the auth-on allocation at a lease mode (C6); the `…M` contracts beside today's (C5′) and the auth-on
  `Md` registrations (C4, C7, C8).
- **Decision.** Approved (etcd-grove-81, 2026-11-15, the S3c Freeze, conditional on review round 5, which found no
  first-tier problem).

## 2026-11-15: store.Watch's revision bound (k8s 7f-5a-P step 5)

- **Spec.** The Draft's `store.Watch.spec` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Draft7f5a.lean`, not yet in `Spec/`).
- **Defect.** Its premise `uint.Z n < 2^63` admits `n = 2^63 - 1` for a watch without initial events, whose
  `startWatching` asks the client for `WithRev(n + 1)`, which wraps negative; the client's `Watch` spec needs `1 ≤ rev`
  (in Go etcd then answers a compacted or invalid watch: no panic, but the proof's start point is not a revision).
- **Evidence.** `watcher.go` `startWatching` (`clientv3.WithRev(wc.initialRev + 1)`); `kStartPre` (`WatchProd.lean`) asks
  `uint.Z r0 + 1 < 2^63` in that case.
- **Proposed change.** `uint.Z n < 2^63 - 1`; the Draft (§3) updated.
- **Decision.** Approved (etcd-grove-81, 2026-11-15).

## 2026-11-16: the store's update report gains "one change per step" (k8s 7f-6 C, F1)

- **Spec.** `KvNext` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Updates.lean`), in the posts of `k8sAu1` and `k8sAuRW`
  (what a write's firing tells its caller); `kvNext_step`, `k8sAu1_kvAu1`, `k8sAuRW_kvAu1`, `k8sAusRW_kvAu1`.
- **Defect.** `KvNext` tells the caller only the next state, so its history (`oneKeyRevs`, over state differences) cannot
  exclude a revision of two changes of one key, where the store's watch (`kStreamOk`, over etcd's events, one per change)
  delivers two events and the driver's check one: the bridge to `StreamOkL` is false without it.
- **Evidence.** `notes/k8s-7f6c-plan.md` §2 (the counterexample); the store sends single-operation transactions
  (`putTxn`, `delTxn`, `OptimisticPut`/`OptimisticDelete`).
- **Proposed change.** `KvNext`'s step disjunct gains `KvOne σ σ'` (every revision the step adds has at most one change);
  `kvNext_step` takes it of the operation's step, `kvOne_optPut`/`kvOne_optDel`/`seedOp_one` prove it of every producer.
- **Decision.** Approved (etcd-grove-02, 2026-11-16, F1 option 1).

## 2026-11-16: three more closed theorems over the file extension (decision A, landing `wal-lean`)

- **Specs.** `etcd_leaseN_adequate`/`etcd_leaseN_safe`, `etcd_leaseexpiryN_adequate`/`etcd_leaseexpiryN_safe`,
  `etcd_authN_adequate`/`etcd_authN_safe` (new on `lean` since the last merge, `523c2a5495`).
- **Defect.** As the 25 earlier ones: the bodied `fileutil`'s package initializer probes `F_OFD_GETLK` over
  `fsExt`, so `[idIssueExt]` (`TrivialExt.lean`) no longer has the extension the server's initialization needs.
- **Change.** As `putgetN`'s: the extensions are `[idIssueExt, fsExt]` (`lib/etcdstart/FsExts.lean`), one new
  premise `Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)`; every other premise and the conclusion unchanged.
- **Decision.** The user's decision (A) of 2026-11-15 for this class of change; listed for the user's review
  with the earlier 25.

## 2026-11-17: `proto.Marshal.spec` (KeyValue) -- the encoding's length unstated (S1b)

- **Spec.** `Spec/google_golang_org/protobuf/proto/Marshal.lean` (`proto.Marshal.spec`, a trust-boundary axiom).
- **Defect.** `mvcc.kvEncode` is opaque and the spec said nothing of its length, so no proof could show an
  entry mvcc writes (`revBytes`, `kvEncode kv`) within bbolt's `bboltEntryMax`, which the proved
  `Bucket.Put` takes (stage S1b of `notes/bbolt-integration-plan.md`).
- **Evidence.** `storeTxnWrite.put`/`delete`'s `UnsafeSeqPut` (`keyPutOk`'s new entry bound).
- **Change.** The post gains `⌜(mvcc.kvEncode kv).length ≤ kv.key.length + kv.value.length + 128⌝`: protobuf's
  wire format, six fields each a one-byte tag and a varint of at most 10 bytes (66 bytes of framing).
- **Decision.** Approved by the coordinator (2026-11-17, a true length fact); applied on `bbolt-putbound`.

## 2026-11-17: `schema.MustUnsafeSaveConfStateToBackend.spec` -- the JSON's length unstated (S1b)

- **Spec.** `Spec/go_etcd_io/etcd/server/v3/storage/schema/MustUnsafeSaveConfStateToBackend.lean` (axiom).
- **Defect.** Its callback took any bytes, so the hook's put of the conf state could not be shown within
  `bboltEntryMax`.
- **Evidence.** `BackendHooks.OnPreCommitUnsafe`'s put (`batchTxBuffered.UnsafePut`'s new entry bound).
- **Change.** Premise `storage.csOkN n cs` (nil, or read-only with at most `n` ids); the callback gets
  `⌜vb.length ≤ 25 * n + 128⌝` (JSON of a `ConfState`: `null`, or four `omitempty` id lists and `auto_leave`,
  at most 86 bytes of names and punctuation, each id at most 20 digits and a comma). The hooks keep the
  bound (`csInv`: `csOkN csIdMax`, `csIdMax = 2 ^ 20`, the server's voters' bound `srvMemOk`).
- **Decision.** Approved by the coordinator (2026-11-17); applied on `bbolt-putbound`.

## 2026-11-17: `etcdKeyMax` -- `2 ^ 27` let a key and a value pass a bbolt entry (S1b)

- **Spec.** `Proof/go_etcd_io/etcd/cache/v3/EtcdModel.lean` (`etcdKeyMax`, in the statements of the client
  model's laws `etcdState_keys`/`etcdState_vals` and of k8s's and the client's specs).
- **Defect.** A key and a value of `2 ^ 27` bytes each, encoded, pass `bboltEntryMax = 2 ^ 28`.
- **Evidence.** mvcc's put (`storeTxnWrite.put`'s entry bound).
- **Change.** `2 ^ 27 - 2 ^ 19`, the bound the request check gives (`etcdMaxRequestBytesOk`:
  `MaxRequestBytes + 2 ^ 19 < 2 ^ 27`). Stronger client-side facts, the same proofs; the coordinator had
  proposed sum bounds (`k + v ≤ n`) in `ChPutsLe`/`irrPutsLe`/`TxnOp.putsLe` and `MarshalIRR`'s statement,
  which this replaces: no axiom statement and no definition but this constant changes.
- **Decision.** Applied on `bbolt-putbound` (2026-11-17); for the coordinator's review.
