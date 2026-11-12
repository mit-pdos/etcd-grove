# k8s 7f-4, require-leader streams: Draft (2026-11-08, branch `k8s-7f4`; notes only, to etcd-grove-81)

This Draft covers the require-leader half of stage 7f-4 (`notes/k8s-7f-scope.md`, §2.3 2, §5.1, §9).
No Lean is written. The Scope and these decisions stand:
- **The user (2026-11-08):** delete `v3rpc.runsNoRequireLeader`, with no etcd fork change.
- **81 (Q7f-2):** a weak handler-context contract; grpc's stream-interceptor contract changed so
  that the handler gets `ci'` with `incomingOf ci' = incomingOf ci`, a reviewed fact; Watch **and**
  LeaseKeepAlive re-proved over it.

The `WithPrevKV` half of 7f-4 (7f-3 in the stage table) is not in this Draft.

Sources: etcd fork `673da07c8f` (`server/etcdserver/api/v3rpc/{interceptor,watch,lease,util}.go`,
`server/etcdserver/v3_server.go`), client `client/v3/ctx.go`, and this repository at lean `3a08c2abee`.

## 1. What changes, in one paragraph

etcd's stream interceptor (`newStreamInterceptor`) has two branches:
- **Without require-leader** (a client that did not call `WithRequireLeader`), it passes the
  stream on unchanged.
- **With require-leader**, which the k8s store's watches always take (`store.watchContext`):
  - if the member has no leader, it refuses the stream with `ErrGRPCNoLeader`;
  - otherwise it wraps the stream's context in a `*cancellableContext` (`WithCancel` of it, plus
    a reason under a `RWMutex`), registers the wrapped stream in `monitorLeader`'s map, and calls
    the handler with it;
  - the monitor cancels every registered stream with `ErrGRPCNoLeader` after 3 election timeouts
    without a leader.

The wrapped context is not an `isContext`:
- its `Err` returns `ErrGRPCNoLeader`, a gRPC status error, where `isContext` allows only
  `Canceled`/`DeadlineExceeded`;
- it can return that error while `Done` is still open
  (`issues/etcd-stream-interceptor-err-before-done.md`).

So:
- the handlers' context premise is weakened (§2);
- grpc's interceptor contract lets the handler's context differ from the run's, with the same
  incoming metadata (§3);
- the new facts are the metadata equality and `WithRequireLeader` over a caller's context (§4);
- every place Watch and LeaseKeepAlive use their context is re-checked (§5);
- the interceptor branch and the monitor get proofs (§6).

Then `runsNoRequireLeader` goes, from 26 files and from the premises of 18 closed theorems (§7).

## 2. The weak handler-context contract

```lean
/-- **A stream handler's context** (persistent): `Done()` as `isContext`'s; `Err()` at any time
returns nil or some error; once `Done` is closed (the caller holds `ContextClosed`), a non-nil
error that is a context error or etcd's no-leader error. -/
def srvCtxWeak (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDone" ∷ □ (∀ Φ, True -∗ ▷ (∀ ch γch, isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷ □ (∀ Φ, ▷ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErrDone" ∷ □ (∀ Φ, ContextClosed s.Done_gn -∗
      ▷ (∀ err : GoInterface, ⌜err ≠ interface.nil⌝ -∗ (isCtxErr err ∨ noLeaderErr err) -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}))

/-- etcd's no-leader error: the value of `rpctypes.ErrGRPCNoLeader` (a status error `srvErrOk`
accepts; `v3rpc/Base.lean:312` already names it). -/
def noLeaderErr (err : GoInterface) : IProp GF :=
  iprop(∃ e, globalAddr rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝)
```

**Laws** (proved; no trust):
- `isContext c s ⊢ srvCtxWeak c s`. `isContext`'s `#HErr`/`#HErrDone` give the two `Err`
  triples (it is stronger before `Done` too). So every path that still passes `isContext`, the
  branch without require-leader and grpc-prometheus's wrapper, meets the contract unchanged.
- `cancellableContext` (§6) gives `srvCtxWeak` for its child's descriptor. Its lock invariant is
  that `cancelReason` is nil or `ErrGRPCNoLeader`.
  - Before `Done` closes, `Err` returns the reason or the child's `Err`: nil or some error.
  - After `Done` closes, `Err` returns `ErrGRPCNoLeader` if the reason was set by the monitor's
    `Cancel(ErrGRPCNoLeader)`, else the child's `Err`, which is `Canceled` (`isCtxErr`). The
    deferred `Cancel(nil)` resets the reason to nil, so the child's `Err` is what is returned
    then.

**What it does not say:**
- Nothing about `Value`. The metadata the handler reads comes from §3's equality.
- Nothing about a non-nil `Err` before `Done` (`isContext`'s `□ PDone ∗ ContextClosed`): that is
  exactly the Err-before-Done window.

## 3. grpc's stream-interceptor contract

**Today** (`Proof/google_golang_org/grpc/InvGrpcStream.lean`):
- `srvStreamInterceptorOk` (`:729`) says the interceptor calls `h` "on the same service value
  and a server end `st'` of the same stream with the same context (… context `ci` …)".
- `srvRawStreamIs` and `srvStreamIs` (`:324`, `:365`) end in `context.isContext ci cd ∗
  grpcRunCtx ci`.
- `grpcStreamHandlerOk` (`:674`) gives the handler `Spec (metadata.incomingOf ci) γ Dn` with
  `srvStreamIs st γ … ci cd`.

**Proposed:**
- **`srvStreamInterceptorOk`**: the interceptor either returns a non-nil error without calling
  `h`, or calls `h` once on the same service value and a server end `st'` of the same stream
  (the same queues, tokens and contents) whose context is some `ci'` with:
  - `srvCtxWeak ci' cd'` for some descriptor `cd'`;
  - `⌜metadata.incomingOf (GoInterface.ok ci') = metadata.incomingOf (GoInterface.ok ci)⌝`.

  The continuation for `h` takes `srvRawStreamIs st' γ Req Rep Up Dn ci' cd'` and that equality.
  The rest is unchanged: `R` comes back either way, and the handler returns an error value.
- **`srvRawStreamIs`/`srvStreamIs`**: the last conjunct becomes `srvCtxWeak ci cd` in place of
  `context.isContext ci cd ∗ grpcRunCtx ci`. `grpcRunCtx` stays on the unary path
  (`grpcMethodOkMd`, the unary handlers' `isContext ∗ grpcRunCtx`), which this Draft does not
  touch.
  - Evidence that the stream handlers do not use `grpcRunCtx`: `Hrunctx` is destructured in
    `watchServer__Watch.lean:172`, `serverWatchStream__recvLoop.lean:205`, `__sendLoop.lean:1749`
    and `LeaseServer__leaseKeepAlive.lean:168`, and never used (grep).
  - To confirm when the Lean is written: no derived stream path reaches a callee needing
    `grpcRunCtx` (§5's table lists every callee).
- **`grpcStreamHandlerOk`**: unchanged in shape. The handler gets
  `Spec (metadata.incomingOf ci') γ Dn`. The chain's proof (`srvStreamChainWP`) carries
  `incomingOf ci' = incomingOf ci` through each interceptor, so the registration's
  `Spec (incomingOf ci)` is the handler's.
- **Who meets it:**
  - grpc's own model of a run starts at `isContext ci cd`, which gives `srvCtxWeak ci cd` (§2's
    law);
  - grpc-prometheus's interceptor passes `ss.Context()`, so it is the same `ci` and the equality
    is `rfl`;
  - etcd's `newStreamInterceptor` takes the same `ci` in its non-require-leader branch, and the
    wrapper in the require-leader branch (§6).

This is a change to the trusted grpc model text (InvGrpcStream is trusted vocabulary), so the 7f-4
Lean stage puts it through the `axiom` skill with §4's facts.

## 4. New trusted facts, and the trust-boundary specs that change

**F1, the metadata fact** (new; reviewed with the `axiom` skill). Two forms, Q7f4-1:
- **(F1-narrow)** For the wrapper the require-leader branch builds from the run context `ci`, a
  `*cancellableContext` whose embedded context is `WithCancel(ci)`:
  `metadata.incomingOf (wrapper) = metadata.incomingOf ci`.
  - It is an axiom about grpc's opaque `incomingOf` (`grpc/metadata/Incoming.lean:27`) at one
    shape of context.
  - Why it is true in Go: `metadata.FromIncomingContext(x)` reads `x.Value(mdIncomingKey{})`. The
    wrapper's `Value` is promoted from its embedded `Context`, the `WithCancel` child, whose
    `Value` at a key other than `&cancelCtxKey` is the parent's (`context.go`'s `value`).
- **(F1-general)** `incomingOf` is determined by `Value` at grpc's incoming key: two contexts whose
  `Value(mdIncomingKey{})` return the same value have the same `incomingOf`.
  - With the ctx-value laws (§8), the wrapper's equality becomes a lemma.
  - It needs the grpc model to state the run context's `Value` at that key in the `ctxValue` form
    (§8, gap (a)), a second change to trusted text.
  - It is more general, and serves any future context derivation on a handler's path.

**F2, `clientv3.WithRequireLeader` over a caller's context** (new trust-boundary triple;
names-only, grpc `metadata`). It generalizes the `Background()`-only spec
(`Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`):

```lean
abbrev WithRequireLeader.spec' : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : ContextDesc (IProp GF)),
  {{ isPkgInit pkg_id.go_etcd_io.etcd.client.v3 ∗ EtcdGrove.context.watchCtx ctx cd }}
    (App (Val (@! clientv3.WithRequireLeader)) (Val #(GoInterface.ok ctx)))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c);
      EtcdGrove.context.watchCtx c cd ∗
      ⌜metadata.outgoingOf (GoInterface.ok c) =
        metadata.mdSet (metadata.outgoingOf (GoInterface.ok ctx)) "hasleader" ["true"]⌝ ∗
      (context.isContext ctx cd -∗ context.isContext c cd) }}
```

- Go: `md, ok := FromOutgoingContext(ctx)`. With none, `Pairs(hasleader, true)`; else a copy with
  the key set. Then `NewOutgoingContext(ctx, md)`, a `WithValue` whose `Done`/`Err`/`Deadline`
  are `ctx`'s.
- `mdSet`/`outgoingOf` are the repository's vocabulary (`grpc/metadata/Outgoing.lean`).
- The `Background()` spec becomes a corollary.
- **Producer:** 7f-3/7f-5a (the store's `watchContext`). It is needed by the client side only:
  the server never sees the triple, only the metadata grpc delivers.

**Trust-boundary specs that change** (each a weaker premise, through the `axiom` skill):
- `traceutil.Tracer.Start.spec` (`Spec/.../traceutil/Tracer__Start.lean:38`).
  - Today it takes `mvcc.txnCtx ctx cd` (`doneNil ∨ isContext`) and gives `txnCtx ctx'`, with
    `isContext ctx -∗ isContext ctx'` and the same `incomingOf`.
  - Add: `srvCtxWeak ctx cd -∗ srvCtxWeak ctx' cd'`. otel's `ContextWithSpan` is a `WithValue`,
    so `Done`/`Err` are `ctx`'s.
  - The premise must also admit `srvCtxWeak` (Q7f4-3: through a widened `txnCtx`, or a disjunct
    here).
- `EtcdServer.waitLeader.spec` (an axiom, `Spec/.../EtcdServer__waitLeader.lean:39`). It takes
  `isContext ctx cd`; with `srvCtxWeak ctx cd` instead, it only selects on `ctx.Done()`. Reached
  from LeaseRenew's `cctx`.
- `leasehttp.RenewHTTP.spec` (an axiom, `Spec/.../leasehttp/RenewHTTP.lean:47`). It takes
  `isContext ctx cd`; with `srvCtxWeak ctx cd` instead, `req.WithContext(ctx)` and net/http use
  `Done`/`Err`. Its post is unchanged (`applyErrIs err` or nil).
- **P-RL2**, contexts derived from a weak parent (`WithValue` in `Tracer.Start`; `WithTimeout` in
  `LeaseRenew`). A child of a `srvCtxWeak` parent is `srvCtxWeak`. Go's child takes
  `parent.Err()` when the parent is cancelled, so `ErrGRPCNoLeader` propagates.
  - For `Tracer.Start` it is part of the triple above.
  - For `WithTimeout` it is a local lemma until a Perennial change (Q7f4-4).
  - `notes/perennial-changes.md`'s entry "Contexts derived from a parent that is not an
    `isContext`" holds it.

Nothing else in the trust base changes. `runsNoRequireLeader`, a premise about the deployment, is
removed (§7).

## 5. Every use of the handler's context in Watch and LeaseKeepAlive

`c` below is `stream.Context()`, `ci'` with `srvCtxWeak ci' cd'`.

| Site (fork `673da07c8f`) | What it does with `c` | Under `srvCtxWeak` | Change |
| --- | --- | --- | --- |
| **W1** `watch.go:203` (`Watch`, the recvLoop goroutine's error path) | `isClientCtxErr(c.Err(), rerr)`, `Done` maybe open | `Err` any (nil or some error): `isClientCtxErr` decides only the log level and the `streamFailures` metric (`util.go:110`) | none beyond `#HErr` |
| **W2** `watch.go:228-233` (`Watch`'s `select`) | `<-c.Done()`, then `err = c.Err()`, `errors.Is(err, context.Canceled)` → `ErrGRPCWatchCanceled`; `err` returned to grpc | `#HDone`; then `#HErrDone`: `isCtxErr` (as today) or `noLeaderErr`. `errors.Is(ErrGRPCNoLeader, Canceled)` returns some bool by the existing status-error `errors.Is` axiom (`Spec/errors/IsStatusErr.lean`: an error grpc accepts against a comparable error); either branch is fine, since the handler's return value is unconstrained (`grpcStreamHandlerOk`'s `∀ err, Φ #err`) | none (an existing axiom's case: `ErrGRPCNoLeader` is an error grpc accepts) |
| **W3** `watch.go:240` (`isWatchPermitted`) | `AuthInfoFromCtx(c)` → `isReqAuth`'s triples take `mvcc.txnCtx c cd` | `txnCtx` is `doneNil ∨ isContext`: neither | Q7f4-3: widen `txnCtx` or give `isReqAuth` a weaker premise; the auth path reads `c`'s metadata (`incomingOf`, preserved by §3) and the TLS peer |
| **W4** `watch.go:333` (`recvLoop`, create) | `Tracer.Start(c, …)` → `ctx'` | §4's changed `Tracer.Start`: `srvCtxWeak ctx'`, same `incomingOf` | the trust-boundary spec |
| **W5** `watch.go:342` (`recvLoop`) | `sws.watchStream.Watch(ctx', …)`; `mvcc.watchStream.Watch.spec` takes `isContext ctx cd` (`Spec/.../mvcc/watchStream__Watch.lean:44`) | mvcc's `Watch` reads only `trace.SpanFromContext(ctx)` (`mvcc/watcher.go:140`) | `watchStream.Watch.spec`'s premise to what its proof uses (`SpanFromContext`'s; proved, not trusted) |
| **W6** `watch.go:492, 550, 574` (`sendLoop` error paths) | `isClientCtxErr(c.Err(), err)` | as W1 | none |
| **W7** `newStreamInterceptor` (§6) | builds `c` | §2's law for `cancellableContext` | new proof |
| **L1** `lease.go:98-106` (`LeaseKeepAlive`'s `select`) | `<-c.Done()`, `err = c.Err()` returned (the comment names case 2: `ErrGRPCNoLeader`) | `#HDone`, `#HErrDone`; return value unconstrained | none beyond the contract |
| **L2** `lease.go:118, 149` (`leaseKeepAlive` error paths) | `isClientCtxErr(c.Err(), err)` | as W1 | none |
| **L3** `lease.go:136` | `ls.le.LeaseRenew(c, id)`; `EtcdServer.LeaseRenew.spec` takes `isContext ctx cd` (`Spec/.../EtcdServer__LeaseRenew.lean:55`) | below, L4-L7 | `LeaseRenew.spec`'s premise to `srvCtxWeak` (an internal, linked spec) |
| **L4** `v3_server.go:490` (`LeaseRenew`) | `Tracer.Start(c, …)` | as W4 | (W4's) |
| **L5** `v3_server.go:524, 546` (`checkLeaseRenew(ctx, id)`) | `AuthInfoFromCtx(ctx)` (`checkLeaseRenew.spec` takes `txnCtx`) | as W3 | (Q7f4-3) |
| **L6** `v3_server.go:537` | `cctx, cancel := context.WithTimeout(ctx, …)` | P-RL2: `srvCtxWeak cctx` | local lemma (Q7f4-4) |
| **L7** `v3_server.go:541-571` | `for cctx.Err() == nil`; `waitLeader(cctx)`; `RenewHTTP(cctx, …)`; then `switch errors.Is(cctx.Err(), DeadlineExceeded/Canceled)`, `default` logs "Unexpected lease renew context error" and returns `ErrCanceled` | `Err` any before `Done` (the loop only tests it: a non-nil `ErrGRPCNoLeader` ends it, as Go does); `waitLeader`/`RenewHTTP` with §4's weaker premises; the `switch` reaches `default` for `ErrGRPCNoLeader` (an `errors.Is` false case, as W2) | the two axioms' premises; LeaseRenew's proof follows the third branch |

Every read is one of: `Done`; `Err` after `Done`; `Err` for logging; metadata; or a derived context.

The table names the trust-boundary specs whose premises change (§4). Every other change is a
proof's.

## 6. The interceptor branch and the monitor (proofs, no trust beyond §4)

- **`newStreamInterceptor`'s require-leader branch** (`interceptor.go:239-258`):
  - `s.Leader() == raft.None` → `ErrGRPCNoLeader`, no handler call;
  - `newCancellableContext(ss.Context())`: `context.WithCancel(ci)`, a `*cancellableContext` with
    its `RWMutex` invariant (`cancelReason ∈ {nil, ErrGRPCNoLeader}`);
  - `serverStreamWithCtx{ctx, ss}`: its `Context()` returns the wrapper; its `RecvMsg`/`SendMsg`
    are the embedded `ss`'s, so `srvRawStreamIs` carries over with `ci'`;
  - `smap.streams[ss] = struct{}{}` under `smap.mu`;
  - `defer`: delete the entry, then `ctx.Cancel(nil)`;
  - then `handler(srv, ss)`.

  The continuation gets `srvCtxWeak ci' cd'` (§2) and F1's equality.
- **`streamsMapInv`** (`v3rpc/InvStreamInterceptor.lean:61`).
  - Today the map is empty.
  - Proposed: each key is a `serverStreamWithCtx` whose `ctx` is a `*cancellableContext`, with a
    share of its `cancelSpec` (`WithCancel`'s), so that the monitor can call `Cancel`.
- **`monitorLeader`** (`interceptor.go:315-354`).
  - On `noLeaderCnt >= 3`, for each key: the `serverStreamWithCtx` type assertion,
    `ssWithCtx.ctx.Cancel(rpctypes.ErrGRPCNoLeader)`, then `<-ss.Context().Done()` (closed by
    `Cancel`'s `c.cancel()`).
  - Then the map is replaced by a fresh empty one.
- **`cancellableContext.Cancel`/`Err`** (`interceptor.go:288-304`): the lock invariant above;
  `Err` under `RLock`.
- **R1, map keys that are interfaces holding structs: checked 2026-11-08** (scratch Lean, kept as
  `notes/k8s-7f4-mapkey-check.lean.txt`; built against lean `3a08c2abee`'s full build):
  - **The semantics supports it.**
    - `go_eq_interface` (Perennial `Golang/Defn/Interface.lean:51`) compares the dynamic types,
      then `CheckComparable` and `==` at the dynamic type.
    - For `serverStreamWithCtx.ty` (a named struct) that is `struct_is_comparable` and
      `go_eq_struct` (`Defn/PostLang.lean:337-349`), field by field: the embedded `ServerStream`
      (an interface again) and the `ctx` pointer.
    - `wp_pures` reduces `==` on two keys `sKey t l c = mkOk serverStreamWithCtx.ty
      #⟨mkOk (ptr t) #l, c⟩` all the way down to the pointer comparisons. The scratch lemma
      `sKey_eq` proves `WP (k == k') {{ Φ }}` from `Φ #(decide (k = k'))`, with the grpc and v3rpc
      `Assumptions` (for `ServerStream.ty`'s underlying interface), up to one pure gap: the
      injectivity of `#` on `serverStreamWithCtx` values. That is a 20-line lemma, as 7e's
      `Obj_intoVal_inj` (`examples/k8s/etcd3/MDefs.lean`).
  - **Perennial's map specs need a local instance.**
    - `wp_mapInsert`/`wp_mapDelete`/`wp_map_lookup2` take `SafeMapKey key_type k`.
    - The default `MapKeys GoInterface` (`Golang/Theory/Map.lean:49`) admits only nil and
      pointer-holding interfaces, but its comment invites "a proof that needs other interface keys
      can give its own instance".
    - So 7f-4 states a local `MapKeys GoInterface` instance for the monitor's map: nil, pointers,
      and `sKey t l c`. It also states the `SafeMapKey` instance from `sKey_eq` (with the
      injectivity lemma), and must not mix this map's `ownMap` with the default instance's
      elsewhere.
    - Proposing the struct case to Perennial later, as a general `SafeMapKey` for a struct whose
      fields are safe keys, is optional and independent.
  - **A new requirement on the grpc model (F3).** The key's `ServerStream` field holds the raw
    stream `st` grpc gave the interceptor, and `srvRawStreamIs` leaves its dynamic type abstract
    (`∃ si, st = GoInterface.ok si`). `sKey` needs a pointer there, and Go too needs a comparable
    one, else `smap.streams[ss] = …` panics with "hash of unhashable type".
    - grpc-go passes a `*serverStream`; grpc-prometheus's wrapper, when present, is a struct of an
      interface and a pointer, comparable too.
    - So `srvRawStreamIs` gains `si.ty` is a pointer type, or, general enough for the prometheus
      wrapper, a key `SafeMapKey` accepts.
    - That is a third change to the trusted grpc model text, with F1 and §3, through the `axiom`
      skill.
- **R2:** `monitorLeader`'s `<-ss.Context().Done()` waits, under `smap.mu`, on the wrapper's
  `Done`, which its own `Cancel` closes. It terminates; partial correctness needs nothing more.

## 7. Statements that change when `runsNoRequireLeader` is deleted

**Frozen and API statements** (the text changes; each has an interface diff to review):
- `v3rpc.newStreamInterceptor.spec` (`Spec/.../v3rpc/newStreamInterceptor.lean`): the premise is
  removed, and the post's `srvStreamInterceptorOk` is §3's.
- `v3rpc.runsNoRequireLeader` itself (`InvStreamInterceptor.lean:76`) and its explanation: deleted.
- grpc's `srvStreamInterceptorOk`, `srvRawStreamIs`, `srvStreamIs` (`InvGrpcStream.lean`): §3.
  This is trusted model text.
- The handlers' specs:
  - `watchServer.Watch.spec`;
  - `LeaseServer.LeaseKeepAlive.spec`, `LeaseServer.leaseKeepAlive.spec`;
  - the `serverWatchStream` ones.

  Their text is unchanged, but `srvStreamIs` means §3's (the context weakened). The linked results
  in `v3rpc/Results.lean` (`:1583`, `:1893-1912`) re-prove.
- Internal specs with a weaker premise: `EtcdServer.LeaseRenew.spec`, `checkLeaseRenew.spec`,
  `mvcc.watchStream.Watch.spec`, and `isReqAuth`'s triples (Q7f4-3).
- **etcdstart's API:** `Spec/.../etcdstart/Serve.lean:61` takes `v3rpc.runsNoRequireLeader`, and
  `etcdstart.commonPremises` (`Proof/.../etcdstart/Defs.lean:199-201`) holds it. The interface
  files that change:
  - `interface/Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/Serve.txt`;
  - `interface/Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/{Serve,OneMember,Defs}.txt`.
- `Spec/.../examples/etcd/restart/serveClient.lean:43`, `Proof/.../client/v3/ServeFromStart.lean`
  (`:62`, `:137`, `:211`), `v3rpc/InvGrpcStart.lean:345`, `examples/etcd/putget3/Defs.lean:153`,
  `examples/etcd/auth/Defs.lean:83`: the premise is removed.

**Closed theorems** (18; the premise leaves their hypotheses: a strengthening, the text of the
premise bundles changes):
- `etcd_putget_safe`, `etcd_putget3_safe`, `etcd_txnlin_safe`, `etcd_watch_safe`,
  `etcd_cache_safe`;
- `etcd_partition_safe`, `etcd_partition_watch_safe`;
- `etcd_lease_safe`, `etcd_leasecatchup_safe`, `etcd_leaseexpiry_safe`, `etcd_leasegrant_safe`;
- `etcd_compacted_safe`, `etcd_compactwatch_safe`;
- `k8s_compactor_safe`, `k8s_compactor_partition_safe`;
- `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe`.

Each reaches it through `etcdstart.commonPremises`, `putget3.premises` or `ServeFromStart`. The
raft examples, the witness part and `goose_prophkv_safe` do not start a server and are untouched.
The 7f-4 Draft's Lean stage regenerates the list with `etc/importers.py --uses commonPremises
--files` and checks it against `etc/tcb-report.py`'s roots.

**Trust base:**
- added: F1 (one fact), F2 (one triple), F3 (the raw stream's dynamic type is comparable, §6 R1);
- removed: the deployment premise;
- changed (weaker premises): `Tracer.Start`, `waitLeader`, `RenewHTTP`, and the grpc model text
  of §3;
- `etc/tcb-baseline.txt` and the collections are updated with `--check --update` when it lands.

## 8. Does the ctx-value proposal cover P-RL1?

`/shared/perennial-ctx-value/docs/design/context-value.md` (branch `ctx-value`, `c3beeb89d`).

**Yes, as a law about Go's `context` package, and correctly stated.**
- L2 gives `ctxValue (WithCancel parent) k R` from `ctxValue parent k R` for `k ≠ &cancelCtxKey`,
  with no premise on the parent's type. It goes through the parent's own `ctxValue`, which
  carries `value()`'s loop form, so the `*valueCtx`/`*timerCtx` objection to P-RL1's first
  wording does not apply.
- L5 covers a context of an application type, such as etcd's `*cancellableContext`: its `Value`
  is promoted from the embedded `WithCancel` child, so `□ {{True}} x.Value(k) {{R}}` follows from
  the child's `ctxValue_Value`.

**What it does not give 7f-4 by itself:**
- (a) **The grpc run context's side.** L2 needs `ctxValue ci k R` for grpc's `ci`. The grpc
  model gives only `isContext ci cd ∗ grpcRunCtx ci`: a `WP ci.Value(k)` form at etcd-prefixed
  keys, nothing at grpc's incoming-metadata key, and no loop form. In Go, `ci` is a `*valueCtx`
  chain, so L5 does not apply to it. So using L2 needs the grpc model to state `ci`'s `Value` in
  the `ctxValue` form, a change to trusted grpc text.
- (b) **`incomingOf` is opaque.** Even with `ctxValue` at grpc's key, the handler's
  metadata-indexed `Spec` reads `metadata.incomingOf`, which is not defined through `Value`. So
  some fact connecting them remains: F1-narrow, or F1-general (§4).
- (c) **P-RL2** (§4) is out of its scope, as the proposal says (§3.4).

**Recommendation (Q7f4-1):**
- **F1-narrow now:** one reviewed fact, no dependency on ctx-value or on changing the grpc model's
  run context.
- **Revisit when ctx-value lands:** with (a) done, F1-general replaces F1-narrow, and P-RL1 is used
  as intended.
- Either way, `notes/perennial-changes.md`'s P-RL1 entry is marked "covered by the ctx-value
  proposal". This Draft adds that line.

The proposal's §5 translator bug (a multi-type `case` tests its first type twice) does not touch
7f-4's code: `interceptor.go`'s type switches are single-type (`ss.(serverStreamWithCtx)`;
`isCancelError` uses assertions, not a switch).

## 9. Estimate (the require-leader half of 7f-4)

| Part | Lean lines |
| --- | --- |
| `srvCtxWeak`, `noLeaderErr`, the `isContext → srvCtxWeak` law | 150-250 |
| grpc's contract change (§3), the chain's metadata equality, grpc-prometheus and the non-require-leader branch re-proved | 300-500 |
| the require-leader branch, `cancellableContext`, `serverStreamWithCtx`, `streamsMapInv`, `monitorLeader` (R1 first) | 900-1400 |
| Watch's chain re-proved (W1-W6; `watchServer__Watch`, `recvLoop`, `sendLoop`, `isWatchPermitted`) | 600-1100 |
| LeaseKeepAlive's chain and `LeaseRenew` (L1-L7), P-RL2 for `WithTimeout` (local lemma) | 500-900 |
| the auth path (Q7f4-3) | 200-600 |
| deleting the premise from 26 files; interface files; tcb baseline | 200-400 |
| **total** | **2850-5150** (the Scope's 3000-5300 for all of 7f-4 included 7f-3's metadata side) |

**Dependencies, unchanged from the Scope:**
- the per-type landing (InvGrpc/InvGrpcStream are rewritten there: §3's change goes on top);
- the grpc serve pool's stage B.

**Checkpoint:** this Draft. Then a hard stop before the first trusted-text change (§3/§4) is
written in Lean.

## 10. Questions for 81

- **Q7f4-1. F1's form.** Recommended: F1-narrow now, F1-general once ctx-value lands and the grpc
  run context is stated in `ctxValue` form (§8).
- **Q7f4-2. `srvStreamIs` drops `grpcRunCtx`** for the weak context (the stream handlers never use
  it, §3). Recommended: yes.
- **Q7f4-3. The auth path (W3, L5).** `isReqAuth`'s triples take `mvcc.txnCtx` (`doneNil ∨
  isContext`; 70 files mention `txnCtx`).
  - (T1) Add `srvCtxWeak` as a third disjunct of `txnCtx`, and check each consumer's use of the
    `isContext` disjunct.
  - (T2) Give `isReqAuth`'s triples and `Tracer.Start` a premise of only what the auth path reads
    (metadata, the TLS peer), and derive it from both `txnCtx` and `srvCtxWeak`.

  Recommended: (T2), with T1 as the fallback if (T2)'s premise turns out to be most of
  `isContext` anyway. Decided at the start of the Lean stage, after enumerating `isReqAuth`'s uses.
- **Q7f4-4. P-RL2.** Recommended: local lemmas for `WithTimeout` and the `Tracer.Start` triple now;
  a Perennial proposal (`isContext` generalized over its errors' predicate) after 7f-4, as an
  independent change.
- **Q7f4-5. The three trust-boundary premises** (`Tracer.Start`, `waitLeader`, `RenewHTTP`)
  weakened to `srvCtxWeak` (§4). Recommended: yes, each through the `axiom` skill. They only get
  weaker premises.

## 11. Decisions on this Draft, and the handoff (2026-11-08)

**81 accepted the Draft as the plan:**
- Q7f4-1: F1-narrow now, F1-general after ctx-value.
- Q7f4-2: yes.
- Q7f4-3: decided at the start of the Lean stage, preferring the narrow premise (T2).
- Q7f4-4: local lemmas now.
- Q7f4-5: yes, each premise through the `axiom` skill before use.
- R1 checked (§6): feasible, with a local `SafeMapKey` instance and F3.

**Re-baseline (2026-11-12):** `notes/k8s-7f4-rebaseline.md` checks this Draft against lean `6803e4e0fd` (after per-type, stage B, premise fixes 7 and 8); its §2 changes Q7f4-1, Q7f4-2 and §3 (pending 81), and its §4 order replaces the order below.

**Handoff to the agent that takes the 7f-4 Lean** (after the per-type landing and stage B of the
grpc serve pool):
- **Start state:**
  - lean has 7f-1 (`3a08c2abee`).
  - 7f-2 is on branch `k8s-7f2` (worktree `/shared/etcd-grove-k8s7f2`, off `k8s-7e`; lands after
    `k8s-7e`, its STATUS entry at landing).
  - This Draft is on `k8s-7f4` (worktree `/shared/etcd-grove-k8s7f`, notes only; land it as notes,
    or carry it).
- **Order:**
  1. Q7f4-3 (enumerate `isReqAuth`'s uses of `txnCtx`, then T2 or T1).
  2. The trusted texts as one package through the `axiom` skill: §3's contract, F1-narrow, F2, F3,
     and the three weakened premises. **Hard stop for review.**
  3. `srvCtxWeak` and its laws.
  4. The interceptor branch and the monitor (the `sKey` instance first, from
     `notes/k8s-7f4-mapkey-check.lean.txt`).
  5. Watch's chain, LeaseKeepAlive's chain with `LeaseRenew` and the local P-RL2 lemma.
  6. The premise's deletion: `etc/importers.py --uses commonPremises --files`, the interface
     files, `etc/tcb-report.py --check --update`.
- **Builds:** seed `.lake/build` from a fresh full build (CLAUDE.md, the memory notes), and run
  every lake command with `--packages=/shared/tmp/manifest-84d.json`. The 7f-1 landing's full
  build was killed once at the 64G cap and passed on the retry.
- **Not this half:** 7f-3, `WithPrevKV` through the watch stack: the client's `watcher.Watch.spec`,
  the server's `prevKV` map and the `sendLoop` branch, the `watchGRPCStream.run` re-proof
  (`notes/k8s-7f-scope.md`, §5.1).
