# Triage of `Watch_dist`'s and `RequestProgress_dist`'s axiom-tok entries (independent, 2026-11-26)

The entries under triage are in `etc/axiom-tok-allow.txt`: the `entry` and `trunc` lines for
`Perennial.EtcdGrove.etcd_dist.Watch_dist.wp_proof` and `etcd_dist.RequestProgress_dist.wp_proof`, and the "Rule 2b,
`Watch_dist`/`RequestProgress_dist` with `8/0`" paragraph of the section header above them. Both entries have the key
`2:L:0:handedtoacallback8/supplieddirectly0,7:P:IPropGF`. Their trace is `notes/axiom-review/full-line-axiom-tok.md`
§(c). This triage was done at `8b31f9f926` (origin/etcd-safe-full-atok/2026-11-26). Nothing is committed.

**Verdict: justified with corrections.** Neither axiom lets its user obtain a `levelTok`/`threadTok` the user did not
have, and neither hands the user a resource that rules 2, 3 or 5–7 are meant to catch. The keys are right and the
`trunc` lines are right. Three statements in the entries' text are inaccurate, though, and are corrected below:

- The 8 counted contracts are never called at all. The entry implies that the forked `run` calls them with its fork
  token.
- `RequestProgress_dist`'s reason ("it only sends on the stream's `reqc`") leaves out that it also creates the
  stream, with the same `go wgs.run()`.
- The fork-token argument is the proved in-process code's. Nothing proves it for the dist call.

## What was run

All runs were on the VM, at the gate's default depth 14, after a `vmlake build` of the three modules (exit 0). The
modules were `Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist`, `…dist.KVPutDist` and
`Proof.go_etcd_io.etcd.client.v3.Link`. Raw output is in `/home/ubuntu/.claude-E/jobs/b20ef685/tmp/tri-w-scratch/`
(`plain.jsonl`, `instr.err`), which is not kept in the repository.

- **plain.** The gate's `etc/AxiomTokCheck.lean` walked seven statements: the two dist axioms, `KV_Put_dist.wp_proof`,
  and the proved `client.v3.watcher.wp_Watch`, `wp_RequestProgress`, `wp_newWatcherGRPCStream` and
  `client.v3.watchGRPCStream.wp_run`.
- **instr.** An untracked copy of the checker, deleted from the worktree afterwards. It pushes an unfold stack in
  `walkI` and `walkProp`, and prints each token occurrence, each opaque occurrence and each truncation note with its
  polarity, `cbDepth`, flips and stack.

| walk | scen. | findings | tokens at `cb=0` |
|---|---|---|---|
| `Watch_dist` | 8 | `level L:0: handed to a callback 8, supplied directly 0`; 4× `∃ P : IProp GF` (in `isCancelCtxOf`) | none |
| `RequestProgress_dist` | 8 | the same | none |
| `KV_Put_dist` | 8 | `… handed to a callback 8, supplied directly 1`; the same 4× `∃ P` | the pre's `levelTok 0` and the post's |
| `watcher.wp_Watch` | 3 | none | none (no token anywhere) |
| `watcher.wp_RequestProgress` | 2 | none | none |
| `watcher.wp_newWatcherGRPCStream` | 4 | only rule 5/7 artefacts of this run's local taint (no allow file) | none |
| `watchGRPCStream.wp_run` | 2 | none | `threadTok` consumed in the pre and produced in the post |

The trace's claims all reproduce:

- **No cb=0 token.** Every scenario of the two dist walks has `tok:L:0 8` produced, all of it `cb:`, and `tok:L:0 8`
  consumed, all of it `ret:`. No token is at `cb=0`. The only difference from `KV_Put_dist` is the `+1` of its pre's
  and post's own `levelTok 0`.
- **The 8 pairs.** There are 16 token occurrences in each dist walk. They form 8 pairs, each `pol=pos cb=3 flips=2`
  (the contract's pre) and `pol=neg cb=3 flips=3` (its post). The stacks are `[etcdInterceptorOk |
  etcdInterceptorOkM>etcdInterceptorOkW, isEtcdConn, X, isNewClient, watchClientAt, spec]`, with `X` ranging over
  `clientKVAt`, `kvObjAt`, `lessorAt>lessorRemoteAt` and `authObjAt`. They are `KV_Put_dist`'s stacks with
  `kvClientAt` replaced by `watchClientAt`.
- **Positive opaques.** Every positive opaque occurrence in `Watch_dist`'s walk is at `cb=3`, inside those contracts'
  pres: `grpcConn` 8, `credsYieldRaw` 8, `metadata.builtRawMDRaw` 16. None is at `cb=0`.
- **Truncations.** The 27 distinct truncation notes are exactly `KV_Put_dist`'s (set difference empty both ways). All
  293 truncation events have `…, isNewClient, watchClientAt, spec` at the bottom of their stack. None is in the post,
  in `watchCtx`/`outMD`/`optsAt`, or in the `□ AU`.

## What 2b's `8/0` means here

Rule 2b compares two counts. One is what the axiom hands to a callback the user supplies, here the `levelTok 0` in
the pre of the retry-interceptor contracts that `isNewClient` holds. The other is what the user supplies directly,
not counting what callbacks hand back: here 0. The danger it guards against is an axiom whose implementation calls the
user's callback on a goroutine that has no spare token. On the caller's goroutine, the caller's own token may be
committed elsewhere, for example to a `wgAdder` deposit or a reader slot. If the callback then never returns, its
token is free for other code, which then holds tokens that no `Fork` stands behind. `notes/axiom-review/r11-grpc-threadtok.md`
is the precedent. There the same gap let more handler runs be alive than `threadBound` allows.

So the entry is sound if and only if both of the following hold for the code the axiom is about (the translated
`(*watcher).Watch`/`RequestProgress`, the `App (Val (w @!! … @!! "Watch")) …` of the statement):

- **(a)** It never calls these contracts on the caller's goroutine.
- **(b)** Any goroutine that calls one has a token behind which a real `Fork` stands.

## The code: (a) and (b) hold, more strongly than the entry says

- **The caller's goroutine.** In the translated `watcher.Watch.impl` and `RequestProgress.impl`
  (`Code/go_etcd_io/etcd/client/v3/chunk0.lean:9246-9631`), the only calls are:
  - `sync.Mutex` `Lock`/`Unlock`, `context.Context` `Done`/`Err`;
  - `OpWatch`, `streamKeyFromCtx`, `errors.New`, `make`/`append`/`close`;
  - channel operations on `reqc`/`retc`/`donec`;
  - `newWatcherGRPCStream`, and `RequestProgress` itself (the `donec` retry).

  `newWatcherGRPCStream.impl` (`:9188-9246`) reads the `remote` field without calling it. It calls
  `context.WithCancel`, makes channels, and `Fork`s `wgs.run()`. Nothing on the caller's goroutine touches the
  connection. The Go (`clientv3 watch.go`, `github.com/upamanyus/etcd/client/v3@…-df6af0c36a6b`, lines 281-444) says
  the same.
- **No goroutine of the call ever calls the counted contracts.** The only connection call in `watch.go` is
  `openWatchClient`'s `w.remote.Watch(w.ctx, w.callOpts...)` (line 1069). It is a gRPC stream open, which goes
  through the stream interceptor (`etcdWatchConn`'s `etcdConnStream`, grpc's `NewStream`), not through the unary
  interceptor. The other goroutines (`serveSubstream`, `serveWatchClient`, `sendCloseSubstream`, the
  `waitCancelSubstreams` helpers) use only the stream's `Send`/`Recv`/`CloseSend`. The 8 contracts the walk counts
  are `etcdInterceptorOk`/`etcdInterceptorOkW` of the four `isEtcdConn`s: the KV's, the `KV` field's, the lessor's
  and the auth client's. They belong to the client's other fields. The unary retry interceptor is called by no
  goroutine that `Watch`/`RequestProgress` runs or starts. (a) holds, and (b) holds vacuously for these contracts.
- **What `run` does use has a `Fork` behind it.** This is the in-process proof's token flow.
  - `watcher__newWatcherGRPCStream.lean:95` applies `wp_fork_tok_body` to the translation's `Fork`. This is a model
    `Fork`, unlike r11's handler runs, so it is backed by the thread fuel.
  - `watchGRPCStream.run.spec` takes that `threadTok` and returns it. The walk of `wp_run` shows `tok:T` 1 in and
    1 out at `cb=0`.
  - `run`'s proof and `newWatchClient`'s split it with `threadTok_level0` around each stream call
    (`watchGRPCStream__run.lean:240,524`; `__newWatchClient.lean:336`).
  - `openWatchClient.spec` takes `levelTok 0` and returns it.

  The dist call runs the same translated code against the network. Nothing proves this for the dist call: it is the
  interim axiom's own content, as `WatchDist.lean`'s "Why it is true" says. But the token flow is identical.
- **The source specs carry no token either.** `watcher.Watch.spec` and `watcher.RequestProgress.spec` are proved
  (`Link.lean:1265-1271`) and their pres and posts have no token. The dist statements change only `isClientWatcher V
  w` to `watchClientAt cl w eps V Γ` and drop the auth row, so `supplieddirectly0` is the proved specs' own shape.
  Neither function needs a caller token in Go: it makes no RPC, and `sync.Mutex` takes none.
  `wp_newWatcherGRPCStream`'s walk has no token at all; the fork token is internal to its proof.

## Trying to extract a token

There are three positions where a user could receive a token or a counted resource from these axioms. None of them
gives one.

1. **The post.** `Watch_dist`'s post is `isSpsc γw.spsc ch (watchStateElemP Γ.kv γw … Q True) (fun _ => True) ∗
   spscConsumer … ∗ monoListIdxOwn …`. An element (`WatchStateDefs.lean:322`) is:
   - `respAtP`, the pure/persistent `watchStateRespOkP` and `cmpOkOf`, and two `monoListIdxOwn` fragments;
   - `□ (⌜…⌝ → True)`;
   - `□ Q σ`.

   `Q` is the user's own: the only `□ Q σ` the axiom can hand out is the `COMM □ Q σ` of the user's `□ AU`. So with
   `Q σ := levelTok 0` the user would have to prove an AU that yields a persistent `levelTok 0`, which they cannot do
   without already having one. The walk confirms this: no positive token or opaque at `cb=0`, and no rule-3 finding.
   `RequestProgress_dist`'s post is `statusErrOk err`. Nothing comes out of either post.
2. **The callbacks' pres (the 2b position).** This is the only remaining route, and in the logic it does give a
   derivation:
   - Dial a connection with your own unary interceptor `ic`. Prove `etcdInterceptorOk ic` for it, where `ic`'s body
     sets a heap flag, deposits its `levelTok 0` into an invariant `flag ↦ false ∨ (flag ↦ true ∗ levelTok 0)`, and
     loops forever. Its post then holds vacuously, by partial correctness.
   - Assemble `isNewClient` around it, call `Watch_dist`, and read the flag. In the `true` branch you open the
     invariant and hold a second `levelTok 0` on the caller's goroutine.

   The derivation is valid against any triple that consumes such a contract. So the question is only whether the
   `true` branch can happen in a real run with no `Fork` behind the token. For these two axioms it cannot. By the
   previous section, no goroutine of the call ever runs `ic`. The flag can be `true` only if some other code of the
   user's own ran `ic`, on a goroutine with its own token, and that goroutine is now stuck in `ic` forever. A thread
   handing its token away and diverging is possible in the base logic anyway (`wp_fork_tok_body`'s child need not
   return), and the adequacy's thread count still includes the stuck thread. So the branch gives nothing beyond the
   base logic. `KV_Put_dist`'s accepted `8/1` is weaker on this point, and still sound: there the interceptor does run
   on the caller's goroutine, with the caller's lent token.
3. **Rule 7's `∃ P : IProp`.** The 4 `P`s are `isCancelCtxOf`'s Done proposition inside `ctxOk ctx cd` in those
   same contracts' pres. They are axiom-picked values that the user's `ic` proof would receive. They sit inside
   contracts that are never called, so no user code receives one. As in `KV_Put_dist`, `P` is used only in the
   context handle and no post mentions it.

The `trunc` lines add no unknown. Every truncated subterm is inside the consumed `isNewClient` (contexts, `isMutex`,
`named`, the models' projections, `cd.4`, `dghostVar`), so it is something the user supplies. A truncation there can
under-count only what the axiom receives, or what it hands to the never-called contracts. It cannot under-count what
the user receives at `cb=0`.

## Corrections to the entry text

The keys and the `trunc` lines stay as they are. Suggested wording:

- **`Watch_dist` entry.**
  - Today: "…in Go the call makes no RPC on the caller's goroutine, and the stream's goroutine (`go wgs.run()`) calls
    the connection with its own fork token (`wp_fork_tok_body`)…". This reads as if `run` called the counted contracts.
  - With the correction: "`isNewClient`'s unary retry-interceptor contracts (`etcdInterceptorOk`/`OkW` of
    `clientKVAt`/`kvObjAt`/`lessorAt`/`authObjAt`), which no goroutine of the call runs. The caller's goroutine
    makes no RPC. The forked `run` only opens a stream (`w.remote.Watch` -> `NewStream`, the stream interceptor),
    with `levelTok 0` split from its own fork token (in-process: `wp_fork_tok_body`, `threadTok_level0`). `P` is the
    binder of those uncalled contracts' `ctxOk`."
- **`RequestProgress_dist` entry.**
  - Today: "it only sends on the stream's `reqc`".
  - With the correction: "as Watch_dist's: it takes the lock, creates the stream when there is none (the same `go
    wgs.run()`), and sends on `reqc` (retrying itself on `donec`); no RPC on the caller's goroutine".
- **Header paragraph.** "So a token any contract is called with is the forked goroutine's own" should become "The
  counted contracts are never called; the only connection call, `run`'s stream open, uses the forked goroutine's own
  token". The header's last sentence already says the unary contracts are never called, so the two sentences now pull
  in different directions. Optionally, also note that the fork-token flow is the proved in-process code's: the dist
  call runs the same translated code, and no proof covers it.
