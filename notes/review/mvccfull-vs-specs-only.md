# Review: mvccfull F1's specs (branch `lean`) against `specs-only`'s

Reviewer: an independent agent, 2026-11-10. Read-only on both worktrees, apart from this file.

- **A** = `lean` at `63d962df7c` (worktree `mvcc-full-tester`): F1's restated mvcc/lease specs and
  the new law modules (`git diff 037bf21c75 63d962df7c`; `notes/decisions.md` l.34067-34105).
- **B** = `specs-only` at `157a6903c5`: specs only, over opaque predicates, no proofs
  (`notes/specs-only/README.md`).
- Go: `/home/ubuntu/etcd-grove/.lake/go-src/etcd` (checked out at `ce3dbc0`; the files cited
  below are the same ones both branches cite).
- Judged by `.claude/skills/spec/PRINCIPLES.md`. Context for the comparison: A's
  mvcc `New`/`NewStore` are proved (`mvccApi_New`, `NewStore_wp_proof`) and its `NewLessor` is an
  axiom. B's specs are all unproved, and its `NewLessor` is an assumed spec too. So for A, "true"
  means proved, or an axiom checked against Go. For B it means the proof sketch is plausible and
  the statement agrees with Go.

## 1. `mvcc.New` / `mvcc.NewStore`, and the restore path

A: `Spec/.../storage/mvcc/Api.lean:926-1009` (`api.New.spec`, `api.NewStore.spec`), the internal
`NewStore.lean`/`newWatchableStore.lean`/`New.lean`. B: `Spec/.../storage/mvcc/{New,NewStore,
store__restore,newWatchableStore}.lean`.

**Both true of the Go code, as far as I checked** (`kvstore.go:87-135`, `restore()` `:317-420`):
- both handle `lg == nil` (A in its internal spec; B as `⌜lg = null⌝ ∨ isLogger`);
- both take a real `*lessor`, so `restore()`'s `panic("no lessor to attach lease")` (`:396-399`)
  cannot be reached;
- both say that an unfinished compaction is resumed once (`compactLockfree`, `:411-421`): the hook
  runs once and there is one commit;
- both give the store at the image's state, with the open token, the whole backend share and the
  reader tokens.

**Where they differ:**

| | A | B | better |
|---|---|---|---|
| Lessor resources | `lessorRdOf γl ∗ isLessor le γl ∗ rdOwn γl rd0 ∗ leaseOwn γl Ls ∅` (4 predicates); post `leaseOwn γl Ls (pendItems σ.log [])` | `Lease.isLessor le γl c ∗ Lease.lessorState γl n ls` (2); post `⌜RestoreLs {ls with rd} h.store ls'⌝ ∗ lessorState γl n' ls'` | B (fewer abstractions, one writer token) |
| Re-attachment premise | `⌜∀ it lid, pendItems … = some lid → lid ∈ Ls ∧ |key| < 2^63-1⌝` | none: `RestoreLs` folds `LessorState.attach`, a no-op on a dead lease (`lease/Api.lean:202-206`) | **B** (see F-A2) |
| Lessor's prior items | must be empty (`leaseOwn γl Ls ∅`) | any `ls` | B |
| Reachability | premise `⌜MvccReachable σ ∧ σ.pending = none⌝` | none; the law `mvccImage_reachable.spec` (`ApiStorage.lean:590`) derives it from the image | B (asks less, a law in place of a premise) |
| Compaction-resume resources | taken and given only `if u` | taken always, `Pre ∗ X` back when `¬u` | A (less glue at `u = false`); the two are equally strong |
| Storage predicate | `mvccStorageFor` is `@[no_expose]` (sealed) | `mvccStorageFor` is a transparent `def` over opaques (`ApiStorage.lean:513`) | A (sealing) |
| Config premise | `batchLimitOk` = `0 ≤ limit ≤ rangeLimitMax` (`InvStore.lean:1555`, a scope restriction) | `storeCfgOk` = `0 ≤ limit` | B is weaker. Whether its compaction sketch survives without the upper bound is **uncertain** |
| Extra post resources | `⧖ (logCh σ.log)` | `mvccRevLent γ false ∗ mvccRestoreGate γ 1` (the `Rev` pool, and the hash/restore exclusion for `issues/etcd-mvcc-hash-currentrev-race.md`) | different scope: B covers the hash race that A's API leaves to the server |
| Store's lessor name | `⌜mvccLeases γ = γl⌝`, a projection of the ghost name | `mvccLessorIs γ γl`, persistent | B: no projection of a ghost-name record |
| Package inits | also takes the backend's and schema's `isPkgInit` | mvcc's only (B's `isPkgInit` includes dependencies, `Spec/PkgInit/Base.lean:4`) | B, if Perennial's `isPkgInit` covers dependencies (**uncertain** on A's side) |

**F-A1 (A, preference: strength, and "every premise has a source").** A's caller must supply
`MvccReachable σ`. A store it stopped gives this (`Api.lean:1095`). A restart reading a disk image
written by another process has only `mvccImage`, which in A carries no reachability
(`EtcdBackend.lean:291-299`). B's law `mvccImage_reachable` is the source.
*Restatement:* drop `MvccReachable σ` from `New`/`NewStore`/`Restore`. Add the law
`mvccImage D L c u → MvccReachable ⟨L, c, none⟩` (or put it inside `mvccStorageFor`).

**F-A2 (A, hard rule "no unneeded premise", and a burden on callers).** The item premise is there
because A's bundled lessor contract (`isLessor`, `InvStore.lean:1990-1997`) gives `Attach` only
with `⌜id ∈ L⌝`. But Go's `restore()` logs a failed `Attach` and goes on (`kvstore.go:400-407`). So
the code does not need the premise; only A's `Attach` clause does.
- *Who pays:* the tester discharges it from its own model (`examples/mvccfull/LogLemmas.lean:738`,
  `logOk_leases`). A real server restart (R2d'b, `notes/restart-plan.md`) would have to carry an
  invariant across the disk image: every key's lease is in the lease bucket. That invariant spans
  the KV store and the lessor.
- *Restatement:* add an `Attach` clause for a lease that is not live, returning `ErrLeaseNotFound`
  with the owner unchanged. Then `New`/`NewStore`/`Restore` post
  `∃ I, ⌜I = pendItems σ.log [] restricted to Ls⌝ ∗ leaseOwn γl Ls I`, as B's `RestoreLs` does, and
  drop the premise.
- The `< 2^63 - 1` key bound is a Perennial-side limit: keep it local, in the `Attach` clause.

**F-B1 (B, measures: glue).** B's `New`/`NewStore` ask for `storageHook B dq f ∗ Pre ∗ hookRun … ∗
X ∗ storageReq …` even when `u = false`, and hand `Pre ∗ X` back. Every fresh-boot caller has to
make them (`Pre = X = True`, `storageReq_true`, `hookRun` at `nil`).
*Restatement:* take A's `if u then … else True` in both pre and post.

**Callers.** A: `examples/mvccfull/runner__open.lean:62`, `mvccrand/runChecks.lean:64`, and
`etcdserver/Results.lean:916` (`server_kv_backend`), all proved. B: `NewServer`'s sketch
(`etcdserver/NewServer.lean:31-32`) and the snippet `specreq/mvcc/restore.go`. Neither branch
shows a server restart discharging New's premises.

## 2. `WatchStream.Watch`

A: `Api.lean:750-781` (`WatchStream.Watch.contract`, at a receiver `(ty, v)`). B:
`watchStream__Watch.lean:72-96` (concrete, at `w : Loc`).

**True.** Both match `watcher.go:114-143`:
- the range check `len(end) != 0 && bytes.Compare(key, end) != -1` comes first, before the lock. A
  writes it `e ≠ [] ∧ ¬ GoStringLt kk e`. B adds `endk ≠ slice.nil`, which `e ≠ []` already
  implies;
- a closed stream gives `ErrEmptyWatcherRange`;
- an id of `0` gets the auto id.

**Comparison.**
- **Atomic update on an empty range.** A asks for the update only for a non-empty range
  (`⌜empty⌝ ∨ au`). B always takes it and hands it back on refusal. A asks less, and its
  disjunction is a case split on the input, which the principle allows. But a caller can pick the
  right disjunct at an empty range, and then loses its update (A's empty arm gives none back).
  *Suggestion for A:* write it `if decide empty then True else au`, so there is no lossy choice.
- **Concurrency.** B threads an exclusive `wsCtl ι n`, which makes `Watch` single-caller per
  stream. Go's `Watch` is safe under `ws.mu` (`:121`). A's atomic update over the stream's state is
  persistent-friendly. This is a point for A ("faithful to concurrency"). B's restriction holds
  only because v3rpc's `recvLoop` is the only caller; it is not stated as a scope restriction.
- **Context.** B asks only `OtelTrace.ctxSpanOk ctx`. A asks for `TODO` or `isContext ∗
  spanCtxOk`. The code only calls `trace.SpanFromContext(ctx)` (`:137`), so B asks less.
- **Facts in the post.** B's post gives persistent facts (`wsReg`, `wsSentLb`, `mvccLb`, the
  position `W.pos`) and the id `= n`. A's post gives them through `Q σ S id`, the caller's
  update. They look equally strong for their callers. B's is easier to chain.
- **Spec shape.** A states the contract once at a receiver and makes each concrete spec an
  instance (`watchStream.Watch.spec`, `Api.lean:924`), which is the "per (type, method)"
  principle. B has only the concrete spec, so a client holding an interface value (v3rpc holds
  `mvcc.WatchStream`) needs a bundle that B does not give.

## 3. `KV.Compact`, and its channel

A: `KV.Compact.contract` (`Api.lean:560-583`, with `compactChanOk` = "a receive returns some
value", `:417-419`) and, new, `compactChan.law`/`KV.Compact.contractC`
(`ApiCompactChan.lean`). B: `KV.Compact.contract` (`Api.lean:424-440`, with `compactChanOk` = a
`recvAu` on a `chan struct{}`, `:280-283`).

**True.** Go (`kvstore.go:197-221`, `:270-282`):
- at or below the compaction revision: `make(chan struct{})` and `ErrCompacted`;
- above the current revision: `nil` and `ErrFutureRev`;
- otherwise `compact()`'s `make` (`:236`).

Both contracts state these three arms correctly.

**F-A3 (A, hard rule "one spec per function").** `contractC` is a second contract of the same
method beside `contract`. It is reached through a law at every handle, and `contract` follows from
it. The reason given (`ApiCompactChan.lean:11-12`, "so that adding it leaves `Api` … as they
were") is the build budget, not a spec reason.
- *Restatement:* strengthen `compactChanOk` in place to
  `⌜ch ≠ chan.nil⌝ ∗ □ {{True}} receive ch {{ ok, RET (#(), ok); True }}`, and delete
  `contractC`/`compactChan.law`. Better still, take B's `recvAu` form (below).

**F-A4 (A, preference: strength).** B's `compactChanOk` (`recvAu` for any `Φ`) covers a `select`
case as well as a plain receive. A's covers a plain receive only. etcd's own compactor waits on
the channel in a plain receive, but a client with a timeout `select` would need B's.
*Restatement:* `compactChanRecv ch := ⌜ch ≠ nil⌝ ∗ ∃ γc, isChan ch γc Unit ∗ □ ∀ Φ, (∀ v ok, Φ v ok) -∗ recvAu γc Unit Φ`.

**F-A5 (A, "no unneeded premise").** A takes `⌜1 ≤ rev⌝`; B takes `⌜rev ≠ 0⌝`.
- A negative revision returns `ErrCompacted` in Go: `rev <= compactMainRev`, since `compactMainRev
  ≥ -1`.
- A client can send one: `CompactionRequest.Revision` reaches `KV().Compact` unchanged.
- Only `rev = 0` needs excluding, while the model has `crev ≥ 0`: at `compactMainRev = -1`, Go
  compacts to `0`.

*Restatement:* `⌜sint.Z rev ≠ 0⌝`, with the negative case in the `ErrCompacted` arm.

## 4. The error variables

A: `errVars.law` (`Api.lean:1044-1066`): four variables, each an `errorsNewVar` (dynamic type
`*errorString`, and the `Error()` triple), pairwise `errVarApart`. B: `init.spec`
(`Api.lean:686-698`: `ErrCompacted`, `ErrFutureRev`, `ErrRevisionNotFound`, as raw
`*errorString` cells, `Nodup`) and `watch_init.spec` (`ApiWatch.lean:414-425`: the three watcher
errors through `errMsgOk`, which hides the dynamic type, `Nodup`).

**True.** Each is its own `errors.New` with its own message (`kvstore.go:38-39`,
`watcher.go:29-32`).

**F-B2 (B, measures: abstractions; and strength).**
- *Three encodings for one concept:* raw cells for mvcc's core errors, `errMsgOk` for the watch
  errors, and Perennial's `errors.newVar` + `errIs` for the lease's (`lease/Api.lean:540-553`).
- *No dynamic type for the watch errors:* `errMsgOk` gives none. A client's `err ==
  ErrEmptyWatcherRange` is Go's interface `==`, which panics on an uncomparable dynamic type. So
  without the type the comparison cannot be proved panic-free.
- *Distinctness only within each group:* nothing says `ErrCompacted ≠ ErrEmptyWatcherRange`.

*Restatement:* one law in A's form (`errorsNewVar` per variable, apartness over the whole list),
over all six variables.

**F-A6 (A, minor).**
- A leaves out `ErrWatcherDuplicateID` (returned by `Watch` for a duplicate caller-chosen id, out of
  scope today) and `ErrRevisionNotFound` (internal to the key index).
- The apartness's `∀ X Y, ⌜X ∈ errVarNames ∧ …⌝ -∗` form needs `simp` per use (the docstring
  says `decide` fails). B's existential values with `Nodup` are simpler for a client.

## 5. `lease.NewLessor`, recovery, `Leases`

A: `Spec/.../lease/NewLessor.lean` (an axiom, restated today over a bucket with records),
`lessor__Leases.lean`, the law `leaseOwn_leases` (`Proof/.../lease/LeaseOwnLeases.lean`). B:
`Spec/.../lease/{Api,NewLessor,lessor__Recover,lessor__Leases}.lean`.

**The two specs' agreement with Go** (`lessor.go:208-249`, `initAndRecover` `:808-835`). Both
agree on:
- every record is loaded with a fresh `*Lease`;
- each lease's TTL is raised to `minLeaseTTL`;
- no item is attached and no range deleter is set;
- the run loop is started;
- a stop right is given.

The details:
- A states the records exactly (`bktEnts = recs.map leaseRecEnc`), a scope restriction it says so
  itself.
- B states them through `beLeases b B`, whose realization says each record unmarshals and is keyed
  by its id. Go takes the id from the record's value (`lpb.ID`, `:818`), so B's realization must
  also tie the value's ID to the key. It says "keyed by the id's bytes", but `leaseBktIs` is not
  shown: **uncertain**.

**F-A7 (A, hard rule "sound", open and known).** A's restated axiom still takes only `⌜lg ≠ null⌝`
(`NewLessor.lean:227`). A's own audit records that this makes the axiom chain false:
- a zero `zap.Logger` panics in `scheduleCheckpointIfNeeded`'s `Debug` (`lessor.go:760`);
- the panic is reached through the proved `Grant` on a primary lessor;
- `notes/audit.md:383,390`, sweep B3-2, gives the cases `examples/axiomcx/lessormethods`
  `PromoteZero`/`GrantZero`, 10/10 runs;
- a repair was proposed and not applied.

F1 restated this exact statement without taking the repair. B takes it: `Zap.isLogger lg`
(`B NewLessor.lean`, pre).
*Restatement:* replace `⌜lg ≠ null⌝` by the zap-zero repair's `zapLoggerOk lg`, in the pre and in
`lessorCfg`. I did not re-run the cases; I took them from A's audit.

**F-A8 (A, preferences: abstraction and coupling; the largest gap between the branches).**
- *Coupling:* A's lease constructor imports `Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot`
  (`NewLessor.lean:30`). Its statement names:
  - mvcc's `KBReal` and `leaseParams`;
  - the backend's `isBackend`/`bOpen`/`wbTok`/`rbPart`/`rbOwnIn`/`bktEnts`, at `d.γB`/`d.P`;
  - apply's `leaseIs`;
  - etcdserver's `lessorApplyOk`/`lessorCkptOk`.

  So the lease API is stated over its dependents' and its dependency's implementations, against
  "an API is stated over the abstractions it builds on".
- *Abstractions:* the post has about 20 conjuncts:
  - `lessorInv`, `lessorModeIs`, `lessorCfg`, `lF "minLeaseTTL" ↦□`, `lessorExpiredC`,
    `lessorGuard`;
  - `actualMaxReaders` copies of `lessorRdOf` (against the bounds principle);
  - `leaseOwn`, `leaseEver` (the ids ever held: a tracking set), `leaseRevokers`, `rdOwn`;
  - `lessorBeOn`, `lessorStopTok`, `leaseReqIs` (requests: ghost bookkeeping), `lessorAt`, and the
    `Lookup` triple.

  The caller-chosen guard `GA` saved in the lessor is HoCAP-shaped. It may fit the approved
  departure (a persistent predicate fixed at creation), but the spec does not say it departs.
- *Pure premises:* five of them sit outside the triple as Lean implications (`S "lease" → …`).
  The style rule asks to move them inside when the spec changes, and this one changed today.

B's version:
- one writer token `lessorState γ n ls` over a transparent model `LessorState`
  (leases, items, keys, bucket, backend, deleter);
- a history `lessorAt`, and counted `lessorReaders γ lessorTokN`;
- the lessor's own opaque view of the backend (`beOk`, `beLeases`), realized by the backend
  through `LeaseBackend.lean` laws.

That is the shape the principles ask for: observable state, no tracking set, no guard, low
coupling.
*What A should take:* not a rewrite now, which would be a large redesign of a proved package's
clients, but the direction. (1) Replace the backend vocabulary in the lessor's statements by a
lessor-side `beLeases`-style predicate with an introduction law in the backend or etcdserver.
(2) Replace `actualMaxReaders` copies by a counted pool predicate.

**F-B3 (B, "no unneeded premise", minor).** B's `NewLessor` takes `threadTok` and returns it
(re-review RR4). The run loop runs on the token the fork mints (`wp_fork_tok_body`, Perennial
`GooseLang/Lifting.lean:1993`), and `initAndRecover` needs none. *Restatement:* drop `threadTok`
from the pre and the post.

**F-B4 (B, a scope gap in its model).** B leaves out `RemainingTTL` (the checkpointed TTL)
entirely. A's `recTTLs` tracks it. No B caller needs it today, so this is a margin, stated as
such.

**`Leases`.**
- *A:* `lessor.Leases.spec` takes `threadTok ∗ ⌜threadBound GF ≤ 2^30-1⌝ ∗ ⌜receiptBound GF ≤
  2^62⌝`. That is older than F1, but against the bounds principle, which forbids `threadBound` in
  a spec. A's new `leaseOwn_leases` (proved) turns the reader's snapshot into the owner's live set.
  It is a sound and useful law, with one caller (`mvccfull/runner__checkLeases.lean:174`).
- *B:* takes `lessorReaders γ 1 ∗ lessorLb γ i`. With the writer token, `lessorState_le` and
  `lessorAt_agree` give the same conclusion as A's new law, with no law of its own.

So B's vocabulary makes A's `leaseOwn_leases` unnecessary.
*A should take:* B's reader token in place of the bound premises, when `Leases` next changes.

**`Recover`.** A has no new statement (F1 did not touch it). B's `lessor.Recover.spec` gives the
old backend's `beOk ∗ beLeases` back and the loaded state at `n + 1`. That is clean, and B's
`NewLessor` is literally its instance at an empty prior state. A argues the same link in prose
(`NewLessor.lean:56`).

## 6. Backend open/close/stop laws, and the other new law modules

A adds eight modules. B has no counterpart: its backend is a redesigned, durable API
(`backend/{New,backend__Close,Durable,StateImage,LeaseBackend}.lean`).

| A law | kind | verdict |
|---|---|---|
| `StopLaws.bStopView_rbPart_agree` | elimination | good. B's `Close` post gives the agreement directly (`⌜Image.agree F I V⌝`), which A needs a law for because its view and part are separate predicates |
| `HooksLaws.hooksOk_nil` | introduction | good |
| `RwLensLaws.rwLens_refl` | introduction | good |
| `GuardLaws.leaseGranted_of_guard` | introduction | good (but see F-A8 on `GA` itself) |
| `LessorApplyLaws.lessorApplyOk_at` | elimination | good (a narrow law at a consumption point) |
| `NewKLaws.wbInit_val`, `rdPoolN_val` | **constant by value** | **F-A9** |
| `NewKLaws.bFresh_eq`, `WbTokLaws.wbTok_toks`, `BkRTLaws.bkRT_eq` | **⊣⊢ body** | **F-A9** |
| `NewKLaws.newPostKP_intro` | introduction restating 11 internal conjuncts | **F-A9** |

**F-A9 (A, sealing and bounds).** These laws make unfolds official instead of removing them:
- `wbTok_toks : wbTok γ ⊣⊢ ownToks γ.wb 1` exposes the ghost-name field `γ.wb`;
- `bFresh_eq` and `bkRT_eq` restate bodies;
- `wbInit_val : wbInit = 2^40 - 1` hands clients the number, against "a size bound … with its
  named constant";
- `newPostKP_intro` lists `bViewC`/`rbOwn`/`rdPool`/`rdAuth`/`rdStock`/`dlInit`/`fkCl`/`srSlot`.

These modules are in `etc/api/backend.txt:22-26`, so they are API. A change to any body is now an
API change. Their users are the tester only (`mvccfull/{Writer,runner__apply,runner__restore}.lean`).
*Restatement:*
- replace `wbTok_toks`/`bFresh_eq` by the operations the tester performs: split/join of the
  write-back stock (`wbToks (n+m) ⊣⊢ wbToks n ∗ wbToks m`, `wbToks 1 ⊣⊢ wbTok`), and
  `bFresh ⊢ wbToks wbInit ∗ bOpen γ 1` with the stock's size kept as the opaque named constant;
- drop `*_val`: the tester's arithmetic should take `wbInit`'s lower bound as a named law
  (`2^40 - 1 ≤ wbInit`, or the inequality it needs);
- `newPostKP_intro` is acceptable only if no narrower introduction serves; check what
  `runner__restore` actually trades.

`ApiLaws` (`hookRun_nil`, `mvccDeleter_persistent`, `mvccDeleter_intro`) is fine: introduction
laws for what callers hold. In B, `hookRun` and `mvccDeleter` are transparent `def`s, so B needs
no such laws, but B also exposes their bodies.

## 7. Where one branch has no counterpart

- **In B, not A:**
  - the `Restore`/`Hash` exclusion `mvccRestoreGate` (the hash/currentRev race);
  - the `Rev` pool (`mvccRevTok`/`mvccRevLent`, the compactor's loop outliving the store);
  - a durable backend API (`beDurInv`, `beFinal`, images);
  - `Lease.Recover` over the lessor's own vocabulary;
  - `RestoreLs` (failed re-attachment);
  - `mvccImage_reachable`;
  - the expiry mode with the trusted `leasesOutliveRun`.
- **In A, not B:**
  - proofs. A's mvcc `New`/`NewStore`/`Watch`/`Compact` are linked results; B's are sketches;
  - `leaseOwn_leases`, which B's vocabulary makes unnecessary;
  - `compactChanRecv` as a plain receive (B's is stronger);
  - the four-variable `errVarApart`;
  - the backend glue laws of section 6;
  - the receipt `⧖ (logCh σ.log)` in `New`'s post;
  - `KV.Compact`'s interface-receiver contract shape. B has it too for KV, but not for
    `WatchStream`.

## 8. Ranking by need of revision

**A** (most first):
1. `lease.NewLessor`: F-A7 (the known premise gap, a hard rule) and F-A8 (coupling and bookkeeping
   state).
2. `mvcc.api.New`/`NewStore` (and `Restore`): F-A2 (the item premise), F-A1 (reachability as a
   premise).
3. `KV.Compact.contract` + `compactChan.law`: F-A3 (two contracts), F-A4, F-A5.
4. The backend glue laws: F-A9.
5. `WatchStream.Watch.contract`: the lossy disjunct, a cosmetic `if` form.
6. `errVars.law`: F-A6, minor.
7. `Leases.spec`: its bound premises, older than F1.

**B** (most first):
1. The error variables: F-B2.
2. `New`/`NewStore`: F-B1 (unconditional hook resources).
3. `watchStream.Watch`: the unstated single-caller restriction (`wsCtl`), and no
   interface-receiver contract.
4. `NewLessor`: F-B3 (`threadTok`), F-B4 (margin); `beLeases`'s ID-to-key tie, **uncertain**.

## 9. Verdict

The overall picture:
- B's lease vocabulary is clearly better: one writer token over a transparent `LessorState`, a
  history, counted readers, and the lessor's own backend view.
- So are B's restore semantics (`RestoreLs` in place of a live-lease premise), its reachability as
  a law, and its `select`-capable compaction channel.
- A is better on what it has proved:
  - sealing (`mvccStorageFor` `@[no_expose]`);
  - interface-receiver contracts;
  - one uniform error-variable law;
  - a `Watch` that does not demand an update it never uses;
  - compaction-resume resources asked only when `u`.

**A should take from B, statement by statement:**
- `Zap.isLogger lg` (or `zapLoggerOk`) in `NewLessor` (F-A7, now);
- an `Attach`-not-found clause and a `RestoreLs`-style post in place of New's item premise (F-A2);
- `mvccImage_reachable` in place of the `MvccReachable` premise (F-A1);
- `compactChanOk` strengthened in place to B's `ch ≠ nil ∗ recvAu` form, deleting `contractC`
  (F-A3, F-A4);
- `rev ≠ 0` (F-A5);
- the counted reader token for `Leases`.

Longer term, re-base the lessor's API on a writer token over a pure `LessorState` and a lessor-side
backend predicate (F-A8).

**B should take from A:**
- A's `if u then … else True` resume resources (F-B1);
- one `errorsNewVar`-style error law with apartness across all of the package's variables (F-B2);
- the `Watch` precondition that asks for the update only on a non-empty range, written as an `if`;
- `Watch` as an interface-receiver contract, with an atomic update over the stream's state (or the
  single-caller restriction stated);
- `mvccStorageFor` sealed;
- `NewLessor` without `threadTok` (F-B3).

No new bug in the Go code was found. The Go behaviours relied on above (a failed `Attach` logged,
`ErrCompacted` for a negative revision, the zero-logger panic) are known, or are not bugs. The
zero-logger case is in A's `notes/audit.md`, a premise gap in this repository's axiom and not a Go
bug, so nothing goes to `issues/`.
