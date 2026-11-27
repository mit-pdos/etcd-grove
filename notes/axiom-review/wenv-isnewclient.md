# Axiom review: the cross-machine client contracts under the new `isNewClient` (watcher-environment refactor)

Reviewed at branch `etcd-safe-wenv/2026-11-26`, commit `046615a437` (worktree `eg-es-wenv`, read-only), against the
change `923a4ae72c..046615a437`. That change edits no axiom's text. It changes the untrusted definitions that the
axioms' preconditions use: `isNewClient` (`InvClientNewResult.lean`), `watcherMu`, `wgsGuard` and `WEnv.atEps`
(`InvWatch.lean`). `isClientWatcherCore` and `isClientWatcher` keep their text, but their meaning changes through
`watcherMu`.

Evidence: a scratch Go module in `notes/axiom-review/wenv-isnewclient/` (`wenv_test.go.txt`, renamed so no Go tool
picks it up, with its `go.mod`/`go.sum`, which are N3's; its output is `output.txt`). It was run at go1.27.3 against
the pinned clientv3 fork (`upamanyus/etcd/client/v3@…df6af0c36a6b`, the `rev` in `etc/goose.py`) and grpc-go
v1.84.0. No counterexample was found, so there is no branch, no Goose project and no Lean proof. I did not run
`lake`, `lean` or `lean-check`. I did not update `notes/audit.md` or the `README.md` index, because the worktree is
read-only except for this file.

I formed my view from the code first. Only after that did I read §25 of `notes/etcd-dist-plan.md`, to compare. It
agrees with my analysis below (F2 in particular), except where noted.

## What changed

- **The lock invariant.** `watcherMu V w callSl` used to keep `isWGS V G callSl` for each stream in the map. It now
  keeps `wgsGuard V G callSl := □ (watchSrvFacts V -∗ isWGS V G callSl)`.
  - Writers (`watcher.Watch`, `RequestProgress`) insert `wgsGuard_intro` of the `isWGS` they built.
  - Readers (`Watch`, `RequestProgress`, `Close`) call `wgsGuard_elim` with the `watchSrvFacts V` of their own
    `isClientWatcher V w`.
  - `closeStream` only deletes an entry, so it needs no change.
  - `isWGS` is unchanged, and still contains `watchSrvFacts V`.
- **The watcher's environment.** `isNewClient cl eps V`'s watcher conjunct is now
  `isClientWatcherCore { V.atEps eps with conn, ics, wc, lg } w`, where
  `V.atEps eps = { V with nm := if V.addrs = eps then V.nm else 0 }`.
  - When `V.addrs = eps` this is the old environment.
  - Otherwise `nm = 0`. Then `watchConnFacts`' pure conjunct `∃ i, i < nm ∧ …` is false, so `watchSrvFacts ⊢ False`,
    and `wgsGuard ⊣⊢ True` is provable.
- **Proofs.** `newClient.wp_proof` now builds the watcher at `V.atEps eps`. `New.spec` keeps its text, so the
  caller still picks any `V`. `isNewClient_watcher_of` gains `hA : V.addrs = eps`.

## Axioms

| # | Axiom | Files | Reaches `isNewClient` through |
|---|---|---|---|
| 1 | `etcd_dist.Watch_dist.wp_proof` | `Proof/.../examples/etcd/dist/WatchDist.lean`; statement `Spec/.../dist/WatchDist.lean` | `watchClientAt` (`WatchClientDist.lean`) |
| 2 | `etcd_dist.RequestProgress_dist.wp_proof` | the same | `watchClientAt` |
| 3 | `etcd_dist.KV_Put_dist.wp_proof` | `.../dist/KVPutDist.lean`, `Spec/.../dist/KVPutDist.lean` | `kvClientAt` (`KVClientDist.lean`) |
| 4 | `etcd_dist.KV_Get_dist.wp_proof` | `.../dist/KVGetDist.lean` | `kvClientAt` |
| 5 | `etcd_dist.KV_Delete_dist.wp_proof` | `.../dist/KVDeleteDist.lean` | `kvClientAt` |
| 6 | `etcd_dist.KV_Compact_dist.wp_proof` | `.../dist/KVCompactDist.lean` | `kvClientAt` |
| 7 | `etcd_dist.Txn_Commit_dist.wp_proof` | `.../dist/TxnCommitDist.lean` | `kvClientAt` |
| — | `Client_Put_dist.wp_proof`, `Client_Get_dist.wp_proof` | `.../dist/ClientPutDist.lean`, `ClientGetDist.lean` | `isNewClient cl [ep] V` directly |
| (interaction) | `EtcdGrove.Client.Close.wp_proof` | `Proof/go_etcd_io/etcd/client/v3/Client__Close.lean` | none (pre `clientCoreAt`), but its Go body locks the watcher |

On this branch, `Client_Put_dist` and `Client_Get_dist` are **theorems**. They take `KV_Put_dist.spec` and
`KV_Get_dist.spec` as hypotheses and add no trust. Earlier reviews of the same axioms against the old definition:
`n3-watch-dist.md` (1, 2) and `n2-kv-dist.md` (3–7).

## Verdicts

| # | Verdict | Findings |
|---|---|---|
| 1 `Watch_dist` | **sound**; its docstring's soundness argument must be rewritten | F1, F2, F3, F5 |
| 2 `RequestProgress_dist` | **sound**; the same docstring change | F1, F2 |
| 3–7 KV, Txn | **sound, unaffected**: nothing in their statements, posts or arguments reads the watcher conjunct | — |
| `Client_Put/Get_dist` | theorems; no trust | — |
| `Client.Close.wp_proof` | **sound, unaffected**: its pre does not mention the watcher, and Go does not panic (W2) | F4 (wording) |

No finding is a counterexample. F2 is the important one. The old encapsulation argument says that no
cross-machine program has `watchSrvFacts`, and that premise is false in the logic. The argument still goes through
on a different premise: such an address is never served.

## 1. `Watch_dist`, `RequestProgress_dist`

### A. Did `isNewClient` become weaker?

- **At `V.addrs = eps`**, the conjunct is the old term (`WEnv.atEps_of`), except for `watcherMu`'s body.
  - A lock invariant is not monotone. So `isMutex mu (watcherMu V …)` with `wgsGuard` is neither weaker nor
    stronger as a proposition than with `isWGS`.
  - What the axioms implicitly promise is weaker. An axiom that runs `Watch` and unlocks must give back
    `watcherMu`, and the new body asks less of each stream (`isWGS ⊢ wgsGuard`).
  - What a later reader can get out of an axiom-inserted stream is also weaker. It gets nothing without
    `watchSrvFacts V`, and with those facts it gets exactly what it got before.
- **At `V.addrs ≠ eps`**, the lock is over an environment with `nm = 0`, and its streams' guard is provably `True`.
  - So the lock no longer pins `V`. Any two such `V` give equivalent lock invariants, so `isNewClient cl eps V` for
    one of them gives it for the others, as long as `isMutex` respects `⊣⊢` of its invariant, as an Iris `inv` does.
  - This is harmless. The axioms' posts read nothing of `V`, and every proved spec that reads the lock needs
    `watchSrvFacts`, which is `False` here.
- **Who can establish the precondition.** As before, only `New` can. `New.spec` is proved, for any `V` the caller
  picks. `isNewClient` holds `clientF cl "Watcher" ↦□ …`, which only `New` writes. `NewWatcher` and
  `NewWatchFromWatchClient` give a `*watcher`, but not a client field that points to it.

So the set of programs that reach the axioms' preconditions is unchanged. The precondition is not weaker in any
way the axioms can use.

### B. Can a spec that opens the lock observe or forge something new?

The pinned Go code locks `w.mu` (an unexported field, `watch.go:149`) only in four places:
- `Watch` (`:335-350`);
- `RequestProgress` (`:416-428`);
- `Close` (`:396-399`);
- `closeStream` (`:457-463`).

No other package can lock it. The specs and axioms for code that locks it:

| Spec | Takes | Under `wgsGuard` |
|---|---|---|
| `watcher.Watch.spec` (proved) | `isClientWatcher V w` (includes `watchSrvFacts V`) | inserts `wgsGuard_intro` of a real `isWGS`; reads with `wgsGuard_elim` and its own facts |
| `watcher.RequestProgress.spec` (proved) | `isClientWatcher V w` | the same |
| `watcher.Close.spec` (proved) | `isClientWatcher V w` | reads with its own facts (`watcher__Close.lean:77`) |
| `watcher.closeStream.spec` (proved) | `isClientWatcher V G.w` | deletes an entry; the rest of the map is kept by `bigSepM_subseteq`, whatever the element predicate is |
| `Watch_dist`, `RequestProgress_dist` (axioms) | `watchClientAt` (core only) | must give back `wgsGuard` for a stream they add; their posts say nothing of the lock |
| `Client.Close.wp_proof` (axiom) | `clientCoreAt` (no watcher fact) | post `True` |

- **Forging.** The only inserters are the two proved specs, which insert guards built from a real `isWGS`, and the
  two axioms. A spec that locks without facts now learns nothing: it gets guards, and a guard without
  `watchSrvFacts` cannot be opened. So the old danger, "a spec that locks without `watchSrvFacts` would read the
  `watchSrvFacts` an axiom-inserted `isWGS` claims", is gone.
- **Observing.** A reader can learn a stream's invariants only by presenting `watchSrvFacts` at the lock's
  environment. Whether a program that holds `watchClientAt` can do that is the question of section C.

### C. Can a cross-machine program hold `watchSrvFacts` for its watcher? (F2)

The old docstring and N3's section B say no: "`addrUnset` is spent". **That is not right.** A program can hold both
facts for the same address `a`:

1. `net.Listen(a)` consumes `netAddrFree a` (`addrClaim ∗ addrUnset`). It gives `netListenerAt l a` and
   `netAddrLeft a` (`InvNet.lean:76`: the pending set, `addrTok`, `lisTokInv`).
2. Build a gRPC server `gs` with etcd's `Watch` handler registered. The raw `grpc.start` axiom
   (`InvGrpcServer.lean:417`) consumes `grpcSrvNew ∗ netListenerAt l a` but not `netAddrLeft`. It gives
   `grpcAddrIs a γ ∗ grpcSrvCfg γ c`. Then `grpc.serveStream` gives `isGrpcStreamMd a "/etcdserverpb.Watch/Watch" …`
   without any `Serve`.
3. Use the leftover `netAddrLeft a` with `netProto_alloc`, `depSlots_alloc` and
   `addr_set_proto_tok … (grpcCliPI (etcdSvc Γ mid)) (grpcSrvPI …)`. That gives `grpcAddrAt a (etcdSvc Γ mid)`,
   which is `etcdAddrAt a Γ mid`.

The two facts live in unrelated ghost structures. `grpcAddrIsRaw` is opaque, and its only law is
`grpcAddrIs_agree`. So nothing refutes the pair. With an in-process server's `watchMemberFacts` and `New`'s
`grpcConn conn eps`, such a program can hold `watchClientAt cl w [a] V Γ` and `isClientWatcher V' w` for the same
watcher at `V.addrs = [a]`. It can then apply both the axioms and the proved specs to one lock.

I did not build this program in Lean. Every step is a spec or ghost law that exists today, and §25.4 reaches the
same conclusion. This held before the refactor too, so it is not new. But the docstring's premise is false.

**Why it still gives no counterexample.** Every endpoint of such a client is an address whose only server is the
`grpc.start`ed `γ`, whose configuration registers the `Watch` stream. Nothing can serve that address:

- `gs.Serve(l)` needs `grpcServeTok gs l a Svc`. That needs `grpcAddrAt a Svc`, and `a`'s protocols are set once,
  to `etcdSvc Γ mid`'s. It also needs `grpcServes (etcdSvc Γ mid) ics regs sregs`, which requires
  `etcdSvc Γ mid "/etcdserverpb.Watch/Watch" ≠ some _` (`InvGrpcRun.lean:151`). `etcdSvc` is opaque, so this is
  unprovable.
- A second server at `a` has no listener. `grpc.start` consumed `netListenerAt`, and `grpcAddrIs_agree` allows one
  `γ` per address.
- `Serve_dist` runs `etcdstart.Serve(s, a)`, which calls `net.Listen("tcp", a)` itself (`common.go:216`). That fails
  while `l` is open. Measured (W1): `bind: address already in use`, and `Serve` returns the error, which its post
  `True` allows.
- The program cannot close `l`, because `grpc.start` consumed its ownership.

So no stream to any endpoint of this client ever receives a response.
- Measured (W2: a listener with a registered but unserved `Watch` handler): `Watch` returns when its context ends
  (2.0 s), and its channel closes with 0 responses. clientv3's `WaitForReady` keeps `run` in `newWatchClient`.
  `RequestProgress` returns `context deadline exceeded`, which is `statusErrOk`. `Client.Close` returns `nil`.
  Nothing panics.
- The control (W3): the same handler, served, answers.

With no response, the axioms' false-in-reality lock contents never meet a fact they would have to justify. What is
left is the behaviour of the real goroutines toward a server that never answers. Those goroutines are the
in-process proof's subject, under the `watchSrvFacts` that really hold here:
- the context-end paths;
- `newWatchClient`'s error;
- `run`'s exit and `closeErr`;
- `closeStream`.

The axioms' posts claim nothing per response. Their elements exist only for responses, and the channel may close
at any position.

### D. Is the `∀ V` triple now valid? (F1)

- **At every `V` with `V.addrs ≠ eps`** (including `V.nm = 0`, N3's F3 case), the guard holds outright. The lock is
  no longer an obstacle to the triple's validity. What still prevents a proof is the stream entry that cannot be
  stated, which is why these are axioms.
- **At `V.addrs = eps`**, a stream the axiom adds must carry `□ (watchSrvFacts V -∗ isWGS V G)`.
  - `isWGS V G` holds the real `respc` channel's invariant at `respcE V` (each response a `watchDn` at `V`'s member
    values), allocated when the stream is created.
  - The real `run`, which holds no facts, cannot keep that invariant for a cross-machine member's responses.
  - No Iris-level contradiction makes the wand vacuous: by C, the antecedent and `membersAt` can both hold.
  - So at these `V` the triple is still not provable, and its use is sound by encapsulation (B, C), as before. The
    refactor narrows the encapsulation argument (no reader without facts), but does not remove it.

### E. Other checks

- **`RequestProgress_dist`'s post** (`statusErrOk err`) is unaffected: W2's `ctx.Err()`, and N3's section E for
  the other returns.
- **`watchClientAt`** keeps `clientF cl "Watcher" ↦□ watcherIfaceOf w`. That agrees with `isNewClient`'s
  existential `w`, so the axioms act on the watcher whose lock `isNewClient` describes.
- **Cross-world.** No new entailment from persistent cells to a pure fact. `WEnv.atEps` is a pure function of `V`,
  and `wgsGuard` is a wand under `□`.
- **Deriving `False`.** I found no way. `wgsGuard_elim` needs the facts. `watchSrvFacts (V.atEps eps) ⊢ False` at
  `V.addrs ≠ eps` lets a program prove things only under a premise it cannot have. An axiom-inserted `G` is
  existential in the lock, and a program learns its `isWGS` only with facts, and only on an address where nothing
  answers (C).

## 2. The KV and Txn axioms (3–7) and `Client_Put/Get_dist`

- **Statements.** `V` occurs only in `kvClientAt cl api eps V Γ`, and there only in `isNewClient`'s watcher
  conjunct. The posts read `Γ.kv`, `api` and the reply.
- **Go.** `(*kv).Put/Get/Delete/Compact` and `(*txn).Commit` never touch `c.Watcher` or `w.mu`.
- **Arguments.** N2's arguments use `clientNoProxy`, `membersAt`, `kvObjAt api eps`, `clientKVAt` and `grpcConn`,
  plus `Serve_dist`'s `kvCongr`. None of these changed. None of the arguments reads the watcher conjunct.
- **The C route** (in-process facts and `etcdAddrAt` at one address) does not help a KV attack. `KV_*_dist`'s posts
  are vacuous on an unserved address (the error arm). The in-process unary registrations (`isGrpcRpcsMd`) are no
  more servable there than the stream registration is.
- **Verdict.** Sound, as N2 found. N2's conclusions were not re-derived here, only their independence from this
  change.
- `Client_Put_dist.wp_proof` and `Client_Get_dist.wp_proof` are theorems from `KV_Put_dist`/`KV_Get_dist`, so they
  add no trust.

## 3. Other axioms and trusted models that mention the changed definitions

- `git grep` finds no mention of `isNewClient`, `isClientWatcherCore`, `isClientWatcher`, `watcherMu`, `wgsGuard`,
  `watchClientAt`, `kvClientAt` or `isKvWatcher` in `TrustedCode/` or `GooseLang/`.
- I checked every `Spec/` file that mentions one of them, plus the definitions that wrap them: `clientWatchOk`,
  `isStore`, `clientOk`, `clusterUp`, `leaseClientAt`, `grantedAt`, `memWAt3`, `featuresInit`, the `client_*.law`s
  and the `premises` defs. For each `.spec` I checked whether its `wp_proof` is an `axiom`. The only hits are axioms
  1–7.
  - The other name matches are collisions with other namespaces: `grpc.NewClient`, `bridge.New`.
  - Two metrics axioms mention `isStore` in their docstrings only.
  - The `client_*.law`s are hypotheses discharged by theorems (`*_law_holds`).
- `etcdResolver_grpc` (`InvClientNew.lean:157`) is in a file that mentions `isNewClient`, but its statement does
  not.
- `Client.Close.wp_proof`'s statement mentions none of them (`clientCoreAt`). Its docstring's "`watcher.Close`,
  proved, keeps the watcher's invariant" is still true: a `nil` map satisfies `watcherMu`. See F4.

## Findings and proposed fixes (none applied)

- **F1. `WatchDist.lean`'s header "The `∀ V` form", `Watch_dist`'s "Margin: the watcher's environment", and
  `RequestProgress_dist`'s last paragraph are stale.**
  - They say that a stream must carry `isWGS V G` in the lock, which holds `watchSrvFacts V`.
  - They say the triples are "`False`" at `V.nm = 0`.
  - They say the retiring proof needs a refactor that takes `watchSrvFacts` out of `isWGS`.

  None of these describes the current `watcherMu`. Proposed text for the header:
  > The lock keeps each stream as `wgsGuard` (its invariants under the servers' facts), over `New`'s
  > environment restricted to the dialed endpoints (`V.atEps eps`, `isNewClient`). At a `V` whose members are
  > not exactly `eps` (including `V.nm = 0`) the guard holds outright, so the lock asks nothing of a stream these
  > calls add. At `V.addrs = eps` the guard asks `isWGS V G` under `watchSrvFacts V`, which a cross-machine
  > stream cannot meet (its `respc` invariant is at `V`'s member values), and no law refutes `watchSrvFacts V`
  > from `membersAt eps Γ`. There the use is sound by encapsulation (below), not by truth.

  Also fix `watchClientAt`'s docstring (`WatchClientDist.lean`). It says "the watcher's environment `V` is the one
  `New` was given", but the watcher is now at `V.atEps eps`.
- **F2. The encapsulation premise is false as stated; restate it.** The header says that every spec that locks the
  watcher "takes `isClientWatcher V w`, whose `watchSrvFacts` no cross-machine program has". N3's section B says
  the same, on the ground that `addrUnset` is spent.
  - A program can hold both facts at one address: `Listen`, then the raw `grpc.start` with the `Watch` handler,
    then `addr_set_proto_tok` from `netAddrLeft` to `etcdSvc` (C).
  - What makes the argument hold is that such an address is never served.
    - `grpcServes (etcdSvc Γ mid)` is unprovable with a `Watch` stream registered.
    - An address has one table and one `γ`.
    - `Serve_dist`'s `net.Listen` fails while the program's listener is open (W1).
    - So no stream on such a client gets a response (W2).

  Proposed replacement sentence:
  > Their use is sound because the lock's contents are never observed against a response: `mu` is unexported;
  > every proved spec that locks it reads a stream only with `watchSrvFacts` of the lock's environment
  > (`wgsGuard_elim`); and a program that holds those facts and `membersAt eps Γ` at once has, at every endpoint,
  > a `grpc.start`ed server with a `Watch` registration that nothing can serve (`grpcServes` of the opaque
  > `etcdSvc` with a stream registered, one table per address, `etcdstart.Serve`'s `Listen` failing on the open
  > listener), so its streams get no response.

  Correct N3's section B in the same way. Its verdict does not change.
- **F3. Record what the argument now depends on (the standing trigger, restated).** With `wgsGuard`, "a spec that
  locks without `watchSrvFacts`" can no longer void the argument. These would:
  1. any change to `watcherMu` or `wgsGuard` that yields a stream's `isWGS` without `watchSrvFacts`;
  2. any law about `etcdSvc` at the `Watch` name (route (a)'s `.stream` entry included), or any other way to make
     `grpcServes` provable for a server with a `Watch` registration at an address of `membersAt`. That would let an
     in-process server, at KV names unrelated to `Γ.kv`, answer a watcher that both the axioms and the proved specs
     act on;
  3. a spec that frees or closes a `grpc.start`ed listener (for example a `Stop`; `grpcAddrIs_agree`'s docstring
     already flags S10);
  4. a new axiom that locks `w.mu`.

  Put this list in place of the bold sentence in the header, and in the audit rows. Point 2 must be checked when
  route (a) defines `etcdSvc`: the entry has to bind the handler to `Γ`'s members.
- **F4. `Client.Close.wp_proof`'s docstring (wording only).** "`watcher.Close`, proved, keeps the watcher's
  invariant" argues in-process. For streams that `Watch_dist` added, the claim is about Go, not about the proof.
  Proposed: "… (`watcher.Close` sets the map to `nil`, which `watcherMu` allows at every environment; each stream's
  `close` returns, also for streams the cross-machine watch contracts opened, `notes/axiom-review/n3-watch-dist.md`
  T5, `wenv-isnewclient` W2)".
- **F5. Retirement plan (no change to trust).** The header says that the retiring proof "meets the `∀ V` form only
  after the watcher-environment refactor", and "the statements do not change".
  - After this refactor, the retiring proof can discharge the guard only off `V.addrs = eps`.
  - At `V.addrs = eps` it still needs a law based on serving, or the client-view split (§25.2). By D, nothing in
    today's models gives either.
  - So the claim that the statement survives retirement unchanged is not yet supported. Either state the ∀ V form's
    retirement as open, or plan to restrict the statement, for example to `V.addrs ≠ eps` or `V` built from the
    table. The second changes what the axiom claims, and needs the user's review.

## Attacks tried, in brief

| Attack | Outcome |
|---|---|
| Weaker precondition through `atEps` (more programs reach the axioms) | No: only `New` writes the `Watcher` field; same reachable `(cl, eps, V)` (A) |
| A lock reader without facts extracts `isWGS`/`watchSrvFacts` from an axiom-inserted stream | No: guard needs the facts (B) |
| A proved spec inserts a fake stream at `nm = 0` that a reader with facts trusts | No: facts at `nm = 0` are `False`; a lock at another environment is another invariant |
| Mixing proved specs and axioms on one watcher | Possible in the logic (C), but every endpoint is unservable; W2: no response, no panic |
| `Serve_dist` serving an address the program `grpc.start`ed | Go's second `Listen` fails (W1) |
| `Client.Close` / `RequestProgress` on a mixed watcher | Return; no panic (W2) |
| KV/Txn axioms through the watcher conjunct | Not read by statements, posts, Go or arguments (section 2) |
| Other axioms/trusted models mentioning the definitions | None besides 1–7 (section 3) |

## Not tried

- I did not build the program of section C (both facts at one address) in Lean. I checked only that every step is
  an existing spec or ghost law.
- I did not re-derive N2's KV conclusions (who answers, retries, the error arms) or N3's resumption and error-arm
  measurements. This review checked only that they do not depend on the changed conjunct.
- I did not check whether `sync.isMutex` respects `⊣⊢` of its invariant (A's "unpinning"). The verdict does not
  depend on it.
- I did not attack the address-exclusivity axioms (`grpcAddrIs_agree`, the `netAddrLeft`/`bridge.New` reviews), or
  whether a raw `Close` of a consumed listener could be specified. Point 3 of F3 records the latter as a trigger.
- I built nothing and ran no Lean. I am trusting that the changed proofs check, as the branch claims.
