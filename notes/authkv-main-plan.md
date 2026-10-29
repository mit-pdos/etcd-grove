# Plan: authkv's `Main`, as a skeleton of frozen statements (spec-first)

Status (2026-10-29): **Scope and Draft.** Started at the user's request ("work on 4": make authkv's
closed theorem the fixed target, so the rest can be proved in parallel). Runs beside the auth-mode
merge (`notes/auth-mode-merge-plan.md`, session `etcd-grove-72`, worktree `etcd-grove-abd`), which
owns `etcdserver/` and `client/v3`'s auth-on stack. This stage touches only
`examples/authkv/` and this file, except where a row below says "server interface". Those rows are
stated here as the interface authkv needs; the merge session changes the server.

## The target

`authkv.Main.wp_proof` is the one `sorry` of `etc/tcb-collections/authkv.txt`. `Main.spec` is the
closed theorem (`Spec/.../examples/authkv/Main.lean`): `Main()` does not panic and returns 0, 1 or
2. The goal of this stage is a `Main.wp_proof` that is a real proof over **named stubs**, each a
statement with its own `sorry`. Each stub is reviewed and frozen, and each can then be proved on its
own worktree by its own agent. The closed theorem then rests on exactly the stubs' `sorry`s, and
`--per-root` shows what is left.

What was left before this stage (`notes/decisions.md`, "E3zb of the auth plan", "What is left",
items 2-5; `notes/c1-plan.md`, A4-A5) is the same work. This stage only fixes its interfaces first.

## Main, step by step, and what each step takes

| Step of `Main` | Callee spec | Today |
|---|---|---|
| `startServer` | `startServer.spec` (from `memberBootOn`, gives `memberUpOn … γa`) | proved |
| allocation with auth on | `server_member_alloc_on` (`etcdserver/Results.lean`) | proved |
| `common.Serve` | `Serve.specOn` (gives `grpcUpOn`) | proved |
| `common.NewClient` (no user name) | `NewClient.spec` | proved, auth off: **S5** |
| `SetUp(cli)` | `SetUp.spec`, over `kvRegsAt` | proved over the plain registrations: **S5** |
| the set-up's admin `Q`s | the Auth service's registration in `grpcUpOn` | **S6** |
| `newUserClient` (root, u, v) | none | **S3** |
| `Work(c, who)` ×4, goroutines, wait group | none | **S2** |
| root's `Put("z/end")` | `client_put_on` (and the `*Client` wrapper) | the wrapper: E3zc's "Not yet" |
| root's watch from revision 1, `Collect` | `watcher.Watch.spec` with auth on, `common.Collect.spec` | **S4** |
| `CheckHistory(evs, setupRev, "z/end")` | `CheckHistory.spec` (proved) and **the history invariant** | **S1** |
| `u`'s watch of `[a, b)`, its check | as watchkv's (its events are in its range) | **S4** (the watch only) |

## The stubs (to draft, review, freeze)

- **S1. The history invariant** (`Proof/.../authkv/Hist.lean`). An invariant over the KV state
  (`etcdKV ρ.rd.kv σ`): every write after `setupRev` is to a key `k` with
  `permittedK (writerK k) k`, or is root's `z/end`. Laws:
  - `akHist_alloc`: allocated after `SetUp` returns, from the state's half.
  - `akWriteAu who k`: the update each principal's write hands the client. It keeps the invariant
    **when it fires**. This needs the server interface D below.
  - `akHist_events`: the events of a watch from revision 1, read up to `z/end`'s revision, meet
    `CheckHistory`'s premise.
- **S2. `Work.spec`** (`Spec/.../authkv/Work.lean`). For a principal `who`:
  - the client `c`'s `KV` and `Watcher` over a connection `conn` to the member, with the `On`
    registrations;
  - the principal's token fact: `userClientAt conn γa who` for `u`/`v`; for `anon`/`bad`, the
    no-user client, whose attempts carry the context's outgoing metadata (C2/C4,
    `deliversOutgoing`);
  - the auth state fixed: every state from the set-up's published index `n` on is `setupSt _`
    (`akAuthFixed`, from S6);
  - the history invariant's write updates for `who`'s keys (S1).

  Post: `True` (no panic). The proof is the workload's: each reply's auth fact (`writeGrantOn`,
  `rangeAuthed`, `txnAuthOn`) at the token of an attempt, which `userClientAt` or `badCtx_unbound`
  pins to `who`, then `granted_setupSt_iff`/`granted_rev0`/`not_coversRange_*`.
- **S3. `newUserClient.spec`** (`Spec/.../authkv/newUserClient.lean`). `clientv3.New` with a user
  name: `isNewClient` plus `clientTokAt … (tokIssued γa · who)`, so `clientTokAt_user` gives
  `userClientAt`. Needs `Authenticate` served with auth on (C1's A4-A5, in progress elsewhere).
  The stub states it over the member's `Authenticate` registration as a premise.
- **S4. Watch with auth on** (E3zb's item 3). A client-level statement: an event on a watch of a
  principal means the watch's creation passed `isWatchPermitted` for that principal's token at a
  state no older than `n`. `Work`'s refused watch (`c/` prefix) then reports nothing. `u`'s watch
  needs only the plain watch facts. Stated as one stub at the `watcher.Watch` level.
- **S5. The no-user client and `SetUp` at the `On` registrations.** `SetUp.spec` takes
  `kvRegsAt`, which an auth-on member does not give (E3zc). Restate it at the `On` registrations,
  or derive `kvRegsAt` for `SetUp`'s puts only (a `Put`'s `On` spec weakens to the plain one,
  `isGrpcRpcMd_mono`, and `SetUp` only puts). The second changes no spec. Preferred.
- **S6. The set-up's history** (E2b's server-side item). After `SetUp` returns `true`, the auth
  history is `setupSt rev` at every later position. No later request is an admin one, and the
  only admin client is the set-up's. Also `setupAuthOk`'s `Q`s from `grpcUpOn`'s Auth
  registration.

## D. The server interface the history needs (open; for the merge session and the user)

`kv_prop_au_on` fires a client's update only when the committed auth state grants the request.
But the update (`kvOpAu1 γk op Q`) is not told so, so it must keep S1's invariant even for a
write that will never be granted (`v`'s `c/v/0`). It cannot. E3zb's item 4 found this:
"the update then needs the grant at the commit to refute an ungranted write".

Proposed (smallest change): the update in `reqPropOkOn` takes, as its premise, the fact the reply
already carries, `writeGrantOn s E ρ tok irr`, at the request's attempt token.
That is, `kvOpAuG ρ tok op Q := writeGrantOn … tok … -∗ kvOpAu1 ρ.rd.kv op Q`. The
client's `*_on` calls thread it through `attemptPre` as they thread the reply's grant. With it:
- `v`'s, `anon`'s and `bad`'s write updates are vacuous (their token has no principal, or one the
  state refuses);
- `u`'s fire only inside `[a, b)`, on its own keys;
- root's one write is `z/end`.

Each keeps S1. The alternative is a server-exported history fact (every applied write granted to
its header's user) plus a ghost record of which connection sent which write. That is bigger and
duplicates what the update already carries.

**What exists at the commit** (the merge session, 2026-10-29, from `kv_prop_au_on`,
`ReqOn.lean`, `ServerKVOn.lean`). Inside the update, at the committed log `L`, the server has
`grantedAt γk st₀ (withHeader rq hm) L` (pure; it fires the update only then). The header's
binding to the token (`hdrBoundT s E.authMode tok hm`) is known before the proposal, from the
request path's `hdrBoundM`. `pubAfterM` exists only after the apply, so `writeGrantOn` itself does
not. The premise is therefore `⌜grantedAt … L⌝ ∗ hdrBoundT … tok hm`, given **inside the update's
commit step** (`L` is bound there), not as a wand around `kvOpAu1`. That is a new `On`-only form
of the update (`kvAu1`'s shape, `InvRequest.lean`), and S1 must use a premise stated in `L`'s
terms (`kvRaftOfOn`'s auth state), not authkv's model. Placement: it touches the statements of the
merge's step 5 (`processInternalRaftRequestOnce`, `raftRequest`, `doSerialize`, `reqPropOkOn`), so
it lands after step 5, or folded into step 5 if the user approves. **Decided (the user, 2026-10-29): folded into step 5**, on the merge session's branch `auth-req`; that session sends the exact statement after its review, before proving it, so S1 can be checked against it. Until then S1/S2 are drafted
against a local `kvOpAuG` in `examples/authkv`.

**This is a change to the server's `On` request spec (`reqPropOkOn`) in the middle of the merge.
That is an escalation trigger (`notes/spec-first-plan.md`, "Who decides").** It goes to the user,
and the merge session owns where it lands.

## Who decides (this stage)

- Decided by the agent: the stubs' file names and their exact statements up to review; S5's
  derivation (no spec change); the order of the stubs.
- For the user: D; any change to `Main.spec`'s premises (a top-level statement). The draft adds
  none so far. Premises S3/S4/S6 may need, if their proofs cannot discharge them, also go to the
  user.

## Steps

1. Draft S1-S6 as Lean statements with `sorry`, and `Main.wp_proof` over them. Compile; `Link.lean`
   regenerated (`etc/gen-link.py --authkv`), so the collection lists the stubs' `sorry`s.
2. A fresh `spec-reviewer` on S1-S6 and the glue (the `spec` skill's principles), the Go code and
   the callers given. Repair; review again.
3. Freeze. Then the stubs are independent, one worktree each. S2 and S1 depend only on D's
   answer. S3 waits on C1's A4-A5, S4 on the watch's auth facts.

## D's candidate, checked against S1 (2026-10-29)

The merge session's candidate (step 5, part B): `kvAu1G γk f G Q`, the update's atomic
postcondition `etcdKV γk (f σ) ∗ G σ`, with `G = writeGrantAt s E ρ ctx rq hm σ :=
hdrBoundM true s E ctx hm ∗ ∃ L, srvRLogLb ρ.raft L ∗ ⌜grantedAt … (withHeader rq hm) L ∧
kvStOn … L = σ⌝` (at the token level, `hdrBoundT`). Checked against S1:
- **The principal: enough.** `hdrBoundT`, C1 (`userClientAt`), `auth.tokIssued_agree` and
  `badCtx_unbound` give the header's user `who` or `""`. Asked: a way to refute `hdrBoundT`'s
  `srvTLSId s` disjunct for a member started without TLS.
- **The position of `L`: a gap.** S6 gives `srvRLogLb ρ.raft Lset`, with `Lset` ending in
  `AuthEnable`'s entry. S1 needs `Lset <+: L`. Two lower bounds are only comparable
  (`srvRLogLb_prefix`), and `L ⊊ Lset` (auth still disabled, so everything granted) cannot be
  refuted. Asked (preferred): `G` also says that `L ++ [e]` is the committed log at the commit, with
  `e` the request's entry (`∀ L₀, srvRLogLb ρ.raft L₀ -∗ ⌜L₀ <+: L ++ [e]⌝`). Then `Lset <+: L`,
  since `e` is a KV write. The alternative is a caller-given lower bound in the precondition, as
  reads have.

**Taken (with the merge session, 2026-10-29).** The persistent `∀ L₀` form is false: later lower
bounds grow past `L ++ [e]`. Instead the lower bound travels with the update. `reqPropOkOn`'s write
case is `∃ L₀, srvRLogLb ρ.raft L₀ ∗ kvAu1G … (writeGrantAt … L₀) Q`, and `G σ` gives
`srvRLogLb ρ.raft (L ++ [e])` with `e` the request's entry (a KV write), `L₀ <+: L ++ [e]`,
`grantedAt … L` and `kvStOn … L = σ`. Gated as a whole on `E.authOn`. authkv's write updates are
built at `L₀ := Lset` (S6), so `Work.spec` takes `srvRLogLb ρ.raft Lset`. Other clients use
`L₀ := []` (`srvRLogLb_nil`).

**Also needed (S2; owned by the merge's step 4).** Refuting `hdrBoundT`'s `srvTLSId s` disjunct
needs `ClientCertAuthEnabled ↦□ false` (`srvTLSId_false`, the merge session's). The value is
hidden after `NewServer` (`isServerReqM`'s `∃ v`, so `memberUpOn`). Proposed: `srvServeCfg s cfg`
also gives `srvCfgFieldAddr s "ClientCertAuthEnabled" ↦□ cfg.ClientCertAuthEnabled'`; authkv's
configuration leaves the field `false`.

**Candidate 3 (after the merge session's review, 2026-10-29).** The lower bound is a fragment of
the server's requested log (`srvReqLogLb ρ.raft L₀`; `srvReqLogLb_of_rlogLb` converts a committed
one). `writeGrantAt s E ρ ctx rq₀ L₀ σ := ∃ hm L, hdrBoundM true s E ctx hm ∗ ⌜L₀ <+: L ∧
grantedAt … (withHeader rq₀ hm) L ∧ kvStOn … L = σ⌝`, with `L` the log before the entry. Laws:
`srvAuthAtLog`, `grantedAt_iff`, `kvGranted_emptyUser`. Threaded through `Txn` too. S6 gives
`Lset` in the requested-log view. authkv's `cfgOk` gains `ClientCertAuthEnabled' = false`.

## D2. Nothing stops an admin request after `SetUp` (open; S6)

S6 ("every log extending `Lset` has the auth state `setupSt _`") must rule out an admin entry
committed after `Lset`. No admin spec takes a caller resource over the auth history: E2h's
`setupAuthOk` lets the server's side choose the `Q`s, and the history's authority (`authOwn`'s half,
the lock's half) is the server's. So nothing on the client side tells the proof that no admin call
happens after `SetUp`. The options:
- (A, preferred) the admin specs take a caller update over a client-side view of the auth history
  (as KV writes take `kvOpAu1` over `etcdKV`). `Main` holds the view, and only `SetUp`'s calls
  give updates.
- (B) per-request attribution, as for writes: a grant for admin requests, root's token only on
  root's connection, and that connection sending no admin request.

(A) changes the admin `On` specs, so it is for the user and the merge session. **Decided (the
user, 2026-10-29): (A).** The merge session places it (step 5 or 6) and sends the statement before
proving it. S6 needs from it: a client-side view of the auth history that the update fires on;
`SetUp`'s `Q`s from the fired updates, so that `Main` holds the view at the eight steps' result;
and the view's last state equal to `srvAuthAtLog … L` for every requested log `L ⊇ Lset`.

**D2's shape (the merge session's stage "5b", after step 5; 2026-10-29).** `kvInvOn` keeps half of a
mono-list of the model's auth states along the log's admin entries. The client's view
`authHistView γ hs` is the other half, exported at the start (`memberUpOn`). An admin request's
update is an AU over the view; it fires at the admin entry's commit (`kv_prop_au_on`'s admin
branch) and appends `adminNext`'s state. `writeGrantAt` gains a fragment of the history up to `L`.
Asked so S6 can close the ordering: (1) the fragment is a pure function of the log (`admStates L`,
its last state `srvAuthAtLog … L`), monotone in `L`; (2) the admin update's commit gives
`srvReqLogLb ρ.raft (L ++ [e])` with `admStates (L ++ [e])` the view's new history. Then `Lset`
(after `AuthEnable`) has `admStates Lset = hs_set`, and every write's `L ⊇ Lset` reads `setupSt`.

## Draft, round 1 (2026-10-29)

On the branch (`d9e2f09fbf`), all compiling (`Proof...authkv.Results` builds):
- **S1** `Hist.lean`: `stateHistOk`/`opHistOk`, the invariant `akHistInv`, the stand-in `kvAu1G`, and
  four stubs (`stateHistOk_step`, `akHist_alloc`, `akHist_writeAu`, `akHist_readAu`).
- **S2** `Spec/.../authkv/Work.lean` (`Work.spec`), with its vocabulary `WorkEnv.lean`
  (`akPrincipal`, `akKVOn`, `akAuthFixed`, S6's predicate over today's names). Proof: a stub.
- **S3** `newUserClient.spec`. Proof: a stub.
- **S5 done (no stub).** `SetUp.spec` takes the member's `Put` registered with auth on and the
  client's `*kv` over its connection (`clientTokAt`) in place of `kvRegsAt`, which an auth-on member
  does not give (its `Delete`/`Txn` specs add shape premises). It is still proved, through
  `client_Put_on` (`ClientOn.lean`, the `*Client` wrapper of `client_put_on`, kept in authkv until
  the client package has the auth-on wrappers). Decided by the agent: `SetUp`'s only caller is
  `Main`, and the spec was restated, not duplicated.
- `Main.wp_proof` takes its callees (`SetUp`, `newUserClient`, `Work`, `Principals`, `CheckHistory`,
  `LastIn`), linked (`etc/link-lean-first-authkv.txt`, `Link.lean` regenerated). Its body is still
  `sorry`. The glue (watchkv's `Main` is 537 lines) is written against the real callers after the
  freeze, when step 5/5b's statements exist.

**Gaps found while drafting (for the user, batched with the review):**
- **G1. The no-user client's token.** `Work` needs `clientTokAt` (the `*kv`'s connection and
  `attemptTokOk` at `False`) for `anon`/`bad`. `common.NewClient.spec` gives only `isNewClient`,
  although `clientv3.New.spec` gives `clientTokAt` (`clientAuthPre_anon`). Adding it to
  `NewClient`/`NewClients`' post is a change to a frozen, shared spec (15 files use it).
  **Decided (the user, 2026-10-29): yes.** Both posts gain `clientTokAt cl addrs (fun _ => False)`
  (`clientv3.New` at `P := False`, `clientAuthPre_anon`). Callers: one more `-` in their
  `icases` (six `Main`s, `linkv3p/startCluster`).
- **G2. The watches (S4).** `watcher.Watch.spec` covers prefix watches of a non-empty key, and
  `watchAddrFacts` needs a non-empty prefix. `u`'s watch is a range `[a, b)`, root's a watch of
  every key (`""` with `WithPrefix`), and `Work`'s refused watch needs the auth outcome (no event
  for a refused principal). One generalized `watcher.Watch.spec` (range, whole keyspace, auth on)
  is the client package's spec, owned by the merge session's area, and a change to a frozen spec.
  **Decided (the user, 2026-10-29): the merge session owns it.** It sends the statement before
  proving it; S1's read update (`akHist_readAu`) fixes what its events must come from.

## Review, round 1 (2026-10-29)

An independent `spec-reviewer` read the skeleton (S2, S3, S5, S1's laws, WorkEnv, ClientOn): not
freezable yet; no bug in the Go code. Its findings and what was done:

**Repaired (this commit).**
- F-H1/F-H2: `akHist_writeAu` took a closed entailment `∀ σ, G σ ⊢ ⌜opHistOk op⌝`, unusable (the
  refutation of a grant needs Iris facts the caller holds), and fixed `Q := True`. Now
  `akHistInv ∗ □ (∀ σ, G σ -∗ |={mask \ akHistN}=> ⌜opHistOk op⌝ ∗ Q σ) ⊢ □ kvAu1G … G Q`: a
  refused write takes `Q := False`, and its reply (`putReplied … Q`) then cannot exist, so the
  reply's own grant is no longer needed.
- F-W1: reads' verdicts come from the auth states at indices at least the published bound they
  are given, which `akAuthFixed` (raft logs) did not speak of. `akAuthFixed γa ρ Lset n` now also
  has `authPubLb γa n` and every `authStateAt γa m st` with `n ≤ m` at `setupSt _` (S6 supplies it).
- F-W2: `Work.spec` takes `□ (srvTLSId s -∗ False)` (from `ClientCertAuthEnabled ↦□ false`; the
  merge's step 4 exports the field), so the statement does not change when step 4 lands.
- F-W5: `Work.spec` takes `clientTokAt cl [addr] (akTokP γa who)`, what `Main` holds from
  `newUserClient`/`NewClient` (G1), instead of its unfolded parts; `akPrincipal` is gone.
- Minor: `akKVOn` without `γr`; `Work.wp_proof` takes its callees (keyOf, reqCtx, refused,
  checkKVs, checkTxnReads, Permitted); `newUserClient` without `name ≠ ""`, `pw ≠ ""` (F-N1) and
  with `clientv3.New.spec`, so `authkv_Main` takes `DialWithBalancerBody` as every client-building
  `Main` does.

**Open, waiting on the merge session.**
- F-E1: `akAuthFixed`'s write part is over `srvRLogLb ρ.raft L`, which step 5's grant
  (`opGrantT … L₀`: `L₀ <+: L`, with the lower bound `srvReqLogLb ρ.raft L₀`, not one of `L`) does
  not give. Restate over 5b's client view of the auth history once it is stated.
- F-W3 (G2): the watch has no auth fact, so `Work`'s refused watch of `c/` from revision 1 is not
  excluded from reporting the set-up's puts; and the token fact is about the KV object's
  connection, while `isNewClient`'s watcher is on a separately existential one. G2's watch spec
  must take the watcher's connection's tokens, or `isNewClient` say the connections are one.
- F-C1: `client_Put_on` (ClientOn.lean) is a second spec of `(*Client).Put`, beside
  `client_Put_any`. A temporary local, not frozen: the merge replaces it by the one
  `(*Client).Put` spec in `client/v3`.

**Decided by the user (2026-10-29).**
- F-S2: `SetUp`'s puts take persistent updates (`□ kvOpAu1`, "may be delivered several times"). A
  late firing of `c/<who>/d` above `setupRev` would put a key the history does not admit into
  root's watch, so the invariant can be allocated neither after `SetUp` (the updates keep needing
  the state) nor before. In Go it cannot happen: a refused attempt did not apply, and a put is
  resent only after a refusal; the interfaces lose this (`writeOnce` needs `noRefusalAt`, and
  `etcd_noRefusal` requires auth off). A gap in the proof interfaces, not in the Go code.
  **Decision: a refusal fact in the client's write results** (an attempt answered with a refusal
  did not fire its update; refusals only at an auth state with `enabled`), so a set-up put's
  update fires at most once and `SetUp` takes a non-persistent one. The merge session adds it to
  step 5's client write results and drafts it here before proving it. Then F-S1: `SetUp.spec`'s
  post gives the last put's revision and the client's `etcdKV` back at it.
- F-W4: `anon`'s and `bad`'s tokens need `reqCtx`'s timeout context to have no outgoing metadata.
  Perennial already says its descriptor has no values (`bgDeadlineDesc`); the gap was this
  repository's grpc model, whose `outgoingOf` is opaque. **Done:**
  `context.WithTimeoutBackground.spec` gives `cd.Values = ∅` (proved from Perennial's),
  `client.wp_WithTimeout_bg` passes it on, `reqCtx.spec` gives `outgoingOf c0 = none`, from a new
  trust-boundary axiom on the grpc model, `metadata.outgoingOf_noValues`
  (`Proof/google_golang_org/grpc/metadata/OutgoingNoValues.lean`: a context with no values has no
  outgoing metadata). No Perennial change needed. The `axiom` skill reviews it before the freeze;
  `etc/tcb-report.py --check --update` before merging.
- `authkv_Main` takes `DialWithBalancerBody`, as every client-building `Main` does: kept.

**Not yet drafted** (`Main.wp_proof`'s other callees): `startServer`, `Serve`, root's `Put`, the
wait group, the watches (G2, for `Work`, root's whole keyspace and `u`'s range), a `Collect.spec`
general in its per-event predicate (F-H3: today's demands each event be a put at `2+n+j` of a
plan's key; root's history has a DELETE), `akHist_events` (an event of `σ.revEvents r` has
`modRev = r`, so `stateHistOk` gives `histOk` of the collected events), S4, and S6's
`akAuthFixed_alloc`. F-S1: `SetUp.spec`'s post says nothing of `rev`; restated with F-S2's answer
(the last put's revision, and the client's `etcdKV` back at it).
