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
  First attempt: a law over the grpc model, "a context with no values has no outgoing metadata"
  (`metadata.outgoingOf_noValues`). The `axiom` skill refuted it: Perennial's `isContext` does not
  constrain `Values`, so it was inconsistent with `AppendToOutgoingContext`'s axiom (a Go program
  that panics, proved not to: `notes/axiom-review/outgoingOf-noValues.md`, branch
  `axiom/outgoingOf-noValues`). **The user's choice: tie the fact to the call.**
  `context.WithTimeoutBackground.spec` gives `metadata.outgoingOf (ok ctx') = none`; its
  `wp_proof` is a trust-boundary axiom again (proved from Perennial's spec until now); the general
  fix is in `notes/perennial-changes.md` ("a descriptor's `Values` constrain nothing").
  `client.wp_WithTimeout_bg` passes the fact on, and `reqCtx.spec` gives `outgoingOf c0 = none`.
- F-S2's part 1, `etcd_noOtherRefusal` (the merge session's, route B): approved by the user.
- `authkv_Main` takes `DialWithBalancerBody`, as every client-building `Main` does: kept.

**Not yet drafted** (`Main.wp_proof`'s other callees): `startServer`, `Serve`, root's `Put`, the
wait group, the watches (G2, for `Work`, root's whole keyspace and `u`'s range), a `Collect.spec`
general in its per-event predicate (F-H3: today's demands each event be a put at `2+n+j` of a
plan's key; root's history has a DELETE), `akHist_events` (an event of `σ.revEvents r` has
`modRev = r`, so `stateHistOk` gives `histOk` of the collected events), S4, and S6's
`akAuthFixed_alloc`. F-S1: `SetUp.spec`'s post says nothing of `rev`; restated with F-S2's answer
(the last put's revision, and the client's `etcdKV` back at it).

## Main's callees, draft (2026-10-29)

`Main.wp_proof`'s hypotheses once frozen, in `Main`'s order (`examples/authkv/authkv.go:365`):

| Call | Spec | State |
|---|---|---|
| `zap.NewNop` | `zap.NewNop.spec` | exists |
| `startServer` | `startServer.spec` (gives `common.memberUpOn … γa`) | exists, proved |
| `common.Serve` | `common.Serve.specOn` (from `memberUpOn`'s parts; its `grpcUpOn` step gives `akKVOn` through `etcd_kv_auth_served_onA`, with the Auth registrations and `Authenticate`'s `authTokReg`) | exists; the merge folds it into `Serve.spec` |
| `common.NewClient` | `common.NewClient.spec` (G1: `clientTokAt … False`) | exists |
| `SetUp` | S5 | restated after the refusal fact (F-S1, F-S2) |
| `newUserClient` ×3 | S3 | drafted |
| `Principals`, `Work` ×4, `sync.WaitGroup` | `Principals.spec`, S2, Perennial's | S2 waits on 5b and G2 |
| `context.WithTimeout`, `ErrAny` | `context.WithTimeoutBackground.spec` (now with no values), `context.ErrAny.spec` | exist |
| `root.Put(z/end)` | `client_Put_on` (local wrapper, not frozen: F-C1) at a non-persistent update once the refusal fact lands | exists |
| `context.WithCancel` | `context.WithCancelBackground.spec` | exists |
| `root.Watcher.Watch("", WithPrefix, WithRev(1))`, `ucli.Watcher.Watch(lo, WithRange(hi), WithRev(1))` | G2's `watcher.Watch.spec` (the merge session's); `WithPrefix.spec`, `WithRange.spec`, `WithRev.spec` | G2 pending |
| `common.Collect` ×2 | `draft.Collect_spec` (`Drafts.lean`): general in a per-event fact `F`. Root's: `F i e := ⌜sint.Z setupRev < sint.Z e.Rev' → keyHistOk e.Key'⌝`, from the watch's events at states `akHist_readAu` fires at. u's: `F i e := ⌜permittedK u e.Key'⌝`, from G2's no events refused to u | drafted; restating `common.Collect.spec` changes a spec of `common` (watchkv, linkv3p use it, through the corollary at their plan): the user's call |
| `CheckHistory` | `CheckHistory.spec`, its premise `histOk` from root's `F` by `draft.histOk_of_keyHistOk` (proved) | exists |
| `LastIn`, `Permitted` | `LastIn.spec`, `Permitted.spec` | exist |

Laws `Main` needs besides: `akHist_alloc` (S1, once `SetUp` gives back the client's `etcdKV` at
`setupRev`), S6's `akAuthFixed_alloc` (from `SetUp`'s admin results and 5b's frozen view; drafted
when 5b is), and the watch's events in `σ.revEvents r` at their `ModRevision` (part of G2's spec:
the events a watch reports are the state's, `watchStateRespOk`).

## Step 5 landed on `auth-req` (2026-10-29; not yet in `lean`)

The merge session's step 5 (`auth-req`, `8054714322`) gives what S1/S2 were drafted against:
`kvAu1G … (writeGrantG ρ.kv srvAuthSt0 Gb (irrPut op) L₀) Q` with `srvReqLogLb ρ.raft L₀` in the
auth-on write permits (`putPermitOn`, `deletePermitM`), one spec per server function at
`E.authOn`, and the laws `grantedAt_iff`, `kvGranted_emptyUser`, `srvTLSId_false` (from
`ClientCertAuthEnabled ↦□ false`: the source of `Work.spec`'s `□ (srvTLSId s -∗ False)`). Once it
is in `lean` and this branch is rebased: `Hist.lean`'s stand-in `kvAu1G` goes (the real one, same
shape and mask, `InvRequest.lean`), and `akHist_writeAu` is at its `G`. 5b brings the rest
(`authHistView` in the boot results, `srvAuthSt0_disabled`, `etcd_noOtherRefusal`, 2a).

## Review, round 2 (2026-10-29)

On `lean` with step 5. Round 1's F-W1, F-W2, F-W4, F-W5, F-H1, F-H2, F-E2, F-E3, F-N1 addressed;
F-W3 (G2), F-E1 (5b), F-H4/F-S1/F-S2 (5b's route B), F-C1 (temporary) open as briefed. New:

1. **Step 5's grant stopped at v3rpc**: the auth-on client registrations and write results
   (`etcdPutSpecOn`, `client_put_on`, ...) were still over plain `kvOpAu1` (`ServedOn.lean`
   dropped the grant at `L₀ := []`), so nothing took `akHist_writeAu`'s update. The merge session
   fixes it as "5a" (branch `auth-5b`): the results take `srvReqLogLb ρ.raft L₀ ∗ □ kvAu1G …
   (fun σ => ∃ md, ⌜clientAttemptMd conn ci md⌝ ∗ opGrantT … (mdTokenOf md) op L₀ σ) Q`.
2. **`Collect.spec` kept watchkv's cursor `Cur`** ("event n at revision 1+n"), unmeetable for u's
   range watch. **Done:** the relation is the caller's (`I`, from `I 0 0`); `wp_Collect_plan` at
   `Cur`, authkv at `True`.
3. What 5b must give `akAuthFixed`: a monotone `admStates` (last `srvAuthAtLog`), a persistent
   frozen view (`authHistFreeze`), and a law from the store's history (`authStateAt`) to it: all in
   5b's design (the merge session, 2026-10-29). The view comes from the cluster allocation.
4. The TLS-off export (`ClientCertAuthEnabled ↦□ false`): 5b, in the boot results.
5. **Done:** `Work.wp_proof` also takes `WithTimeoutBackground`, `ErrAny`,
   `AppendToOutgoingContext` (its watch's context).
6. **Done:** `akAuthAt` gone, `srvAuthAtLog ρ.kv srvAuthSt0` in its place.
7. **Done:** `draft.revEvents_modRev` (proved, from mvcc's `evsOfRevM_modRev_sm`). `setupRev`'s
   sign comes from F-S1's `SetUp` post.
8. Open, small: `ctxErrClientAll` is reached only by unfolding `ctxErrClientAllW` (a law of
   `client/v3` to add); the closed theorem's thread bound must cover `Main`'s four goroutines;
   `authkv_Main`'s callees join at the freeze (`Main.lean`'s header).
9. Not taken: `reqCtx.spec`'s `c0` could go (its post is `outgoingOf c = if bad then mdAdd none
   "token" badToken else none`); sound as is.
10. **Done:** stale docstrings (`WorkEnv`, `Main`).

5b's client admin specs retry each attempt (`□ ▷`), so SetUp's admin updates get through only by
F-S2's no-refusal route (the view all disabled): F-S2's part 2 comes before 5b's client side.

## 5b, checked against authkv (2026-10-29)

The merge session's 5b candidate 2 (client history view `authHistView`, frozen `authHistFrozen`,
the admin update `histAu`, `writeGrantG` with `authHistLb (admStates L)`) gives `Work`'s write
refutation: from `Lset <+: L`, monotone `admStates` and the frozen `hs_set`, `admStates L = hs_set`,
so the grant is at `setupSt r`. `akAuthFixed`'s write half becomes `authHistFrozen ρ.kv hs ∗
srvReqLogLb ρ.raft Lset ∗ ⌜admStates Lset = hs ∧ ∃ r, srvAuthAtLog Lset = setupSt r⌝`. Asked and
taken for candidate 3: `∃ r` in `SetUp`'s post; `histAu`'s post with `srvReqLogLb (L ++ [e])`.
Open, a design item of 5b's: the read side needs the store's history indices to follow the log's
prefix order (an index at or after `SetUp`'s published `n` at a log extending `Lset`); the merge
session plans an invariant tying the store's recorded states to `admStates` along the applied log.

5b candidate 3 (the merge session's, going to the user after its review round 3) settles the auth
side of `SetUp.spec`: pre `authHistView ρ.kv [srvAuthSt0]`; post `∃ γz hs Lset r k,
authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗ ⌜admStates Lset = hs ∧ srvAuthAtLog Lset =
setupSt r⌝ ∗ authPubLb γa k ∗ authStateAt γa k (setupSt r)` (`k` from `AuthEnable`'s reply,
published after its commit); the freeze cell is allocated inside `SetUp`, after the puts (which
use route B's view branch). The read side's law (§5, the store's history along the applied log)
is stated with 5b and proved later: authkv's dependency. authkv adds `SetUp`'s KV side (F-S1).

5b approved by the user (candidate 4, 2026-10-29; the merge session implements it on `auth-5b`).
The read side's server fact (`authHistTie E ρ`, the store's history along the applied log) is
deferred; its law's statement is fixed (`authStateAt_setup`: tie ∗ frozen `hs` ∗ `setupHist hs` ∗
`authStateAt γa m st` ∗ `hs.length ≤ m` ={E'}=∗ `st = last hs`), and authkv keeps the read fact as
a premise (no `sorry`, no axiom; where exactly: asked). Round 3 of 5b's review (H7) for authkv:
`akAuthFixed`'s write half over requested logs (`srvReqLogLb`); `SetUp`'s proof chooses the `Q`s
over the metadata-indexed admin specs; the cell's token a `dghostVar` half held by `SetUp`'s
invariant; `setupPrefixR` says only the last set-up state is enabled (`k = |hs_set|`); per-kind
laws (`AuthEnable`'s successor `{st with enabled := true}`, no bump; `UserAdd`/`RoleAdd` need
`n ≠ []`); `AuthEnable`'s reply selects the recorded disjunct (`admRec_of_done_authEnable`).
Where the read premise sits (the user's words: "authkv keeps the read fact as a premise until the
invariant is built; no sorry or axiom"): a law-shaped hypothesis of `Main.wp_proof` (the tie's
law), `Main.spec` unchanged. Undischarged, `Link.lean`'s `wp_Main` passes it on, so the exported
`authkv_Main` takes it too: a change to the top-level statement the user sees. At the restatement,
show the user `authkv_Main`'s exported form with it before committing.

The user approved 5b's `SetUp.spec` draft (the merge session's, on `auth-5b`): its auth half, and
`clientTokAt` naming the client's `Auth` field over the KV connection. The Watcher's connection
stays out of 5b: tying it to the same connection (F-W3) is its own statement change, proposed as
part of G2 after the merge. `clientTokAt_user`'s conclusion is unchanged.

## After 5b merged (2026-10-29)

`lean` merged into `authkv-main-skel` (SetUp, ClientOn: lean's, the merge session's). The timeout
context's metadata: first folded into `context.WithTimeoutBackground.spec` (one spec per function),
then undone (the user's, 2026-10-29) once the cost showed: on `lean` `WithTimeoutBackground.wp_proof`
is proved, and the fold made it an axiom under ten other collections. So the split stays: the
proved base for everyone, the axiom `context.WithTimeoutBackgroundMd` for authkv's `SetUp` and
`reqCtx` only (F-W4's in-place conjunct not taken). `Work`'s own watch context (`authkv.go:268`) takes the Md
axiom too: G2's refutation needs its outgoing metadata to be none (G2 review round 2, R6; no new
axiom, it is already in authkv's collection).
`akAuthFixed`'s write half restated over `SetUp`'s post (`srvReqLogLb ρ.raft Lset`, `authHistFrozen`
at `admStates Lset`, last state `setupSt r`), with the law `akAuthFixed_write` (proved: a grant's
`authHistLb (admStates L)` at `Lset <+: L` is at `setupSt`).

The read half is blocked on the read tie (the merge session, etcd-grove-72): the plan's
`setupHist` is `setupFrozenOk` (`SetupInv.lean`), which `SetUp`'s post does not export (it could
gain `⌜setupFrozenOk hs⌝`, a `SetUp.spec` change for the user). `authHistTie` is not defined, and no
stub: one nothing gives is useless to `Main`, one the boot gives is a new axiom (the user's call),
and a law over today's server views may be unprovable (`authkv_Main` vacuous). The fix is H5, the
tie as a server invariant (a third share of `γa.hist` through the auth store's admin and lock
specs and the apply thread's admin step), exported from the on start: design work, which the
merge session is raising with the user. Until then `Main.wp_proof` gets no read hypothesis.
The user chose to build H5 (the merge session's report, 2026-10-29): `authHistTie` a proved server
invariant exported from the auth-on start, no axiom; the merge session drafts it (the invariant,
its export, `authStateAt_setup` proved over it) for the user before any proof, on a branch off
`lean` after `etcd_noOtherRefusal`. `setupHist` reads `setupFrozenOk`. `Main`'s read side waits
for the tie's statement.
H5 candidate 3 approved by the user (the merge session implements it on `h5-tie`). Its read law:
`authStateAt_setup (hγa) (hE : ↑kvN ∪ ↑authHistN ∪ ↑authTieN ∪ ↑(nroot.@"authRev") ⊆ E')`:
`srvRaftLogInv ρ.raft ∗ kvInvOn ρ.raft ρ.kv srvAuthSt0 ∗ authHistTie E ρ ∗ authHistFrozen ρ.kv γz hs
∗ authStateAt γa k (hs.getLastD srvAuthSt0) ∗ ⌜k ≤ m⌝ ∗ authStateAt γa m st ={E'}=∗ ⌜st =
hs.getLastD srvAuthSt0⌝`. No `setupFrozenOk` (the server's `admStates_nodup` puts `last hs` at one
index), so `SetUp.spec` does not change. `Main` has the first two from `memberBootOn` (persistent),
the tie from `Start.specOn`'s post, the rest from `SetUp`'s (`admStates_getLastD` turns
`srvAuthAtLog Lset = setupSt r` into `hs.getLastD _ = setupSt r`). `akAuthFixed`'s read half then
becomes a fancy update at such an `E'`.

## G2, the watch with auth on (2026-10-29)

Drafted by this session (the user's request; the merge session has no draft and H5 does not touch
the watch path). The user chose the full design (A): keep `Work`'s refused watch. Candidate 1
(scratch, not committed): a watch's check as its responses report it, `v3rpc.watchAuthed s E n tok
o` (`rangeAuthed` without the read's floor), through four layers: a metadata-indexed stream
registration (grpc), the server's watch stream at the client's published bound (v3rpc; server-side
statements proposed to the merge session, not edited here), one restated `watcher.Watch.spec` (any
range; each response with events carries `watchAuthed`; the `Watcher` on the client's KV
connection, F-W3), and `Work`'s refutation. Spec-first: review rounds (at most three), the user's
approval of each changed trusted statement, the statements in code over named stubs, then the
freeze; no proof before it. Estimated as large as `Work`'s proof or larger.

Rounds 1 and 2 (2026-10-29) found seven first-tier problems each; round 2's included a false
trusted change (`NewStream`'s delivered metadata is `clientAttemptMd`'s, with `withVersion` inside,
not `grpcAttemptMd` at the caller's context) and a bug in this repository's trust base
(`streamKeyFromCtx`'s axiom claims a return at a nil context: `notes/audit.md`). The user's
choices (2026-10-30): strengthen the stream axioms **in place** under their names (`NewStream`,
`serveStream`, `streamKeyFromCtx`; one proof of `Watch`, so no split is possible; the collections
resting on each are listed in the candidate and go into the audit rows); the stream context's
metadata through the existing local axiom `context.WithCancelValCtx` (its post gains `outgoingOf
ctx' = outgoingOf inctx`), with the general fix (a `Value` contract for `WithCancel`) proposed to
Perennial; `streamKeyFromCtx` takes `context.isContext`. Candidate 3 went to round 3, the last
with first-tier findings allowed.

Round 3 (2026-10-30) left two first-tier findings, both repaired with the user's approval: the
server's stream-interceptor contract keeps the run's context (grpc-prometheus's interceptor axiom
strengthened with it), and `dialOk` requires an etcd stream interceptor. The user then approved
the whole trusted table (candidate 4, `notes/g2-watch-auth.md`). Next: the statements in code
over named stubs (client, grpc and context here; v3rpc and auth proposed to the merge session),
the `axiom` skill on each strengthened axiom, then the freeze.

## Round 3 and the freeze (2026-10-30, branch `authkv-r3`)

**F-S1, the user's choice: the checker tolerates a repeated set-up write.** `SetUp`'s puts take
persistent updates (the client may resend a refused put), and with F-S2 part 2 parked nothing
excludes such an update firing after `SetUp` returns. `CheckHistory` skips a set-up put
(`SetupWrite`: `x/<who>/d`, the value `setup`), so the history invariant (`Hist.lean`: `evHistOk`,
`stateHistOk`, `akHistInv`) is over the whole log, allocated at the boot state before `SetUp`
(`akHist_alloc` proved, `stateHistOk_boot`), and the set-up's updates come from it
(`akHist_setupAu`, over the `akHist_writeAu` stub). `setupRev` was then dead (every event at or
below it a set-up write) and is gone, the user's choice: `CheckHistory(evs, endKey)` checks every
event, `SetUp` returns `bool`. The invariant's set-up case checks key and value only; that such an
event is a put comes from the watch's reachable log (`revEvents_setupPut_put`, over `kvLogOkTo`).
The trade-off is in `notes/decisions.md` ("authkv's checker admits a repeated set-up write").

**The read half (H5).** `akAuthFixed`'s read row is an update at any mask containing the server's
`authTieReadMask` (`AuthTieRead.lean`), built by `akAuthFixed_alloc` from `SetUp`'s post and the
read view (`isServerReadM_tie`, `ReadOn.lean`): both proved, no premise added to `Main.wp_proof`.

**Round 3's review** (spec reviewer): both changes sound; first-tier F1, `Work.spec` not tied to the
member's watcher (G2's F-W3), fixed (`Work.spec`'s premise on `V`: address, one member, the server
and environment, the KV names); F2-F6 fixed (`Main`'s pure laws drafted and proved:
`opHistOk_putKey`/`_endPut`, `stateHistOk_boot`, `revEvents_setupPut_put`; the comment no longer
claims Go can apply a set-up put late; `authTieReadMask`; stale text). G2's `Watch` of `""` reports
from `"\x00"` (the user's, 2026-10-30, on `g2-freeze`): every authkv key is non-empty, no change.

**Frozen (2026-10-30).** The statements: `Main.spec` (unchanged), `SetUp.spec`, `Work.spec`,
`newUserClient.spec`, `CheckHistory.spec`, `SetupWrite.spec`, `Hist.lean`'s invariant and laws,
`WorkEnv.lean`'s `akAuthFixed`. Stubs left, each provable on its own: `akHist_writeAu`,
`akHist_readAu`, `Work.wp_proof`, `newUserClient.wp_proof` (needs C1's A4-A5), `Main.wp_proof`
(over the others and G2's frozen `watcher.Watch.spec`). Still open, not statements: F-C1 (`ClientOn`'s
second `Put` spec, temporary), round 2's item 8 (`ctxErrClientAll`'s law, the thread bound).


## Proving the stubs (2026-10-30, branch `authkv-hist`)

Proved: `akHist_writeAu`, `akHist_readAu`, `newUserClient.wp_proof`. `Work.wp_proof`, in layers:

1. **The principal of an attempt** (`WorkAuth.lean`): from `clientTokAt cl [addr] (akTokP γa who)`'s
   `attemptTokOk`, `reqCtx`'s context facts (no outgoing token; `bad`'s `badtoken`) and the TLS
   refutation, a header or auth info bound to an attempt's token (`hdrBoundT`, `infoBoundT`) has the
   user `""` or, for `u`/`v`, `who`.
2. **Refusals at `setupSt`**: a write's grant (`clientGrant` at `Lset`, through `akAuthFixed_write`)
   or a read's check (`rangeAuthed`, `txnAuthOn`, `watchCheckOk`, through `akAuthFixed`'s read row)
   for such a principal covers only keys `permittedK who`; the write's update is
   `akHist_writeAu` with `Q` the permission (so a refused write's reply cannot exist).
3. **The `*Client` methods with auth on** (`ClientOn.lean`): `Get`, `Delete`, `Txn`'s builder, a
   `Put` told its grant (F-C1's second `Put` spec), the `Watcher` field.
4. **`Work` itself**, one call at a time.

Progress (2026-10-30): `WorkCalls.lean` holds the per-call lemmas: `akWriteAu`, `work_put`,
`work_delete`, `work_get` (with `srvRangeOk_keys`), `work_commit`, and the pure facts of the
three ranges. **The nested transaction (T4)** is outside client/v3's proved specs: `txn.Then`
needs every op's `txnOpOf` (an `OpTxn` has none), and `client_txn_on` needs `TxnModel.plain`. The
user chose to extend client/v3's specs to nested transactions; that is handed to the G2 session
(etcd-grove-83). Until it lands, Work's T4 call is a named `sorry`.

**`Work` proved** (2026-10-30), over the per-call lemmas, but for T4: `then_commit_nested_refused`
(`sorry`; a triple of `Then` with the nested op whose post is the refused `Commit`, so that it does
not depend on how client/v3 will model a nested op: today's `reqOpAt` of one is `False`). Next:
`Main`.

## Main: what blocks it (2026-10-30)

Proved: `ak_alloc` (`MainAlloc.lean`): `memberBootOn`, the client's `etcdKV` at an admitted boot
state (for `akHist_alloc`) and `authHistView … [srvAuthSt0]` (for `SetUp`), from the mode-`on`
cluster and member allocations. The serve step (`wk_served`'s analog) needs four facts nothing gives:

1. **`watchAddrFacts V` with auth on** (first-tier). Its `srvKVFacts` is `srvKVInvs`, the auth-off
   KV invariant (`kvInv`), and the watch client's proofs fire the read update through it
   (`watch_fire`, `raw_to_state`, `WatchFire.lean`; `WatchRun.lean`). An auth-on member has
   `srvKVInvsOn` only, so `Work.spec`'s premise and `Main`'s two watches cannot be met. **Fixed**
   (G2's follow-up, on `lean` `8a4cba9dc6`): `srvKVFacts V = ∃ on γr, srvKVCoreM on V.R.E γr ∗ …`
   (`client/v3/InvWatch.lean`), from `memberUpOn`'s `isServerReadM true` by `srvKVCoreM_of_readM`
   (`etcdserver/ReadOn.lean`), `srvKVFacts_intro`; `watchAddrFacts`' `srvLogsSmall` by
   `srvLogsSmall_of_receipts` (`ServerWatcher.lean`, any mode). Left: assembling `watchAddrFacts`
   from `grpcUpOn` (the watch half of the serve step).
2. **`Authenticate`'s registration** in `grpcUpOn`: `v3rpc.authRegs` holds the five admin methods,
   not `Authenticate` (C1's A5, "Q9"); `etcd_kv_auth_served_onA` takes it as `hreg`.
3. **The auth store's `BcryptCost()`** (`bcryptCostOk`, a premise of `etcd_kv_auth_served_on(A)`):
   no spec of `authStore.BcryptCost`, `NewAuthStore`'s post and `memberUpOn` do not export it.
4. **`ClientCertAuthEnabled = false`** (`SetUp`'s and `Work`'s `□ (srvTLSId s -∗ False)`, by
   `srvTLSId_false`): `memberUpOn` has the field at an unknown value (`watchSrvOk`'s `cca`), not
   the config's `false`.

3 and 4 are an export from `NewServer` through `startServer`'s post (`memberUpOn`).

**Done (2026-10-30): 3 and 4** (`notes/decisions.md`, "The started member exports its auth store's
cost field and its TLS fallback off"): `memberUpOn` gives `srvBcryptField s` and
`□ (srvTLSId s -∗ False)`. **2** is left to C1's A5: `etcd_kv_auth_served_onA` dropped `hreg`
(it is a `sorry` meanwhile). The serve step's KV and Auth half is proved over them
(`ak_served_kv`, `MainServe.lean`: `akKVOn`, `setupAuthServed`, `Authenticate`); its watch half
waits on 1.

**`Main.wp_proof` up to `SetUp` (2026-10-30)**: the logger, `ak_alloc` and `akHist_alloc`,
`startServer`, `Serve.specOn` with `ak_served_kv`, `NewClient`, `SetUp` (its puts by
`akHist_setupAu`), every error's `Failed`; a `sorry` from `SetUp`'s success on. Linking: the
callees `zap.NewNop`, `startServer` (pending in `Link.lean`, `?`: `Results.lean`'s `authkv_Main`
passes `authkv_startServer`, so it takes its premises `auth.ValidSpec`, `authSchemaSrv` and the
semantics' `Float64ToInt64Semantics`, `ErrorStringLeaf`; the user's choice), `Serve.specOn`
(`=common.wp_ServeOn`, `common/LinkOn.lean`), `NewClient`, `authStore.BcryptCost`. `startServer.spec`
takes `bootstrap`'s contract at authkv's `cfgOk`/`urlsOk` (Main's premise; was `common.bootPremise`,
whose `common.cfgOk` leaves out the simple token provider, so Main could not meet it; the user's
choice). `ak_alloc` also gives `ρ.rd.kv.c0 = 0` (`SetUp`'s `c0 ≤ ai0`).
