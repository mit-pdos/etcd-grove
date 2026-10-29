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
