# F7 S5 review: `leaseCheckD` (`P = some info.Username'`) and `authFloorD`'s new conjunct (2026-11-26)

This review used the `axiom` skill and was read-only. I read `/shared/etcd-grove-f7` at `e8aba773a5` through
`git show`/`git diff aaa769c60f e8aba773a5`, and wrote nothing there. The Go source is the etcd pin `df6af0c36a`
(`.lake/go-src/etcd`, copied to `/shared/tmp/coord-03/f7-s5-gotest/etcd`), run with go1.27.3.

## Verdicts

| target | verdict |
|---|---|
| 1. `leaseCheckD`'s binding `P = some info.Username'`, which reaches `Lease_{Grant,Revoke,TimeToLive,Leases}On_dist` | **The binding is right, but the axioms are UNSOUND because of `outTokOk`.** Go refuses an anonymous or bad-token call before the lessor changes (test below, all three members). But `outTokOk` constrains only the `token` metadata key. etcd's server also accepts the key `authorization` (`TokenFieldNameSwagger`, optionally with a `Bearer ` prefix). So an anonymous client (`P = none`, `outTokOk` satisfied) that sends root's token under `authorization` gets a **success** from all four lease calls as root, while auth stays enabled. The post then forces `enabledVerdictFrom … false`, which is false. Go test: confirmed. Lean proof: not attempted (see 1.3). |
| 1'. The same gap in `KV_GetOn_dist`, `Txn_CommitOn_dist` and every other F7 contract that takes `outTokOk` (13 spec files) | **UNSOUND, same counterexample, and more direct.** `readCheckedD`, `txnReadCheckedD`, `writeCheckedD` and `adminRepliedD` each state `userOk P <server-side user>`. For `P = none` and server-side user `root` that is `False`, so the success arm is contradictory outright, with no auth-history reasoning needed. Go: an anonymous `Put` and a linearizable `Get` with `authorization: <root token>` succeed on every member (test below). |
| 2. `authFloorD`'s new conjunct | **TRUE of etcd. As written it is not derivable from `authHistTie`: CONDITIONAL, one fix.** The content holds: each state recorded at a position `j ≥ i` is the state after a committed prefix `L' ⊒ L₀` of the one requested log. The alignment worry is closed by revision monotonicity (2.1). The flaw is the form. The conjunct is a plain persistent wand that hands out `srvReqLogLb γR L'` for states recorded later. That fragment exists only inside the `authTieN` invariant, so it can only be obtained under a fancy update. The in-process analogue, `akAuthFixed` (`examples/etcd/auth/WorkEnv.lean:87`), has exactly that update: `={E'}=∗` with `authTieReadMask ⊆ E'`. |

## 1. `leaseCheckD`, and the Go test

### 1.1 The test: `/shared/tmp/coord-03/f7-s5-gotest/etcd/tests/integration/f7s5_lease_auth_test.go`

**Setup:** a 3-member integration cluster (`integration.NewCluster`, `Size: 3`) with simple tokens; root and `alice`
(role `r`, read-write on `[a,b)`); auth enabled. Root grants lease `l1`. For each member `i`:

- **Anonymous** (`clientv3.Config{Endpoints: member i}`, no user): Grant, Revoke(`l1`), TimeToLive(`l1`),
  TimeToLive(`l1`, `WithAttachedKeys`) and Leases.
- **Bad token:** the same five calls with `metadata.AppendToOutgoingContext(ctx, "token", "badtoken")`.
- **Lessor unchanged:** afterwards, root's `Leases` count is unchanged and `l1`'s TTL is still positive.
- **`alice`:** Grant, TimeToLive and Revoke of her own lease, and Leases.
- **Attack:** an anonymous client gets root's token with `Authenticate("root","123")` and sends it under
  `authorization`, both as is and with a `Bearer ` prefix. Its outgoing `token` values are `[]`, so `outTokOk none`
  holds by its first disjunct. It then calls Grant, TimeToLive(keys), Leases, Revoke, Put and a linearizable Get.

**Output** (full log: `/shared/tmp/coord-03/f7-s5-gotest/test-output.txt`; `--- PASS: TestF7S5LeaseAuth (38.56s)`). On
each of members 0, 1 and 2:

```
member i anonymous Grant|Revoke|TimeToLive|TimeToLive(keys)|Leases: etcdserver: user name is empty   (ErrUserEmpty)
member i badtoken  Grant|Revoke|TimeToLive|TimeToLive(keys)|Leases: etcdserver: invalid auth token   (ErrInvalidAuthToken)
member i: leases before 1 after 1; l1 TTL 587/574/561
member i alice Grant/TimeToLive/Revoke/Leases: <nil>
member i attack: outgoing token values [] (outTokOk: none)
member i ANONYMOUS client (P = none) Grant with authorization="pSqzyzJGGMmFiXJd.21": err=<nil>
member i   ... TimeToLive(keys): <nil>
member i   ... Leases (admin-only for others' leases): err=<nil> n=2
member i   ... Revoke: <nil>
member i ANONYMOUS client Put: <nil>; linearizable Get: err=<nil> kvs=1
(the same with authorization="Bearer <token>")
```

**The two answers to question (1):**
- **Anonymous and bad-token calls:** confirmed. Every lease call, keys or not, is refused with
  `ErrUserEmpty` or `ErrInvalidAuthToken`, at a leader and at followers, before the lessor changes. In Go:
  - `requireAuthInfo` (`v3_server.go:1278`) runs before `raftRequest` (Grant `:448`, Revoke `:478`) and before
    `leaseTimeToLive` (`:700`).
  - `LeaseLeases` reads `s.lessor.Leases()` first (`:739`), but only reads it, and discards the result on refusal
    (`checkLeaseLeases`).
  - `LeaseGrant` draws `reqIDGen.Next()` before the check. That is the id generator, not the lessor.
- **The binding `P = some info.Username'` for `P = some u`:** also right, so the change from `userOk` is correct.
  - The client's per-RPC credentials send `token: <u's token>`, and `AuthInfoFromCtx` (`store.go:1081-1087`) reads
    `md["token"]` first, so u's token wins. The test's `alice Leases` with `authorization=<root token>` passed as
    alice.
  - Simple tokens are assigned to the same user on every member.
  - TLS identity is excluded by Serve's `□ (srvTLSId s -∗ False)`, and JWT by `NewServer_dist`'s
    `AuthToken = "simple"`.

### 1.2 The gap: `outTokOk` sees one of the two keys

`authStore.AuthInfoFromCtx` (`server/auth/store.go:1072`):

```go
ts, ok := md[rpctypes.TokenFieldNameGRPC]        // "token"
if !ok { ts, ok = md[rpctypes.TokenFieldNameSwagger] }   // "authorization"
...
token := strings.TrimPrefix(ts[0], "Bearer ")
```

`outTokOk P om := mdVals om "token" = [] ∨ (P = none ∧ ∀ t ∈ mdVals om "token", ¬ tokShape t)` (`AuthViewDist.lean:97`).
It says nothing about `authorization`, although the server model knows that key (`auth/InvAuth.lean:731-742`,
`authStore__AuthInfoFromCtx.lean:198`). The in-process contracts are not affected: they bind through the token the
server actually found (`principalBound T E.authMode tok`). The dist drafts replaced that binding with `outTokOk`, and
the second key was lost. This is new: no earlier `f7-*` review mentions `authorization`.

**Consequences:**
- **`P = none`, root's token under `authorization`:**
  - In Go, every auth-on call succeeds as root.
  - The lease posts leave only the disjunct `enabledVerdictFrom (.on (Γ.au mid)) n false`, which is false while
    auth is enabled.
  - `readCheckedD`/`txnReadCheckedD`/`writeCheckedD`/`adminRepliedD` give `userOk none "root"`, which is `False`.
- **`P = some u`, with a client whose own token is empty:** the same thing happens. `getToken` leaves the token `""`
  when `New` ran with auth disabled (`client.go:297-305`), and `perRPCCredential` then sends no `token` key
  (`credentials.go:73`). The server then reads `authorization` as another user, and `P = some u` is false. The client
  refreshes on `ErrUserEmpty`, but here there is no error.

### 1.3 Counterexample program (shape; Lean not done)

```go
cli := clientv3.New(Config{Endpoints: eps})            // anonymous: principalOf cfg = none
ctx := metadata.AppendToOutgoingContext(context.Background(), "authorization", tok)
if _, err := cli.Get(ctx, "k"); err == nil { panic("anonymous read admitted") }  // or Put / Lease.Grant
```

- **The panic:** with auth enabled and `tok` a live root token, Go panics. The test above shows the underlying
  successes.
- **The proof:** by `KV_GetOn_dist`, `om` passes `outTokOk none`, and the success arm's `readCheckedD` contains
  `⌜userOk none info.Username'⌝`. With `info.Username' = "root"` that refutes the arm, so the `if` is unreachable in
  the logic. A caveat: the post does not pin `info.Username'` to root. The logic only has `userOk none u`, i.e.
  `u = ""`, which is consistent. So for KV the Lean contradiction needs auth known enabled at `L` together with the
  user being non-empty.
- **The cleanest Lean route is the lease or write arm:**
  - `writeCheckedD`: `userOk none hm.username ∧ grantedAt … L`. `grantedAt` with auth enabled and an empty user is
    false (`ErrUserEmpty` at apply).
  - `leaseCheckD`: `enabledVerdictFrom … false` against a frozen auth-on history, as in `akAuthFixed`.
- **Why the Lean proof was not written:**
  - The brief allows no writes outside `/shared/tmp`, and a Lean proof needs a Goose project in the repository.
  - The program must obtain `tok` through a specified call: `Auth.Authenticate` has no dist contract among the F7
    fourteen. Either specify it, or read the token from the environment.

### 1.4 Fix

Make `outTokOk` cover both keys the server reads, and compare the trimmed value:

```lean
def outTokOk (P : Option GoString) (om : GrpcMd) : Prop :=
  (metadata.mdVals om go!"token" = [] ∧ metadata.mdVals om go!"authorization" = []) ∨
    (P = none ∧ ∀ k ∈ [go!"token", go!"authorization"], ∀ t ∈ metadata.mdVals om k,
       ¬ auth.tokShape (strings.trimPrefix t go!"Bearer "))
```

- **Existing users:** `SetUpDist.lean:86` (`Or.inl rfl` at `om = none`) and `outTokOk_reqMd`
  (`AuthLeaseDefs.lean:40`, which sets only `token`) should still discharge it. Check that `mdVals none k = []` for
  both keys.
- **Docstrings:** "the caller adds no issued token of its own" (`AuthViewDist.lean:49`) should name both keys.
- **Shared fix:** the fix covers all 13 contracts that take `outTokOk`, so it is a correction to the F7 batch as a
  whole, not to S5.
- **Issue filing:** the dual-key behaviour is documented etcd behaviour (the gRPC gateway's `Authorization`
  header), not an etcd bug. No `issues/` entry is needed. This repository's bug goes in `notes/`.

## 2. `authFloorD`'s new conjunct

> `□ ∀ j st, ⌜i ≤ j⌝ -∗ authStateAt (Γ.au mid) j st -∗ ∃ L', ⌜L₀ <+: L' ∧ st = srvAuthAtLog Γ.kv srvAuthSt0 L'⌝ ∗ srvReqLogLb γR L'`

### 2.1 It is true of etcd: the R1 argument, with the alignment closed

**What the invariant gives.** `authHistTie` (`KVApplyOn.lean:363`) says `inv authTieN (∃ A, srvRLogLb γr.raft A ∗
capAuth γa (bootState :: admStates kv st₀ A))`, and `authOwn_capped` (`InvAuth.lean:1337`) says the member's history
is a prefix of the cap. So position `j ≥ 1` holds `admStates A` at position `j-1`: the state after the `(j-1)`-th
recorded admin entry of a committed `A`, i.e. `srvAuthAtLog` of the prefix of `A` through that entry.

**Alignment (review A's caveat): closed.** Cap states are pairwise distinct:
- `bootState` has revision 0 and `srvAuthSt0 = bump bootState` has revision 1.
- `admEntry` requires `adminNext rq st ≠ st`.
- Every `.next` outcome in `auth/Steps.lean` is `bump …`, and `.same`/`.err` keep the state.

So revisions strictly increase along the cap. Hence `authStateAt i (srvAuthAtLog L)` fixes `i = |admStates L|` (the
cap index of `L`'s last recorded admin entry; never 0, since `srvAuthAtLog L` has revision ≥ 1). Every `j > i` is an
admin entry after the end of `L`. For it, `L'` is the prefix of `A` through that entry, which extends `L ⊒ L₀`
(`A` and `L` are lower bounds of one authority, so they are comparable). For `j = i`, take `L' := L`.

**Without distinctness, R1 as stated in `f7-getOn-n1.md` would be false.** A history A→B→A would let `i` be the
first A while `j` is B, a state no extension of `L₀` reaches. It holds only because revisions are bumped. Record
this lemma (strict revision monotonicity of the cap) in R1.

**Attacks:**
- **Lagging follower:** the conjunct is about member `mid`'s own recorded states, which come from its applied prefix
  of the one committed log (raft safety, the tie `γR.raft.log = Γ.kv.rlog`). Lag only delays positions; it never
  records a state outside the cap. A floor taken at `mid` says nothing about another member. The lease contracts
  read `Γ.au mid` of their own member, and injectivity of `Γ.au` stops the floor of `mid` being used at `mid'`.
- **Restarted member:** excluded. `NewServer.specG_dist` needs a fresh WAL, and `authNamesFreshD (Γ.au mid)` is
  exclusive, so a second server cannot reach `memberUpOnL` at the same names (`f7-rerev-a.md`, `f7-getOn-n1.md` §2).
- **Leader change:** no effect on the claim. `L'` is a prefix of the committed log, which leader changes do not
  rewrite. The deposed-leader issues concern the lease reply (`TTL`), not this conjunct.
- **Snapshots** (allowed outside `clusterNoSnap`): a follower that installs a snapshot jumps its auth store several
  revisions. In Go the recorded state is still the state after a committed prefix (the snapshot index) at or after
  the floor, so the claim stays true. Its derivability rests on the proved `authHistTie` holding on the snapshot
  path. I did not re-audit whether that path is proved or sits under an axiom or `sorry`.
- **Mid-apply view** (`commitRevision` before `refreshRangePermCache`, `store.go:577-578`): concerns the verdict,
  not the recorded states. Unchanged from `f7-getOn-n1.md`.
- **Requested log vs raft log:** the cap's `A` is a raft-log lower bound (`srvRLogLb`), while the conjunct gives
  `srvReqLogLb γR`. The conversion is `srvReqLogLb_of_rlogLb`/`kvRaftOfOn_eqv`, already named in R1. The prefix of
  `A` must be taken in the same indexing as the requested log. Proof work, not a soundness issue.

### 2.2 Not derivable as written: the missing update

`authStateAt j st` is `monoListIdxOwn γa.hist j st ∗ ⌜permKeysOk st⌝` and carries no log fragment. For a `j`
recorded after the floor, `srvReqLogLb γR L'` (a fragment of the requested-log authority) is not owned at floor
time. It can only be produced later, by opening `authTieN` to read the then-committed `A`, and opening an invariant
needs `|={E}=>`.

A plain persistent wand that yields it therefore holds in no resource the server can give, so the axiom's post
says more than the member can guarantee in the logic. A Go program cannot exploit this, because the fragment really
is obtainable at every reachable point. It is still a false Iris claim, of the kind that should not enter the
trust base. It is also the shape the in-process code already avoids: `akAuthFixed` states
`□ (∀ E' m st, ⌜authTieReadMask ⊆ E' ∧ n ≤ m⌝ -∗ authStateAt γa m st ={E'}=∗ …)`.

**Fix** (no change of meaning for a client at `⊤`):

```lean
□ (∀ (E' : CoPset) (j : Nat) (st : auth.AuthState), ⌜authTieReadMask ⊆ E' ∧ i ≤ j⌝ -∗
    auth.authStateAt (Γ.au mid) j st ={E'}=∗
    ∃ L' : List EntryModel, ⌜L₀ <+: L' ∧ st = srvAuthAtLog Γ.kv srvAuthSt0 L'⌝ ∗ srvReqLogLb γR L')
```

Use whatever mask names `authTieN`, matching `akAuthFixed`.

### 2.3 Reach: `KV_GetOn_dist` and `Txn_CommitOn_dist`

Both receive `authFloorD` only inside their success arms (`readCheckedD`, `txnReadCheckedD`), so 2.2's fix carries
over unchanged. Apart from it, the new conjunct adds no claim Go breaks. Both are still unsound through
`outTokOk` (1'), independently of S5.

## Not tried / left

- No Lean counterexample (no repository writes allowed; it also needs an `Authenticate` contract). The Go side is
  confirmed.
- Not re-audited: whether the snapshot path's `authHistTie` is proved; the other F7 contracts beyond their shared
  `outTokOk` premise.
