# authN: the statement of `etcd_authN_safe`, for review before linking (2026-11-15)

Branch `authN`. Plan: `notes/authN-plan.md`; the principals' mapping, the name and `1 ≤ k ≤ 1000` decided by
etcd-grove-81 (`questions.md`). Everything below the closed theorem is proved, kernel included: `Main.wp_proof`,
`run.wp_proof`, `barrier.wp_proof`, `newUserClient.wp_proof` (both copied from auth3), `etcdstart.StartMemberAuth`
and `StartMembersAuth`, over the specs of their callees. No `sorry`, no new axiom, no trusted text. What is left
is the linking (`MainLinked`, `Adequacy`, `Results`, generated `PkgTable`/`Init`, etcdstart's `Link` entries and
API list, the collection, interfaces, bounds, gates), which waits for this statement.

## The program

`examples/etcd/authN`: `Main(k)` starts `k` etcd members in one process with auth on
(`etcdstart.Members("authN", k, 29000, 30000)`: members `authN-0` .. `authN-(k-1)`, peer addresses
`127.0.0.1:29000+i`, client addresses `127.0.0.1:30000+i`; `etcdstart.StartMembersAuth`: auth3's member start,
the simple token provider, TTL 300, the no-snapshot settings, token `authN-1286`), then `run`: every member's gRPC
API served at its client address; authkv's set-up (`auth.SetUp`: users, roles, auth enabled) through member 0;
root's linearizable read at every member (the barrier); the four principals' workloads at once, each through its
member: the client with no token through member `0`, `u` and the client with a token no provider issued through
member `1 mod k`, `v` through member `2 mod k`; then root's last write, its history watch and `CheckHistory`
through member 0, and `u`'s watch check through `u`'s member. `Main` panics if a member let a principal do
what the auth state does not permit. At `k = 3` the members and the mapping are auth3's. The program is
`authN.initialize' #() ;; Main #(W64 k)`.

## The statement (Lean, as it will be in `Results.lean`)

```lean
theorem etcd_authN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (hG := heapAt hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (hG := heapAt hG lctx))
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis (auth3's)
    (hD22 : ∀ hG, ⊢ authSchemaSrv (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (authNProgram k) authNNames)
    (HAs : addrsUnclaimed (authNProgram k) (etcd_authN.authNAddrs k))
    (HDs : dataDirsAbsent (authNProgram k) (etcd_authN.authNDirs k))
    (HEnv : verifyEnvOff (authNProgram k))
    (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_authN.premises (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([authNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

with `authNAddrs k` the `2k` addresses (every member's peer and client address, `authN/Dir.lean`), `authNDirs k`
the `k` data directories `authN-i.etcd`, `authNNames` the read package's two metric names (auth3's), and
`etcd_authN.premises k n ids ps ctxs boot` (`authN/Defs.lean`): for each member, `bootstrap`'s contract at its
name, URLs and id with `AuthToken = "simple"` (`etcdstart.bootPremiseOn`, auth3's `bootPremise` at the token
`authN-1286`), at the directory naming each member's one peer URL (putgetN's `dirN`); `proto.Marshal`'s contract
at the bootstrap log's conf changes; the raft wrapper's contracts (`etcdstart.commonPremises`). The ghost-state
bundle is auth3's (`putgetGF`, the same functors as putgetN's `putgetNGF`).

## In plain words

For every member count `k` from 1 to 1000: run the program from a fresh state with one thread, for any number
`n` of steps (`n + 2 ≤ 2^28`). Then, if the main thread has finished, it returned `Ok`, `Failed` or `WatchEnded`;
no thread is stuck; no thread has panicked. Not panicking means none of authkv's checks failed at any member a
principal uses: after the set-up through member 0 and the barrier at every member, each member refuses every
forbidden request of the principals that use it and replies only with keys the principal may read; root's history
watch through member 0 holds only permitted writes, and `u`'s watch through member `1 mod k` only keys of
`[a, b)`. This holds if:

1. etcd's member ids for the `k` members (`ids`, in member order), the peers in `bootstrap`'s order (`ps`, a
   permutation of `ids`), the peers' contexts and the bootstrap log are what Go computes, and the ids' 16 low bits
   are distinct and not 0 (`BootFacts`, putgetN's; `TestMemberIDs` checks it for every `k ≤ 1000` at the token
   `authN-1286`);
2. the size facts auth3 assumes: auth records fit, the backend is under quota, gRPC replies fit, the disk behaves;
3. at start nothing else claims the program's metric names, its `2k` addresses or its `k` data directories, and
   `ETCD_VERIFY` is off;
4. the trust-boundary contracts per member (`premises`), the context and client error classes (`Hctx`, `Hcec`),
   auth3's D22 (`hD22`, the auth store's backend: trusted text as a named hypothesis), and the class instances,
   all as auth3's.

## Compared with `etcd_auth3_safe` and `etcd_putgetN_safe`

| | `etcd_auth3_safe` (678 axioms) | `etcd_putgetN_safe` (640) | `etcd_authN_safe` |
|---|---|---|---|
| members | 3 | `k`, `1 ≤ k ≤ 1000` | `k`, `1 ≤ k ≤ 1000` |
| ids | `id₁ id₂ id₃`, putget3's `BootFacts` | `ids`, `Hlen`, putgetN's `BootFacts` | putgetN's (`ids`, `Hlen`, `BootFacts`) |
| start | auth on, simple tokens (`startMember`) | auth off (`StartMembers`) | auth on, simple tokens (`StartMembersAuth`, auth3's start per member) |
| served | every member | member 0 | every member |
| workload | authkv: set-up at 1, barrier at 1, 2, 3; anon at 1, u and bad at 2, v at 3 | one Put, one Get | authkv: set-up at 0, barrier at every member; anon at 0, u and bad at `1 mod k`, v at `2 mod k` |
| `premises` | three `bootPremise`s (auth on) | `bootPremise` per member (auth off) | `bootPremiseOn` per member (auth3's, auth on) |
| `hD22` | yes | no | yes (auth3's) |
| addresses | 6 | `k + 1` | `2k` |
| result | `0`, `1` or `2`, no stuck thread, no panic | `#()`, ... | auth3's |

**New premises: none.** Every premise is auth3's, with putgetN's generalization of the three members to a list:
`1 ≤ k ≤ 1000` and `ids.length = k` (putgetN's), `BootFacts` over a list (putgetN's), `premises` over the
members' list (each member's `bootPremiseOn` is auth3's `bootPremise`), and the address and directory lists
generated from `k`. The transport's directory bound for up to 1000 members (`rafthttp.bootCfg`) is discharged at
linking by `rafthttp.bootCfg_of_le`, as putgetN's. The axioms are expected to be auth3's (to be confirmed by the
collection `etc/tcb-collections/authN.txt` at linking).

**What the result does not say** (auth3's list, adapted): liveness; `Failed` and `WatchEnded` skip the checks after
them; each principal uses one member (members `3..k-1` are served and pass the barrier, but no principal's requests
go to them, and at `k ≤ 2` several principals share a member); the barrier is the driver's; no snapshot is taken
(the no-snapshot settings); a token is used only at the member that issued it; no member fails, restarts or is
partitioned.

## Decisions for the reviewer

1. Approve the statement above (the name and the mapping are etcd-grove-81's decisions).
2. Forms decided by the agent (questions.md): `barrier`/`newUserClient` specs and proofs copied from auth3 (the Go
   functions are copies); `run.spec` over lists (the servers' slice, the members' slice with their ghost names, each
   member's `memberUpOn` behind the thread token as `StartMembersAuth` returns it, every member's names the
   cluster's as member 0's); auth3's `serve_member` copied into `authN/run.lean`.
