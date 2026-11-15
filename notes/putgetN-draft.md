# putgetN: the statement of `etcd_putgetN_safe`, for review before linking (2026-11-15)

Branch `putgetN`. Plan: `notes/clusterN-scope.md`; decisions Q1-Q6 approved by the user, 2026-11-15, via
etcd-grove-81. Everything below `Main(k)` is proved (no `sorry`, no new axiom); what is left is the linking
(`MainLinked`, `Adequacy`, `Results`, generated `PkgTable`/`Init`), which this statement waits for.

## The program

`examples/etcd/putgetN`: `Main(k)` starts `k` etcd members in one process (`etcdstart.Members` names them
`putgetN-0` .. `putgetN-(k-1)`, peer addresses `127.0.0.1:24000+i`, client addresses `127.0.0.1:25000+i`;
`etcdstart.StartMembers` starts them in order, each serving its raft handler on its peer address), serves
member 0's gRPC API on `127.0.0.1:25000`, connects a client to it, puts `k = v`, gets `k`, and panics unless the
Get returned `v`. The program is `putgetN.initialize' #() ;; Main #(W64 k)`.

## The statement (Lean, as it will be in `Results.lean`)

```lean
theorem etcd_putgetN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (hG := heapAtN hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (hG := heapAtN hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (putgetNProgram k) putgetNNames)
    (HAs : addrsUnclaimed (putgetNProgram k) (putgetNAddrs k))
    (HDs : dataDirsAbsent (putgetNProgram k) (putgetNDirs k))
    (HEnv : verifyEnvOff (putgetNProgram k))
    (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_putgetN.premises (hG := heapAtN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

with `putgetNAddrs k` the `k` peer addresses and member 0's client address, `putgetNDirs k` the `k` data
directories `putgetN-i.etcd`, `putgetNNames` the read package's two metric names (putget3's).

## In plain words

For every member count `k` from 1 to 1000: run the program from a fresh state with one thread, for any number
`n` of steps (`n + 2 ≤ 2^28`). Then, if the main thread has finished, it returned normally (the Get returned the
Put's value); no thread is stuck; no thread has panicked. This holds if:

1. etcd's member ids for the `k` members (`ids`, in member order), the peers in `bootstrap`'s order (`ps`, a
   permutation of `ids`), the peers' contexts and the bootstrap log are what Go computes, and the ids' 16 low bits
   are distinct and not 0 (`BootFacts`);
2. the size facts putget3 assumes: auth records fit, the backend is under quota, gRPC replies fit, the disk
   behaves (`authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit`, `diskOk`);
3. at start nothing else claims the program's metric names, its `k + 1` addresses or its `k` data directories,
   and `ETCD_VERIFY` is off;
4. the trust-boundary contracts hold at every ghost-state instance (`premises`): for each member, `bootstrap`'s
   contract at its configuration (name `putgetN-i`, data directory `putgetN-i.etcd`, token `putgetN-1405`, a new
   cluster, raft's clock 100 ms and 10 ticks) and its URLs (its one peer URL, its one client URL, the initial
   cluster's map whose keys are the `k` names, each name's URLs its member's peer URL); `proto.Marshal`'s contract
   at the bootstrap log's conf changes; the raft wrapper's three contracts.

## Compared with `etcd_putget3_safe`

The same theorem with `k` in place of 3. Every premise is putget3's, generalized; none is of a new kind.

| putget3 | putgetN | change |
|---|---|---|
| `id₁ id₂ id₃` | `ids`, `ids.length = k` | a list |
| `BootFacts id₁ id₂ id₃ ps ctxs boot` (`BootCore ∧ ps.Perm [id₁, id₂, id₃]`) | `BootFacts ids ps ctxs boot` (`BootCore ∧ ps.Perm ids`) | same content over a list |
| — | `1 ≤ k ≤ 1000` | **new**: the member count, bounded (Q3) |
| `premises N id₁ id₂ id₃ ps ctxs boot`: putget3's `bootPremise` ×3, `urlsOk` (the map is a 3-insertion, `initURLs3`) | `premises k N ids ps ctxs boot`: `etcdstart.bootPremise` for each member (`[∗list] m; id ∈ members k; ids`), `urlsN` (the map's keys are the `k` names, `iuOf`) | same contract, a list; the map described by its keys instead of its insertion order |
| token `putget3` | token `putgetN-1405` | the token is chosen (below) |
| 4 addresses, 3 data directories, `decide`d distinct | `k + 1` addresses, `k` data directories, distinct by `decStr_inj` | generated |
| `Haf`, `Hbuq`, `Hrf`, `Hdbo`, `HNs`, `HEnv`, `Hn`, the semantics classes | the same | unchanged |

**The id premise.** `BootCore`'s "16 low bits distinct and not 0" is putget3's premise too, but it now
has to hold for every `k ≤ 1000`, which a random token makes unlikely (birthday bound of 16 bits: at token
`putgetN` it fails first at `k = 214`, so the theorem would be vacuous above 213). The token `putgetN-1405` is the
first `putgetN-<i>` at which it holds for every `k ≤ 1000`; `TestMemberIDs` checks it for every `k`, from the ids
etcd computes without starting a cluster (member `i`'s id depends only on its peer URL and the token, so the ids of
`k` members are those of `k + 1` minus the last). This choice is the one decision to review: **recommended**, as it
is what makes the premise true at every claimed `k`; the alternative is the token `putgetN` with the bound lowered
to `k ≤ 213`.

## Trust base

No axiom or trusted text is added. `Members` calls `strconv.FormatUint`, whose trust-boundary axiom is already in
putget3's collection. One law is needed at linking: `rafthttp.bootCfg` for a directory of up to 1000 members
(`rafthttp.bootCfg_of` takes at most 3; the definition's bound is `peersMax = 2^20`). It is a new constructor lemma
in the sealed module `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean` (no unsealing, no change to
the definition); `Main.wp_proof` takes it as a hypothesis (`hbcfg`) until then.
