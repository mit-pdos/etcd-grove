# kvraftN: Scope (2026-11-15, for etcd-grove-81)

Goal (the user, 2026-11-15, via etcd-grove-81): the paper's Figure 2 is about k members; the Raft-library
theorems `raft_kv_porcupine_safe`, `raft_kvreconf_porcupine_safe` and `raft_kvdurable_porcupine_safe` are to be
stated for k replicas (`raft_kvwitness_porcupine_safe`, two voters and a witness, stays as it is). Branch `kvraftN`
(worktree `/shared/etcd-grove-restartN`, off lean `4d6437b44a`). This is the Scope: no Lean or Go change yet
besides a scratch probe.

## Finding 1: only kv is 3-replica; kvreconf and kvdurable already run 1 to 5 voters

The brief's premise holds for **kv** only:

| theorem | `Main` | voters | replicas started |
|---|---|---|---|
| `raft_kv_porcupine_safe` | `StartCluster([]uint64{1, 2, 3})` | 3, fixed | 3 |
| `raft_kvreconf_porcupine_safe` | `Run(RandomConfig(), …)`: `RandomOptions().Voters = 1 + below(5)` | 1 to 5, drawn by `Main` | up to `maxReplicas = 9` (reconfiguration adds fresh ones) |
| `raft_kvdurable_porcupine_safe` | the same, `Main(dir)` | 1 to 5, drawn by `Main` | up to 9, each with a file `dir/replica-<id>` |

The kvreconf and kvdurable theorems are about every execution of `Main`, so they already cover every initial
voter count 1 to 5 (`OptsOk`: `1 ≤ Voters ≤ 5`; `StartCluster.spec` is stated over `bootVoters (uint.nat
o.Voters')`, generic in the count). Nothing in them is 3-specific. What is fixed is **5** (the largest initial
count) and **9** (`maxReplicas`, the ids `1 … 9`).

## What is 3-specific in kv

The Go library is generic (`StartCluster(voters []uint64)`, `NewStorage(voters)`, `Check`'s replica index
`in.Replica % len(kvs)`); only `Main` names `{1, 2, 3}`. In the proof, `kvVoters := [W64 1, W64 2, W64 3]`
(`Defs.lean`) is a global constant, and the 3-specific points are:

- **Spec**: `StartCluster.spec` takes `vsl ↦*□ [W64 1, W64 2, W64 3]` and returns `rs.length = 3`.
- **Definitions** using `kvVoters`: `kvMembership` (`Membership.simple (listToSet kvVoters)`), `runStor` (the
  storage's `voters` slice `↦*□ kvVoters`), `rkvInv`'s `confAt γr.cluster 0 kvMembership`.
- **Concrete facts by `decide`** on the list: `kvCluster_alloc` (raft's `cluster_alloc` premises: nonempty,
  `Nodup`, `0 ∉`, length `< 2^62`), `kvConfState_is` (`Nodup`), `KV__run`'s `snapListsOk_voters` (four
  `decide`s), `StartCluster`'s `clusterIds_nodup`, `clusterIds_size` (only for `clusterIds_ne`),
  `nodeConfig_valid` (`rcases … rfl | rfl | rfl`), `Hvlen3`, and the loop's exit (`take 3`/`drop 3`).
- **`Main`'s proof**: the slice literal `{1, 2, 3}` and `Hne` from `rs.length = 3`.
- **Adequacy**: `kvProgram` is `initialize'(); Main()`, no argument.

Raft's side is already generic: `cluster_alloc_dec_impl` takes any `vs` with `vs ≠ [] ∧ vs.Nodup ∧ W64 0 ∉ vs ∧
vs.length < 2^62`; `RestartNode` takes `ConfigValid` (id `∉ {0, 2^64-1, 2^64-2}`). The store's other state is
keyed by replica id (`S`, the sequence numbers: `constMap clusterIds 0`) and the `StartCluster` loop invariant
is already `take k`/`drop k` of the list.

## What a k-replica statement looks like

### kv (recommended: `MainN(k)`, `Main()` = `MainN(3)`)

- **Go**: `func MainN(k uint64)` builds `voters = 1 … k` (`for i := uint64(1); i <= k; i++ { voters =
  append(voters, i) }`, as kvreconf's `StartCluster` builds `boot.Voters`), then `StartCluster(voters)` and
  `Check(kvs, CounterClock(), 4, 25)` as now; `Main()` becomes `MainN(3)`. The workload is unchanged: 4 clients
  of 25 operations, each on replica `n / 9000 mod k`.
- **`StartCluster.spec`, over a voter list**: `∀ vsl vs, KvVotersOk vs → … vsl ↦*□ vs … {{ ∃ γr rs, ksl ↦* rs ∗
  ⌜rs.length = vs.length⌝ ∗ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗ rkvVal γr kvEmpty }}`, where `KvVotersOk vs`
  is raft's premises plus `ConfigValid`'s ids: nonempty, `Nodup`, no `0`, `2^64-1` or `2^64-2`, length `< 2^62`.
  This is what the Go function needs (raft panics on a duplicate or a `0` id), not what one caller passes.
- **The voter list in the store's ghost names**: `RKVNames` gains a field `voters : List w64` (pure, like
  kvreconf's `isClusterC γr vs`); `kvVoters` becomes `γr.voters`, `kvMembership` a function of it, and
  `rkvInv` holds `⌜KvVotersOk γr.voters⌝`, from which the `decide`s above are replaced by the probe's generic
  lemmas. `isKV γr …` is unchanged in shape, so `Check.spec` (already over any `rs ≠ []`) and the per-operation
  specs (`Put`/`Get`/`Append`/`Read`) do not change.
- **New closed theorem** `raft_kvN_porcupine_safe (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ B)` over `kvProgramN k :=
  initialize'(); MainN(#(W64 k))`, the conclusion as now. **`raft_kv_porcupine_safe` keeps its text**: `Main()`
  is `MainN(3)`, its spec a corollary (the program's code changes, the statement does not).
- No new premise beyond `1 ≤ k ≤ B`, no axiom, `sorry` or trusted text.

### kvreconf and kvdurable: two options

- **(R1) Leave them** (cost 0): they already are k-member theorems over the program's own random draw,
  `k ∈ 1 … 5`, up to 9 replicas. Figure 2 can say "1 to 5 initial voters, chosen by the program; up to 9 replicas
  through reconfiguration (and crashes)".
- **(R2) `MainN(k)`** for uniformity with kv and etcd's N theorems: `RandomConfigN(k)` = `RandomConfig()` with
  `Voters = k`; `maxReplicas` from a constant to a `Cluster` field `max = k + 4` (at `k = 5`, today's 9); `Main()`
  unchanged (`Voters = 1 + below(5)`, `max = Voters + 4`... or kept at 9: see below). 5- and 9-specific places to
  generalize:
  - `OptsOk`'s `Voters ≤ 5` (kvreconf `DefsCluster`; kvdurable `kdOptsOk`) → `Voters ≤ B`;
  - `allIds := bootVoters 9`, `freshIds k := range 10 filtered`, `allIds_split (k ≤ 9)`, the `bootVoters_*`
    lemmas' `k ≤ 10`, `size_of_keys`' `nid ≤ 10`, `freshIds_cons (k < 10)`, `startNew`'s `nid < 10`
    (kvreconf and kvdurable), all becoming functions of `max`; the lemmas only need `max < 2^61`;
  - kvdurable: replica ids `1 ≤ id ≤ 9` in `Cluster.start.spec`, `newReplica.spec`, `readSeqs.next.spec`,
    `kdFileInv`'s `%Hidr`, `freshIds_get`; the files' distinct names `kdFileNames_nodup` (today 9 concrete
    digits by `rw`/`decide`) by `decimalB_inj` (probed below); `Main`'s and the closed theorem's premise
    `∀ i ∈ allIds, fs !! kdFileName dir i = none` becomes over `1 … k + 4` (a premise that depends on k, as
    restartN's `dataDirsAbsent (restartNProgram k) …`).
  - New closed `raft_kvreconfN_porcupine_safe`, `raft_kvdurableN_porcupine_safe` over `k`; the existing two keep
    their text if `Main()` stays `Run(RandomConfig())` with `max = 9` (the `Cluster` field then set to 9 by
    `Main` and to `k + 4` by `MainN`): their specs follow from the generalized lemmas at `max = 9`.

### What bounds the bound B

Nothing in these proofs below about `2^61`:
- raft: `cluster_alloc`'s `vs.length < 2^62`; `ConfigValid`'s ids exclude `2^64-1`, `2^64-2` (ids `1 … k`);
- kvreconf/kvdurable: `newReplica.spec`'s `GMap.size m.ids < 2^61` (ids `1 … k + 4`);
- Go: `k` and the ids are `uint64`, the loop `i <= k` needs `k < 2^64 - 1`;
- no thread tokens: these examples take none (`etc/bounds-check.py` counts only their receipt specs, which do
  not depend on k); the step bound (`n < 2^61`) and the receipts' bound (`2^61`) are per execution, not per
  replica;
- the per-id ghost state (`[∗list]` over `1 … k` or `1 … k + 4`) stays symbolic; nothing materializes it (the
  CLAUDE.md rule on large lists: no bare `iframe` there).

Recommended **`B = 1000`**, the bound of etcd's N theorems (`etcd_restartN_safe`, `etcd_txnlinfaultsN_safe`), so
that Figure 2 has one range; any `B < 2^61` costs the same, so a larger one (e.g. `2^32`) is a free alternative
if the figure does not need uniformity. `k = 1` is included: a single voter elects itself and serves (raft's
single-voter read-index fix is in the pinned raft); measured below.

## kvreconf's configuration changes and kvdurable's crash/restart files

Neither depends on 3. Configuration changes act on any configuration (`validConf`, raft's joint
configurations; ids drawn from the current configuration or fresh up to `maxReplicas`); the only constants are
5 and 9 above. kvdurable's files are per replica id, named `itoa(id)`: their distinctness is today 9 concrete
digits; for `max = k + 4` it needs `itoa` injective, which holds and is proved in the probe
(`decimalB_inj`, from core's `Nat.ofDigitChars_ten_toDigits`).

## One shared `StartCluster.spec`?

No: the three `StartCluster`s are different Go functions (`kv.StartCluster(voters []uint64)`,
`kvreconf.StartCluster(opts)`, `kvdurable.StartCluster(opts, dir)`) of different packages with different
invariants (`isKV`, `isClusterC`, kvdurable's files). What they share is the voter vocabulary: kvreconf's
`bootVoters k` and its lemmas (kvdurable already uses kvreconf's). kv should take a voter list (`KvVotersOk vs`,
above), the most general form for its Go signature; its `MainN` proof instantiates it with `1 … k` (a local
copy of `bootVoters` with three lemmas, or an import of kvreconf's `DefsCluster` as kvdurable does; recommended
the local copy: kv importing kvreconf drags in its whole definitions).

## Go tests

- kv: `TestMainN` (`kv_test.go`) draws k from {1, 3, 5, 7} at random, `KV_MEMBERS` overrides (1 … B), logs
  the k and the rerun command, runs `MainN(k)` (as `TestMainRun` of txnlinfaultsN, `TXNLINFAULTSN_MEMBERS`);
  `TestMainPasses` keeps `Main()`. `cmd/kvcheck`: `-members k` runs `MainN(k)`.
- (R2) kvreconf/kvdurable: `TestMainN` likewise (`KVRECONF_MEMBERS`, `KVDURABLE_MEMBERS`), runs `MainN(k)` and
  checks `Converged` as `TestRounds` does.
- Measured today (no code change; `kvcheck -replicas k -clients 4 -ops 25`, the `MainN` workload): k = 1, 3, 5, 7,
  9 three rounds each, k = 25 and k = 101 one round: porcupine `Ok`, 60 to 370 ms per round.
- kvreconf/kvdurable, `Run(RandomConfig())` with `Voters` overridden to 1, 3, 7 (today's `maxReplicas = 9`; a
  throwaway test, deleted): all porcupine `Ok`. kvreconf 14 s, 4 s, 6 s. kvdurable 20 s, 15 s, and **15 min at
  k = 7** (one sample; the first attempt hit `go test`'s 10-minute timeout). Safety is not in question, but a test
  that draws k = 7 for kvdurable needs that understood first (likely crashes and fsync-heavy restarts against a
  7-voter quorum, with only 2 fresh ids left under `maxReplicas = 9`): one more reason to pick R1 for kvdurable,
  or, under R2, to draw kvdurable's test k from {1, 3, 5} until the slowness is explained.

## Trusted text

None. The Go changes are in the translated, verified examples (`MainN`, kvreconf/kvdurable's `max` field);
no Goose configuration (`Code/**/*.toml`) lists anything of these packages as trusted; no axiom, `sorry`,
opaque or `TrustedCode` model is added. The collections `etc/tcb-collections/{kv,kvreconf,kvdurable}.txt` gain
the new roots with the same baseline.

## Estimates

| item | work | estimate |
|---|---|---|
| kv | Go `MainN` + tests + retranslation; `RKVNames.voters`, `KvVotersOk` in `rkvInv`; `StartCluster` spec and proof over `vs`; `MainN`/`Main` proofs; `kvProgramN`, adequacy, `Results`, collection, gen-link | 2 to 3 days |
| kvreconf (R2) | `max` field, `OptsOk ≤ B`, `allIds`/`freshIds` of `max`, lemmas, `startNew`, `RandomConfigN`, `MainN`, adequacy | 2 to 3 days |
| kvdurable (R2) | kvreconf's, plus ids `≤ max` in five specs, `kdFileNames_nodup` by `decimalB_inj`, the files premise over `1 … k + 4` | 3 to 4 days |

(R1) costs nothing for kvreconf/kvdurable; kv alone is 2 to 3 days.

## Probe (the riskiest points, scratch Lean)

`/shared/tmp/kvraftN/KvraftNProbe.lean` (not committed; checked with `etc/lean-check.py -a`: 0 errors, no
`sorry`), importing kv's `StartCluster`, `Reconf`, `KV__run` and kvdurable's `Defs`:
- `KvVotersOk`, `kvBootVoters k` with `kvBootVoters_ok (1 ≤ k < 2^62)`: the `decide`s on `[1, 2, 3]` replaced;
- `nodeConfig_valid_gen` (any id of a `KvVotersOk` list is `ConfigValid`), `kvConfState_is_gen`,
  `snapListsOk_gen`: the three places that used the concrete list;
- `decimalB_inj` (`itoa` injective), kvdurable's file names for any number of replicas.

The Iris-level changes (the `StartCluster` loop to `vs.length`, the `voters` field threaded through `rkvInv`,
`runStor`, `appNode`) are mechanical: the loop invariant is already over `take k`/`drop k` of the list, and every
use of the concrete list is one of the `decide`s above.

## Recommendations

1. kv: `MainN(k)` with `Main() = MainN(3)`, `StartCluster.spec` over a `KvVotersOk` voter list, new
   `raft_kvN_porcupine_safe` for `1 ≤ k ≤ 1000`, `raft_kv_porcupine_safe`'s text unchanged.
2. kvreconf/kvdurable: (R2) for a uniform Figure 2 (`MainN(k)`, `max = k + 4`, `1 ≤ k ≤ 1000`, existing
   theorems unchanged at `max = 9`), in that order after kv; or (R1) if the figure can say "1 to 5 voters, up
   to 9 replicas" (no work).
3. `B = 1000` for uniformity with etcd's N theorems (any `B < 2^61` at the same cost).
