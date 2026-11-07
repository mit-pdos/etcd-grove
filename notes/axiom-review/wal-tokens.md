# The WAL's file-state tokens: `walDirFresh`, `walDirsAbsent`, `walFiles` (axiom sweep B3-1)

Reviewed 2026-11-07 by the `axiom` skill (sweep phase 1, Go first), on `lean` at `d4fe2b0a67`, worktree
`/shared/etcd-grove-sweep3` (branch `axiom/sweep-b3`). Go at the etcd pin `673da07c8` (the module cache's
`github.com/upamanyus/etcd/server/v3@v3.0.0-20261103162249-673da07c8fab`, which `examples/go.mod` uses;
`.lake/go-src/etcd` is checked out at another commit and was not used). **No Lean was built** (the
sweep's disk budget): the Lean side below is a sketch, to be built later.

## The axioms and the statements that produce and consume the tokens

| Statement | Where (at `d4fe2b0a67`) | Kind |
|---|---|---|
| `walDirFresh dir` (+ `walDirFresh_timeless`) | `Proof/go_etcd_io/etcd/server/v3/storage/WalDir.lean:27,30` | axiom (opaque `IProp`) |
| `walDirsAbsent e Ds` | `Proof/runtime/Start.lean:86` | axiom (opaque `Prop`, a hypothesis of every closed theorem) |
| `goose_adequacy_start` (its `Ds` part: `startRights`' `[∗list] d ∈ Ds, walDirFresh d` under `hDs : Ds.Nodup`, `hDsFree : walDirsAbsent e Ds`) | `Proof/runtime/Start.lean:89-94,103-121` | axiom |
| `walFiles dir id cid σ` (+ `walFiles_timeless`) | `Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean:178,181` | axiom (opaque `IProp`) |
| `bootstrapContract` (consumes `walDirFresh` through `wal.bootRes`, `WalApi.lean:195-196`) | `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean:503` | premise (`Hprem` of every closed theorem, via `etcdstart.bootPremise`) |
| `isWalStorage`'s `Close` law (produces `walFiles`) | `Proof/go_etcd_io/etcd/server/v3/etcdserver/WalApi.lean:76-85`, given by `rnNewStorageOk` (`InvNodeStart.lean:172`) | premise (`Hprem`) |
| `bootstrapRestartContract` (consumes `walFiles` through `srvFiles`, `InvRestart.lean:79`) | `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRestart.lean:563` | DRAFT premise; used only by `etcdstart/Restart.lean`'s `bootPremiseR` and the restart example's `restartCheck.spec`; no exported result |
| `walPurgeRight` (taken by `Close`) | `WalRecs.lean:192` | opaque; `EtcdServer.purgeFile.spec` does not take it (plan item (5) not applied) |
| `walBaseLb` | `WalRecs.lean` | sealed def; `storage.Release.spec` does not take it (plan item (4) not applied) |

### The claims, in plain words

1. `walDirFresh dir`: "the directory `dir` holds no WAL" (`WalDir.lean` header), so `bootstrap` on it
   starts a new member. Not exclusive, timeless; produced only by program start.
2. `goose_adequacy_start` + `walDirsAbsent`: program start hands the WP proof one `walDirFresh d` for
   each **string** `d ∈ Ds`, `Ds.Nodup` **as strings**; `walDirsAbsent e Ds` says no WAL is in a
   directory of `Ds` at start and none is created there by unverified code or another process. Its
   argument (`Start.lean:28-32`): "the verified code's first `bootstrap` of `d` consumes the right; so
   each directory of `Ds` is bootstrapped fresh at most once in a run".
3. `bootstrapContract`: with `walDirFresh (config.walDirOf cfg.DataDir cfg.DedicatedWALDir)`, a
   `NewCluster` configuration, `dbOpensOk`, `walCreateOk`, `bootstrap` returns an error or `bootOk`:
   a **fresh** member (WAL records `walFresh`, consistent index `0`, `Meta` empty, the KV store empty,
   the member id computed from the configuration, the cluster the configuration's).
4. `walFiles dir id cid σ`: "a closed WAL's files in `dir` read back as `σ` with metadata `(id, cid)`".
   Made by `Close` (which takes the whole open token, the records, the metadata and the purge right);
   consumed only by the DRAFT restart contract. Not exclusive.

## Verdict

| Axiom | Verdict |
|---|---|
| `goose_adequacy_start` (its `Ds` part), with `walDirsAbsent` | **Refuted (Go side; Lean sketched, not built).** `Ds.Nodup` is a fact of strings; the argument needs distinct directories. Two strings name one directory (`wda-3.etcd` and `/proc/self/cwd/wda-3.etcd`), so the proof holds a `walDirFresh` of a directory after another member's bootstrap created a WAL in it. Counterexample below, 20/20 runs panic. |
| `walDirFresh` | Refuted jointly with the above: its meaning ("the directory holds no WAL") does not survive another string's bootstrap of the same directory. Read as `True` it is consistent (no `⊢ False`), as its header says; the falsity is in what start gives and `bootstrapContract` reads. |
| `walDirsAbsent` | True as worded for the counterexample (no WAL at start; the only WAL is created by verified code), so the gap is the wording: it says nothing about two strings of `Ds` naming one directory. |
| `walFiles` | **Survives**, vacuously for now: no exported result consumes it (only the DRAFT `bootstrapRestartContract`). Two latent gaps for when the restart contract lands, below. |

## The counterexample (the deterministic variant)

`examples/axiomcx/waldiralias/waldiralias.go` (package `waldiralias`; tests only, no Goose project yet).
`Run` is `examples/etcd/restart`'s `Run` up to the stop, with no snapshots (`etcdstart.NoSnapCount`, so
that a member catches up by appends), then:

```go
// freshCheck starts member AliasPrefix+name as the one member of a new cluster (StartServer:
// peer URL http://peerAddr4, not served; client address clientAddr4), serves its gRPC API and
// panics if a Get of k0 through it returns a value. An error from any step returns.
func freshCheck(name string, lg *zap.Logger) {
	s, err := etcdstart.StartServer(AliasPrefix+name, peerAddr4, clientAddr4, lg)  // AliasPrefix = "/proc/self/cwd/"
	...
	if err := etcdstart.Serve(s, clientAddr4); err != nil { return }
	cli, err := etcdstart.NewClient(clientAddr4, lg)
	...
	resp, err := cli.Get(ctx, "k0")
	...
	if len(resp.Kvs) != 0 {
		panic("waldiralias: a new cluster's Get returned a key no client of it put")
	}
}

func Run(lg *zap.Logger) {
	// members wda-1, wda-2, wda-3 (token "waldiralias"), data directories "wda-i.etcd";
	// wda-1 serves gRPC; Put k0=v1 through it
	...
	if m3.s.Leader() == m3.s.MemberID() {
		stop(m2)            // examples/etcd/restart's stop: AppliedIndex ≥ 3, HardStop, peer listener closed
		freshCheck("wda-2", lg)
	} else {
		stop(m3)
		freshCheck("wda-3", lg)
	}
}
```

The fresh member's data directory is `/proc/self/cwd/wda-3.etcd`, its WAL directory
`filepath.Join(..., "member", "wal")` = `/proc/self/cwd/wda-3.etcd/member/wal`: a different string from
`wda-3.etcd/member/wal` (`filepath.Join` cleans `./` and `..`, so those aliases do not work; an
absolute alias through the kernel's `/proc/self/cwd` link does, with a constant string and no
unverified code), the same directory (`TestAliasDirs`: `os.SameFile`).

**What Go does** (pin `673da07c8`): `bootstrap` computes `haveWAL := wal.Exist(cfg.WALDir())`
(`server/etcdserver/bootstrap.go:77`; `wal.Exist`, `storage/wal/util.go:30-36`: any `*.wal` file) — true,
the stopped follower's WAL; `bootstrapCluster` takes `bootstrapClusterWithWAL` (`bootstrap.go:332-333`,
`:412-435`), which ignores `NewCluster`, the name, the token and the initial cluster and takes the node
and cluster ids from the WAL's metadata. The "fresh" member is the stopped follower restarted; it rejoins
its old cluster (its transport adds the old peers from the backend's members; the leader reaches it
over the stream it dials, it reaches the leader by the pipeline), catches up, and the linearizable Get
returns `k0 = v1`.

**What the proof says**: the fresh start's `bootstrapContract` (the same premise every closed theorem
takes, at a configuration meeting `cfgOk token name cfg`, `bootCfgFresh`) gives `bootOk` of a new
one-member cluster whose KV state is empty; no client of that cluster puts anything, so its Get of `k0`
returns no key, and the `panic` is dead code.

**Test** (`go test ./axiomcx/waldiralias/ -v`, go1.27.3, the pins of `examples/go.mod`, under
`systemd-run --scope -p MemoryMax=32G`; logs `/shared/tmp/7c-logs/b3-1-*.log`):

```
=== RUN   TestAliasDirs
    waldiralias_test.go:54: wda-3.etcd/member/wal and /proc/self/cwd/wda-3.etcd/member/wal: one directory
--- PASS: TestAliasDirs (0.00s)
=== RUN   TestRun
    waldiralias_test.go:63: messages of a boot from an existing WAL: 2
    waldiralias_test.go:68: Run panicked: waldiralias: a new cluster's Get returned a key no client of it put
--- PASS: TestRun (1.41s)
=== RUN   TestFreshIDs
    waldiralias_test.go:89: /proc/self/cwd/wda-2: member 912b56ec45527c1d, low 16 bits 0x7c1d
    waldiralias_test.go:89: /proc/self/cwd/wda-3: member f8091bf1e1712913, low 16 bits 0x2913
--- PASS: TestFreshIDs (0.00s)
```

`TestRun` passes when `Run` panics (recovered on the main goroutine). 20 runs in separate processes:
20/20 panicked ("boot from an existing WAL: 2" = `bootstrapWALFromSnapshot`'s and the restart's log
lines). `TestFreshIDs` checks the fresh member's `BootFacts` premise (its id's 16 low bits not `0`).
`go.mod`/`go.sum` unchanged.

### The racy variant (a panic inside `bootstrap` itself)

`examples/axiomcx/waldiralias/race.go`, `RaceRun`: two one-member clusters started at once on goroutines,
data directories `wdb.etcd` and `/proc/self/cwd/wdb.etcd`. Both bootstraps see no WAL (`wal.Exist`
before any lock, `bootstrap.go:77`); one opens the bbolt file first (`backend.go:233`, no `Timeout`: the
other blocks on bbolt's `flock`); the program `HardStop`s the started one, whose backend close releases
the lock; the other goes on with its stale `haveWAL = false`, `bootstrapNewWAL` calls `wal.Create`,
which returns `os.ErrExist` (`storage/wal/wal.go:103-105`), and `cfg.Logger.Panic("failed to create
WAL")` (`bootstrap.go:717-719`) panics on that goroutine. `TestRace` (child process): 19/20 runs panic
with `panic: failed to create WAL` (`{"error": "file already exists"}`); the other outcomes are
`lg.Fatal("failed to create snapshot directory")` (`bootstrap.go:211-212`: the two `TouchDirAll`s race
on `member/snap/.touch`; `os.Exit`, not a counterexample) and, with a development logger, a run where
the second start's `Exist` came after the first's `Create` (no panic). This variant needs no KV
reasoning, but it is racy and it leans on `storage.walCreateOk`, whose text excludes "another
**process** creating a WAL in the directory meanwhile" (`InvOpen.lean:100-110`); in-process creation
by another member is not named, so the premise holds as worded, but a reader may argue its intent.
The deterministic variant does not touch `walCreateOk` (Go never calls `wal.Create` there).

## The Lean side (SKETCH; not built)

A project `waldiralias` modelled on `restart`'s (`etc/goose.py`, `local=examples/axiomcx/waldiralias`),
with `RaceRun` moved out of the package (or a second package) so that `Main` is `Run(zap.NewNop())`.

**The triple of `Run`** (`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/waldiralias/Run.lean`),
by the proofs of `examples/etcd/restart`'s `startMember`, `serveClient`, `put` and `stop` (all proved:
`grep -c sorry` is 0 in `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/restart/`; `stop` through the
proved `EtcdServer.HardStop.spec`), and etcdstart's `StartServer`/`Serve`/`NewClient` (putget's):

1. Precondition as `restart`'s `Run.spec`, plus `memberStartRes (AliasPrefix ++ "wda-2") a₄` and
   `memberStartRes (AliasPrefix ++ "wda-3") a₄` (each `walDirFresh (memberWalDir n) ∗ netAddrFree
   clientAddr4 …`, `StartRes.lean:70`; only one branch runs, the other's rights are dropped) and
   `etcdstart.bootPremise` for the one-member cluster of each alias name (token = name, peers
   `[id₄]`, its `BootFacts`).
2. Up to the stop: `restart`'s proof verbatim (three fresh starts, each consuming `walDirFresh
   (memberWalDir "wda-i")` through `bootstrapContract`; `serveClient`; `put k0 v1`; `stop`, which
   consumes `memberStop`, returns `srvDiskImage`, dropped).
3. `freshCheck`: `StartServer.spec` with `walDirFresh (memberWalDir (AliasPrefix ++ "wda-3"))` — still
   held: no step consumed it — and the alias cluster's `bootPremise` (so `bootstrapContract` at
   `cfgOk (AliasPrefix ++ "wda-3") (AliasPrefix ++ "wda-3") cfg`): the fresh member of a new cluster,
   whose KV state is `etcdKV γ₄.kv σ₀` with `σ₀.kvs = []`.
4. Allocate `inv kvClientN (∃ σ, etcdKV γ₄.kv σ ∗ ⌜mvcc.findKey "k0" σ.kvs = none ∧ σ.kvs.Pairwise
   etcdKvLess⌝)` (as putget allocates `client.putGetInv`, `PutThenGet.lean:100`); its read update
   (`kvReadAu`, the proof of `getAu_of_putGetInv` with the flag removed) gives the Get's result
   `findKey "k0" σ.kvs = none`, so `resp.Kvs = []`; the `if len(resp.Kvs) != 0` branch is dead.
5. `Run` returns `#()`.

**The closed theorem** `waldiralias_adequate`, as `etcd_putget3_adequate` (`putget3/Adequacy.lean:125`)
through `etcdstart`'s `etcd_adequate_members`, hence `goose_adequacy_start`, with
`Ds := [memberWalDir "wda-1", memberWalDir "wda-2", memberWalDir "wda-3", memberWalDir (AliasPrefix ++
"wda-2"), memberWalDir (AliasPrefix ++ "wda-3")]`, hypotheses `HDsNd : Ds.Nodup` (as putget3's: true of
Go's `WALDir()`, five distinct strings) and `HDs : walDirsAbsent prog Ds` (true: the run starts in an
empty directory, and the only WAL is created by the verified `bootstrap` of `wda-3`), `As` the four
listened addresses (`peerAddr1-3`, `clientAddr1`) and `clientAddr4`, and `Hprem` as `restart`'s plus the
two alias clusters' `bootPremise`. Conclusion: no thread ends in a panic. Go: the main thread panics.

`#print axioms` of it would list the whole server stack's trust base (every closed theorem's), not just
the reviewed axioms: the program must run etcd. The step that uses the false fact is the one
`bootstrapContract` application in step 3, which is true of Go under `walDirFresh`'s documented meaning;
what makes that meaning false at that point is `goose_adequacy_start` handing a token per string. Every
other premise is true in the run (checked: `bootCfgOk`/`bootCfgFresh` of the alias configuration,
`dbOpensOk` (bbolt opens), `walCreateOk` (not exercised), `BootFacts` (`TestFreshIDs`), the scope of
`HardStop` (the stopped follower never served gRPC)).

## Which results rest on it

`goose_adequacy_start` is taken by every closed adequacy theorem (`grep -rn walDirsAbsent Proof`):
`etcdstart`'s `Adequacy`/`AdequacyMembers`, and `putget`, `putget3`, `partition` (+ `AdequacyWatch`),
`cache`, `compacted`, `compactwatch`, `lease`, `leasecatchup`, `leaseexpiry`, `leasegrant`, `txnlin`,
`watch`, `k8s/compactor`, `k8s/etcd3` (three theorems). Their own programs do not alias: every data
directory is `<name>.etcd` relative to one working directory, with distinct slash-free names, so those
statements stay true of their programs; what is false is the axiom's general claim, which a new
program can instantiate. The reach the sweep plan quotes (47/17, 36/17, 17/17) counts these.

## Proposed restatement (not applied)

Make the distinctness a fact of directories, not strings. Minimal: add to `walDirsAbsent`'s docstring
(and so to what a user checks): "the strings of `Ds` name pairwise distinct directories for the whole
run (no two resolve to one directory through symbolic links such as `/proc/self/cwd`, absolute versus
relative paths, or a change of the working directory), and no WAL directory any configuration of `e`
bootstraps names a directory of `Ds` under a string not in `Ds`". With it, `Start.lean`'s argument goes
through: a WAL created in a directory of `Ds` is created by the bootstrap that consumed that
directory's only token. A checkable alternative for the examples: `Ds` of the form `memberWalDir n`
for distinct names `n` with no `/` and not `.`/`..`, and the program never changes its working
directory. The same per-string flaw is in `backend.pathOwn` (D22's "nothing else creates, renames or
deletes a file at `<DataDir>/member/snap/db`", given by each `bootOk` per string: here the fresh
member's `bootOk` gives a second `pathOwn` of the stopped follower's file), and possibly in `As`
(`netAddrFree` per string: `127.0.0.1:p` / `localhost:p` / `:p`); not attacked here.

## Attacks tried that failed, and why

1. **Two members on aliased directories, concurrently, no stop.** The second blocks forever in
   `bolt.Open`'s `flock` (`storage/backend/backend.go:231-235`; `storage.OpenBackend`, `server/storage/backend.go`, never sets `Timeout`, so
   no timeout): a hang, not a counterexample. The stop is what turns it into a panic (both variants).
2. **Two `walDirFresh` of one string.** `hDs : Ds.Nodup` gives one token per string; nothing else
   produces `walDirFresh` (`grep`: only `startRights`, `memberStartRes`, `wal.bootRes`); it is opaque,
   so no proof duplicates it.
3. **Two closes of one WAL** (two `walFiles` from one WAL). `Close` takes `storage.walOpen w 1` whole
   (`WalApi.lean:79-80`) and gives nothing back; the server's one `Close` is `raftNode.onStop`'s.
4. **Contradictory `walFiles` (records before and after an append).** A `walFiles` is made only by
   `Close`, after which no `Save` is possible (no open token). Two `walFiles` of one directory string
   need two WALs bootstrapped there: two `walDirFresh` of one string (attack 2) or a restart (DRAFT,
   linear: it consumes the `walFiles`). Through aliasing they need two strings, and then each
   `walFiles` names its own string. No exported result reads a `walFiles` (only the DRAFT
   `bootstrapRestartContract`), so a contradiction there could not reach a closed theorem today.
5. **Close then a second writer in one process.** In Go, `wal.Open` for writing after `Close` is the
   restart path; while the first is open the second blocks on bbolt (attack 1). Only the restart
   contract reads the files, DRAFT.
6. **A stale lock file / leftovers.** The WAL has no lock file: its locks are `flock`s on the segment
   files, released at `Close` or exit. A leftover `member/wal.tmp` is removed by `wal.Create`
   (`wal.go:112-118`). A leftover `*.wal` is excluded by `walDirsAbsent`.
7. **`wal.Create` on an existing directory.** `Create` returns `os.ErrExist` only if a `*.wal` exists
   (`wal.go:103-105`); `bootstrap` calls it only when `wal.Exist` was false, so only a race with
   another creator reaches it: the racy variant above (in-process, not excluded by `walCreateOk`'s
   "other process"). A directory with non-WAL files is removed whole by `renameWAL`'s
   `os.RemoveAll(w.dir)`, with no panic.
8. **Torn writes, failed `Close`/`Save`/`Create`.** I/O failures, excluded by `storage.diskOk`
   (`walSaveOk`, `walCloseOk`, `walCreateOk`, `dbOpensOk`; `InvOpen.lean:118`), which every closed
   theorem takes; `Close`'s error case is `⌜¬ storage.walCloseOk⌝`.
9. **Purge versus `Close`** (`walPurgeRight`). `EtcdServer.purgeFile.spec` takes nothing (plan item (5)
   not applied), so the right's meaning ("the purge is not running") is not enforced by the logic. In
   Go the order holds: `run`'s shutdown does `s.wg.Wait()` (which waits for `purgeFile`, attached by
   `s.GoAttach(s.purgeFile)`, `server.go:538`) before `s.r.stop()` (`server.go:827-833`). Only the restart
   contract would read files a purge removed: latent, DRAFT.
10. **`Release` versus the records' base** (`walBaseLb`). `storage.Release.spec` does not take it (plan
    item (4) not applied); `ReleaseLockTo` only drops locks, the purge removes files; same as 9: latent
    until the restart contract is used.

## Not tried

- The `As` (address) analogue of the alias (`localhost:p` versus `127.0.0.1:p`): `Listen.spec` allows an
  error, so a second bind fails cleanly; whether `httpProtoFree`'s once-per-address protocol can be
  split by an alias was not checked.
- An alias through a change of working directory (`os.Chdir`; probably unspecified, so not provable)
  or a dedicated WAL directory (`DedicatedWALDir`: the examples' `cfgOk` fixes it empty).
- A data directory nested inside another member's WAL directory (`/proc/self/cwd/a.etcd/member/wal` as a
  data directory: the first member's `wal.Create` `RemoveAll`s it); no panic expected, not run.
- The restart contract's own claims (`bootstrapRestartContract`, `srvFiles`): DRAFT, out of scope until
  it is used by a result.

## In the Go code

Not a bug in the verified code's use: two etcd servers on one data directory is a misuse etcd does not
support. One robustness finding, by test, for `nonissues/` if the user wants it: `bootstrap` computes
`haveWAL := wal.Exist(...)` (`bootstrap.go:77`) **before** taking bbolt's file lock
(`bootstrapBackend`, `:78`), so a second server started on a directory whose first server has not yet
created its WAL waits on the lock and then, once the first exits, panics in `bootstrapNewWAL`
("failed to create WAL: file already exists", `:719`) instead of restarting from the WAL or returning an
error (a check-then-act race; shown in-process by `TestRace`, plausibly the same across processes).
Not filed.
