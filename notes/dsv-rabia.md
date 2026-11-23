# dsv-rabia: dsverify-lab's rabia kit on the net extension (phase 6)

Branch `dsv-rabia` (2026-11-23, off `origin/dsv-paxos` `e3eaf5cd0d`), worktree
`/shared/etcd-grove-dsvrabia`. Plan: `notes/dsverify-net-port-plan.md`, phase 6; pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/rabia/` (read only):
run **`rabia-r1wake-1`**, proof `2a8c0fc` (tag `final`), fork `ef2a93b` (R1-wake: the executor waits on
a slot's wake channel), Perennial `3afd77e35`; the lab's statement `dsv_goal_check : SafeDist
(orchNode :: clientNodes ++ serverNodes) rabiaNetCfg`, axioms Lean's three and porcupine's
`CheckOperations.wp_proof`. The lab's proof is 40.6k lines under `proof/Proof/` (plus its harness
pieces under `proof/Harness/`).

**State (2026-11-23, evening): Go, translation and every initializer done (the kit's and the twelve
programs' `PkgTable`s build); the foundation's first five files are ported (`Dsverify/Proof/rabia/
Core/{Model,Protocol,Ghost,Proto,PkgState}.lean`, each checks with `etc/lean-check.py -a`); the
per-package proofs, the kit's proofs and the statement are not.** Missing model pieces are
hypotheses named after the lab's specs (the coordinator's rule, 2026-11-23; list below): those of
the initializers are stated (`InitHyp` classes); the rest are listed, to be stated when a ported
proof needs them.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/rabia/` (module `rabia`, the fork's path): the fork's packages `internal/{config,message,queue,ledger,tcp,logger,system}`, `roles/server` (with `layers/{network,consensus,proxy}`), their tests, over the **real** zerolog v1.23.0, gogo/protobuf v1.3.2, go-redis v8.8.2 (the lab replaced these by its models, `harness/rpcmodel/{zerolog,gogoprotobuf,goredis}`); the kit `examples/rabianet` (rewritten onto remote, below) and its twelve commands `cmd/{orch,client0..5,server1..5}`. `go vet`, `go test ./...` pass (the deployment test 8 runs in a row, random configurations, 40-48 of 48 operations answered). Not copied: Rabia's client, controller, `main.go`, deployment scripts, `redis-raft`, the lab's `cmd/dsrig` |
| translation | `etc/goose.py` project `dsv-rabia` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/rabia/...`): rabia's packages with bodies; zerolog, gogo `proto`/`gogoproto`, go-redis (and its `internal/proto`) and `os/signal` **names only** with their types (`Dsverify/Code/**.toml`); remote and `net` the part `Net/`'s; lintest, porcupine, `bufio`, `container/heap`, `path`, `os`, `syscall` the main tree's; the rest Perennial's. Identical to the lab's translation but for the imports' module roots (checked file by file). Builds (`lake build Dsverify.GeneratedProof.rabia.examples.rabianet` and the twelve commands) |
| initializers | `etc/gen-init.py` `dsv_inits`: `DSV_PKGS`/`DSV_PROGRAMS` extended with rabia's packages and programs; `DSV_MAIN` (`bufio`, `container.heap`, `path`, `internal.bytealg`: their `Init.lean` generated into the part over `Net/`'s `PkgInitExt`, the last three with instances of the part's own, `Dsverify/Proof/{container/heap,path,internal/bytealg}/Base.lean`, since the main tree declares them in etcd's packages); `DSV_HYP_INITS` (dsv-vr's mechanism, `dsv_hyp_fix`, copied verbatim; math/rand as dsv-quepaxa: the names-only libraries' and math/rand's `wp_initialize'` are hypotheses, below); `SPECIAL['rabia.internal.config']` (`Conf`'s invariant) and `SPECIAL['rabia.internal.message']` (its errors, maps, descriptor and the `Register*` calls). Package facts: `Dsverify/Proof/**/Base.lean`, `True` but `config`'s |
| proofs | `Dsverify/Proof/rabia/Lib/OrdChan.lean` (the lab's ordered multi-producer channel); `Dsverify/Proof/rabia/Core/`: `Model` (pure: values, wire format, the key-value map `kv` restated from the lab's `Harness.Model`), `Protocol` (pure, unchanged), `Ghost` (the record of facts and `rabiaInv`; the client's update is remote's, below), `Proto` (the protocols onto `GooseLang/Ext/Net/Proto.lean`), `PkgState` (`confClaim`) |
| statement | not yet (`rabia_remote_robust`, `DistDeploy … → Robust [] …`, as `paxos_remote_robust`) |
| trust base | `etc/tcb-collections/dsv-rabia.txt` (roots `Dsverify/Proof/rabia/`, empty baseline) |

## What changed against the lab

- **The kit is remote's** (`examples/rabianet/kit.go`): twelve machines. The orchestrator (`Orch`)
  chooses the configuration at random and sends it to every client machine and to servers 1..N
  (`New`, the lab's configuration protocol unchanged: `sendConf`/`awaitConf`, five bytes and an
  acknowledgment), sleeps `StartMs`, then `remote.Check` of six clients' eight operations against
  the **key-value map with pending puts** (`Model`: per key the value and the puts of unknown outcome
  not yet seen; a get of a pending value takes it, once). Client machine `c` (`Client`) waits for the
  configuration, configures Rabia, connects its Rabia client endpoint, **then** `remote.ServeClient`
  (as paxos: `ServeClient`'s `newClient` is a persistent triple with precondition `True`, and
  client `c`'s configuration listener is one-shot); its operation (`Op`) is the lab's. Server
  machines are the lab's `serve`. The lab's driver, recorder, `check.KV`, `models.KV`, `remote.KV()`
  codec and porcupine axiom are gone; the codec (`Codec`) is the kit's.
- **Generator:** lintest's `gen` takes the client only, not the operation's index; Rabia's `Gen(c, j)`
  (a put then a get of one key per round) is served by `gens()`, a per-client atomic counter
  (`atomic.AddUint64(&next[c], 1)`): `genSpec`'s persistent triple holds with the counters in an
  invariant (each `Gen(c, j)` is a valid input for any `j`). Design finding for lintest/remote: a
  per-operation index in `gen` would remove the counter.
- **Addresses:** loopback `127.0.0.1:76xx` (proxies 7601-7605, network layer 7611-7615, servers'
  configuration 7621-7625, clients' requests 7631-7636, clients' configuration 7641-7646), constants;
  the lab's `10.77.0.x` hosts with shared port numbers are gone. `kit_test.go` runs each machine in a
  process of its own (the test binary re-executed), since Rabia's `config.Conf` is a process global.
- **Go source:** the fork's packages are byte-identical to the lab's fork. Lean rejects the tabs of
  Rabia's Go doc comments, which goose copies into `/-- … -/`: `etc/goose.py`'s
  `expand_comment_tabs` (project option, set for `dsv-rabia`) makes them four spaces in the
  translation, as the lab's `goose.sh` did (`notes/perennial-changes.md`, 2026-11-23). Upstream's two
  Redis tests skip without a Redis server (`redisUp`, in `proxy/redis_test.go`; the lab ran them
  against its go-redis model).
- **Translation:** `Proxy.redisExecuteCmd` names only (`Dsverify/Code/rabia/roles/server/layers/proxy.toml`):
  goose converts to go-redis's `internal/proto.RedisError` without importing it
  (`notes/perennial-changes.md`, 2026-11-23); the kit never uses Redis (`StorageMode` 0).
- **Names-only libraries bring generated `sorry -- axiomatized type` instances** into
  `Dsverify/GeneratedProof/` (zerolog 14, gogo `proto` 26, `gogoproto` 2, go-redis 88 over its
  chunks, `internal/proto` 4, `os/signal` 4): types of those libraries goose cannot translate (their
  own dependencies are not translated), none of them a type rabia's code stores. As in the main tree
  (CLAUDE.md, "The Goose translations"), no linked result should reach them; models of the libraries
  (the lab's cut-down copies) would remove them. **The gates accept them** (checked 2026-11-23): `etc/tcb-report.py` counts a `sorry`
  only when a root (a `Link`/`Results`/`MainLinked`) reaches it, and no gate greps for `sorry`; the
  main tree has 170 such files in `GeneratedProof/`, and `Net/GeneratedProof/net.lean` alone 168
  instances. The collection's `--check` will show any that a rabia result reaches.
- **The client's update is remote's** (`Core/Ghost.lean`, `opAU`): the lab's atomic update at
  the harness's `clientN` (`AU <{∃∃ σ, kvState γ σ}> @ clientN, ∅ <{…}>`) is the one-shot fancy
  update `|={cliE, ∅}=> ∃ σ, kvState γ σ ∗ ∀ σ' o, kvState γ σ' ∗ ⌜step⌝ -∗ |={∅, cliE}=> Q σ σ' o`,
  `cliE = ⊤ \ rabiaE`, `rabiaE = ↑rabiaR` (`rabiaR = nroot.@"rabia"`): remote's `lin` with
  `RBase.Eop = rabiaE` (as dsv-vr's `AUof`/`vsrE`). Every invariant open when an update is fired
  (rabiaInv, now `rabiaR.@"inv"`; the broadcast logs', the established connections', `Conf`'s, and,
  when ported, the servers' key sets' `srvKeysN`) is below `rabiaR`. The lab's hypotheses
  `clientN ⊆ E` read `cliE ⊆ E` (textually; `cliE_disj_of_sub` gives the lab's disjointness facts
  `clientN ## N` for `N` below `rabiaR`); `commit_batch` shrinks `E` to `cliE` around the update
  (`fupd_mask_subseteq`). The ported Ghost's other proofs are unchanged.
- **Protocols onto Net's vocabulary** (`Core/Proto.lean`): `Proto GF`, `addrProto`, `sentLb` are
  `GooseLang/Ext/Net/Proto.lean`'s (connections are numbers: `estab`'s `cid : Nat`; `addrTok` is
  persistent, so the shares' address tokens are mere validity facts). Addresses `kitAddr n =
  "127.0.0.1:76" ++ digits2 n`; the table lemmas (`addrP_proxy`, …) by `kitAddr_ne` on the port's
  digits. `cliAddr c` is remote's serve address (its protocols remote's, set by the top level as
  paxos's `clientAddrs`), not the lab's never-listened `:7000` claim address.
- **Package states** (`Core/PkgState.lean`, `internal/config/Base.lean`): no record of package
  states (the generated initializers prove each package's `Base.lean` fact). `config`'s fact is
  `inv confN confInv` with `confInv = Conf ↦ zero ∨ ∃ σ, ownGoState σ`; a machine's one `configure`
  claims `Conf` with its package state (`confClaim`), which the top level's boot must hand to `main`
  after the initialization (paxos's `wp_boot` drops `ownInitializing`; rabia's keeps it). The lab's
  third state (a client node's claim with its unset address protocol, told apart by IP) is gone.
  `message`'s fact is `True` for now (the lab's `msgState`: added with the proof that needs it, as
  dsv-vr's weaker facts).
- **Hypotheses of the initializers** (`InitHyp`, dsv-vr's mechanism): `Dsverify/Proof/<pkg>/Init.lean`
  for `github_com/rs/zerolog`, `github_com/gogo/protobuf/{proto,gogoproto}`,
  `github_com/go_redis/redis/v8` (and `internal/proto`), `os/signal`, `math/rand` is a class
  `InitHyp GF : Prop` holding the package's `wp_initialize'`; every generated theorem above takes it
  as an instance (`variable [<pkg>.InitHyp GF]`). gogo `proto`'s class also holds the specs of
  `RegisterEnum`/`RegisterType`/`RegisterFile` (the coordinator's decision: `message`'s init calls
  them; `RegisterEnum`'s spec is true of a name's first registration, the only one per program).
  The generated `os/signal`/library initializers with `initFuncsOk` axioms are gone: no axiom under
  `Dsverify/` (`path/Init.lean` mentions `opaqueInitsOk` in its doc only).
- **OrdChan:** the channel idioms' atomic updates are crash-aware at Perennial `9c3b81f3`
  (`notCrashed ={⊤,∅}=∗ notCrashed ∗ …`): `ncfupd_of_fupd` at the start of each update's proof.

## The hypotheses (missing model pieces; named after the lab's specs)

**Stated** (classes, instance arguments of every theorem above them, up to the closed statement):
- `github_com.rs.zerolog.InitHyp`, `github_com.gogo.protobuf.gogoproto.InitHyp`,
  `github_com.go_redis.redis.v8.InitHyp`, `github_com.go_redis.redis.v8.internal.proto.InitHyp`,
  `os.signal.InitHyp`, `math.rand.InitHyp` (each the package's `wp_initialize'`, the lab's
  `<pkg>.init.spec`);
- `github_com.gogo.protobuf.proto.InitHyp` (`proto.init.spec`, and `RegisterEnum`, `RegisterType`,
  `RegisterFile`).

**To state** when a ported proof needs them (a section variable or a premise with this name, never
an axiom; the closed statement carries it until the shared change (bufio, #24) or a model lands):

- **bufio** (one shared change on #24; the main tree translates only `NewReader(Size)`,
  `Reader.Read` and helpers): the lab's `Harness/Proof/bufio/` — `bufio.wp_NewReaderSize`,
  `bufio.wp_NewWriterSize`, `bufio.wp_Write` (`(*Writer).Write`), `bufio.wp_Flush`, `bufio.wp_ReadFull`
  (`io.ReadFull` over a `*bufio.Reader`), and its connection laws `readerOk_conn`, `writerOk_conn`,
  `readsOk_conn`, `bufioReadsOk` (a `bufio.Reader`/`Writer` over a `net.Conn` with `recvTok`/`sendTok`).
  Used by `internal/message` (`BufWrite`, `BufRead`, `WriteFlush`, `MarshalWriteFlush`,
  `ReadUnmarshal`) and `internal/tcp` (`GetReaderWriter`, the send and receive loops).
- **zerolog** (real v1.23.0 names only; the lab's `rpcmodel/zerolog`): `github_com.rs.zerolog.New`,
  `SetGlobalLevel`, `ParseLevel` (the lab's `ParseLevel.warn`), `Logger.Warn`, `Logger.Debug`,
  `Event.Msg`, `Event.Int`, `Event.Uint`, `Event.Bool`, `Event.Float`.
- **gogo/protobuf**: nothing more (the generated `Marshal`/`Unmarshal` code is rabia's own).
- **os/signal** (names only here; the lab's `Harness/Proof/os/signal.lean`): `os.signal.Notify`,
  `signal.Stop` (`internal/system.SigListen`).
- **math/rand** (Perennial's, names only; the main tree proves `Float64`/`Int63n` only):
  `math.rand.New`, `math.rand.NewSource`, `math.rand.Rand.Intn` (the consensus coin),
  `math.rand.Intn` (the kit's `choose`).
- **log** (Perennial's model has `Println`, no spec): `log.wp_Println` (the kit's `send`).

## State, in detail

- Built (`lake build`): the translation; every `Init.lean` of the part's rabia packages and the
  libraries' hypothesis files, `rabianet`'s and the twelve programs' `PkgTable.lean`
  (`lake build Dsverify.Proof.rabia.examples.rabianet.Init` plus the twelve
  `…cmd.<n>.PkgTable`). `gen-init.py --check` and `goose.py --check` up to date.
- Checked with `etc/lean-check.py -a` (not yet `lake build`): `Lib/OrdChan`, `Core/{Model,
  Protocol,Ghost,Proto,PkgState}`, `internal/config/{Base,Init}`.
- Not ported: the lab's `Proof/Rabia/{Chans,Start,StartAlloc,GoalSpec}.lean` (`Chans` needs
  `internal/ledger/Spec`; `Start`/`StartAlloc` become the top level's allocation, `GoalSpec` the
  statement) and every per-package file under the lab's `Proof/rabia/` (about 35k lines).

## Next steps

1. The leaves by editing the lab's files (imports `Proof.Rabia.*` → `Dsverify.Proof.rabia.Core.*`,
   `NetConn` → `Net`, `[HasExt netConnExt]` → `[HasExt netExt] [π : NetProtoGS]`, the lab's
   `inits.<pkg>.init.spec` and `pkgStates` → the generated `wp_initialize'`/`Base.lean` facts,
   `(↑dsverify_lab.harness.clientN : CoPset)` → `cliE`, `ndot nroot "rabia_…"` → `ndot rabiaR "…"`):
   queue, ledger (`Pure`, `Sorting`, `Spec`, the `Slot__*`), then `Core/Chans`.
2. message (wire format; the bufio hypotheses; `message`'s fact `msgState` into its `Base.lean` and
   `SPECIAL[...]['finish']`, from the lab's `message/initialize.lean`'s end), tcp (the transport:
   `net.Conn` specs + `Proto.lean`'s laws `write_acc`/`read_au`/`dial_au`/`accept_au`, as paxos's
   `NetProof`), network, consensus (`srvKeysN` below `rabiaR`), proxy, server.
3. The kit: `Configure` (`confClaim` in place of the lab's client claim), `NewClient`, `Op` (its
   update is `opAU`: `lin_opAU : remote.lin (kvR γ) i Φ ⊢ opAU γ i (fun _ _ o => Φ o)`, with `kvR`
   the kit's `RBase` over `kvState` and `Eop = rabiaE`, as dsv-vr's `kvR`/`lin_AUof`), `Server`, the
   porcupine model's proof (`Model`/`step` of `kit.go` against linkv's pending-writes map, as dsv-vr's
   and dsv-paxos's `ModelSet`/`ModelProof`), `gens()`'s `genSpec`.
4. The mains, `TopLevelDefs`, `TopLevelRobustness` (`rabia_remote_robust`, with a `wp_boot` that
   hands the package state to `main`; the stated hypotheses as premises), `#print axioms`, the
   collection's baseline.
