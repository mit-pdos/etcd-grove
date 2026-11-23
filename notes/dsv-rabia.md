# dsv-rabia: dsverify-lab's rabia kit on the net extension (phase 6)

Branch `dsv-rabia` (2026-11-23, off `origin/dsv-paxos` `e3eaf5cd0d`), worktree
`/shared/etcd-grove-dsvrabia`. Plan: `notes/dsverify-net-port-plan.md`, phase 6; pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/rabia/` (read only):
run **`rabia-r1wake-1`**, proof `2a8c0fc` (tag `final`), fork `ef2a93b` (R1-wake: the executor waits on
a slot's wake channel), Perennial `3afd77e35`; the lab's statement `dsv_goal_check : SafeDist
(orchNode :: clientNodes ++ serverNodes) rabiaNetCfg`, axioms Lean's three and porcupine's
`CheckOperations.wp_proof`. The lab's proof is 40.6k lines under `proof/Proof/` (plus its harness
pieces under `proof/Harness/`).

**State (2026-11-23): Go, translation and most initializers done; the proof port has started (one
library file).** Missing model pieces are to be taken as hypotheses named after the lab's specs (the
coordinator's rule, 2026-11-23; list below); none is taken yet, because no proof that needs one is
ported yet.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/rabia/` (module `rabia`, the fork's path): the fork's packages `internal/{config,message,queue,ledger,tcp,logger,system}`, `roles/server` (with `layers/{network,consensus,proxy}`), their tests, over the **real** zerolog v1.23.0, gogo/protobuf v1.3.2, go-redis v8.8.2 (the lab replaced these by its models, `harness/rpcmodel/{zerolog,gogoprotobuf,goredis}`); the kit `examples/rabianet` (rewritten onto remote, below) and its twelve commands `cmd/{orch,client0..5,server1..5}`. `go vet`, `go test ./...` pass (the deployment test 8 runs in a row, random configurations, 40-48 of 48 operations answered). Not copied: Rabia's client, controller, `main.go`, deployment scripts, `redis-raft`, the lab's `cmd/dsrig` |
| translation | `etc/goose.py` project `dsv-rabia` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/rabia/...`): rabia's packages with bodies; zerolog, gogo `proto`/`gogoproto`, go-redis (and its `internal/proto`) and `os/signal` **names only** with their types (`Dsverify/Code/**.toml`); remote and `net` the part `Net/`'s; lintest, porcupine, `bufio`, `container/heap`, `path`, `os`, `syscall` the main tree's; the rest Perennial's. Identical to the lab's translation but for the imports' module roots (checked file by file). Builds (`lake build Dsverify.GeneratedProof.rabia.examples.rabianet` and the twelve commands) |
| initializers | `etc/gen-init.py` `dsv_inits`: `DSV_PKGS`/`DSV_PROGRAMS` extended with rabia's packages and programs; `DSV_MAIN` (`bufio`, `container.heap`, `path`, `internal.bytealg`: their `Init.lean` generated into the part over `Net/`'s `PkgInitExt`, the last three with instances of the part's own, `Dsverify/Proof/{container/heap,path,internal/bytealg}/Base.lean`, since the main tree declares them in etcd's packages); `SPECIAL['rabia.internal.config']` (`Conf`'s type). Package facts: `Dsverify/Proof/**/Base.lean`, all `True` for now |
| proofs | `Dsverify/Proof/rabia/Lib/OrdChan.lean` (the lab's ordered multi-producer channel, ported: checks with `etc/lean-check.py`) |
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
- **OrdChan:** the channel idioms' atomic updates are crash-aware at Perennial `9c3b81f3`
  (`notCrashed ={⊤,∅}=∗ notCrashed ∗ …`): `ncfupd_of_fupd` at the start of each update's proof.

## The hypotheses the port will take (missing model pieces; named after the lab's specs)

None is used yet. When a ported proof needs one, it is a hypothesis (a section variable or a premise
of the `wp_proof`) with this name, never an axiom; the closed statement then carries it until the
shared change (bufio, coordinator, #24) or a model lands.

- **bufio** (one shared change on #24; the main tree translates only `NewReader(Size)`,
  `Reader.Read` and helpers): the lab's `Harness/Proof/bufio/` — `bufio.wp_NewReaderSize`,
  `bufio.wp_NewWriterSize`, `bufio.wp_Write` (`(*Writer).Write`), `bufio.wp_Flush`, `bufio.wp_ReadFull`
  (`io.ReadFull` over a `*bufio.Reader`), and its connection laws `readerOk_conn`, `writerOk_conn`,
  `readsOk_conn`, `bufioReadsOk` (a `bufio.Reader`/`Writer` over a `net.Conn` with `recvTok`/`sendTok`).
  Used by `internal/message` (`BufWrite`, `BufRead`, `WriteFlush`, `MarshalWriteFlush`,
  `ReadUnmarshal`) and `internal/tcp` (`GetReaderWriter`, the send and receive loops).
- **zerolog** (real v1.23.0 names only; the lab's `rpcmodel/zerolog`): `github_com.rs.zerolog.New`,
  `SetGlobalLevel`, `ParseLevel` (the lab's `ParseLevel.warn`), `Logger.Warn`, `Logger.Debug`,
  `Event.Msg`, `Event.Int`, `Event.Uint`, `Event.Bool`, `Event.Float`, `zerolog.init`.
- **gogo/protobuf** (real v1.3.2 names only; the lab's `rpcmodel/gogoprotobuf`): `proto.init`,
  `gogoproto.init`, and `proto.RegisterType`/`RegisterEnum`/`RegisterFile`, which `message`'s
  initializer calls (its `init.«0»`/`init.«1»`).
- **go-redis** (real v8.8.2 names only): `v8.init` only (no proof calls go-redis).
- **os/signal** (names only here; the lab's `Harness/Proof/os/signal.lean`): `os.signal.Notify`,
  `signal.Stop`, `os.signal.init` (`internal/system.SigListen`).
- **math/rand** (Perennial's, names only; the main tree proves `Float64`/`Int63n` only):
  `math.rand.New`, `math.rand.NewSource`, `math.rand.Rand.Intn` (the consensus coin),
  `math.rand.Intn` (the kit's `choose`).
- **log** (Perennial's model has `Println`, no spec): `log.wp_Println` (the kit's `send`).

## State, in detail

- Built: the translation; the `Init.lean` of config, logger, system, go-redis, `os/signal`, bufio,
  `container/heap` (and what they import).
- **`internal/message`'s `Init.lean` does not build**: gen-init leaves `TODO` for the types of its
  eleven package variables (`SPECIAL['rabia.internal.message']['alloc_types']`, to add), its translated
  initializers (`errors.New`, `fmt.Errorf` errors, the `MsgType` maps, the file descriptor's slice)
  need the generator's `newvars`/`custom` steps, and `init.«0»`/`init.«1»` call gogo proto's
  `Register*`, whose specs are hypotheses (above): a generated `wp_initialize'` cannot take a
  hypothesis, so this initializer (and every package and program above it: queue, ledger, tcp,
  network, consensus, proxy, server, the kit, the twelve `PkgTable`s) waits for a decision: a
  hand-written `Init.lean` for message with the hypotheses as premises (gen-init's `ASSUMED`
  mechanism, or the part's `custom`), or the gogo proto model.
- The package facts are `True` for now; the lab's are `config`'s `inv confN confInv` (the `Conf`
  points-to, claimed by a client node or a server's boot) and `message`'s `msgState`
  (`Proof/Rabia/PkgState.lean`): to be redesigned with the kit (remote's machines, no lab
  `NetConn` claims).
- Ported: `Lib/OrdChan.lean`. Everything else of the lab's `Proof/` imports the lab's foundation
  (`Proof/Rabia/{Model,Protocol,Ghost,Proto,PkgState,Chans}.lean`), which rests on the lab's KV model
  (`Harness/Model`), its `NetConn` vocabulary and its package states; those are the next files.

## Next steps

1. The foundation: `Model.lean` onto the kit's model (`State`/`Entry`, pending puts) and remote's
   pending library (as paxos's `opAU`/`woR`), `Protocol.lean` (pure), `Ghost.lean`, `Proto.lean` onto
   `GooseLang/Ext/Net/Proto.lean`'s vocabulary (`addrProto`, `sendTok`/`recvTok`, `recvTokL`),
   `PkgState.lean` onto the generated initializers' package facts (`Base.lean`).
2. The leaves (queue, ledger, consensus/ledger `Pure`, `Sorting`), then message (wire format; bufio
   hypotheses), tcp (the transport: `net.Conn` specs + `Proto.lean` laws, as paxos's `NetProof`),
   network, consensus, proxy, server, by editing the lab's files.
3. message's initializer (above); the kit's proofs (`Orch`, `Client`, `Server`, the model's proof as
   paxos's `ModelSet`/`ModelProof`); the mains and links; `rabia_remote_robust` and its
   `TopLevelRobustness` files; `#print axioms`; the collection's baseline.
