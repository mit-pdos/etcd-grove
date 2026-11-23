# dsv-rabia: dsverify-lab's rabia kit on the net extension (phase 6)

Branch `dsv-rabia` (2026-11-23, off `origin/dsv-paxos` `e3eaf5cd0d`), worktree
`/shared/etcd-grove-dsvrabia`. Plan: `notes/dsverify-net-port-plan.md`, phase 6; pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/rabia/` (read only):
run **`rabia-r1wake-1`**, proof `2a8c0fc` (tag `final`), fork `ef2a93b` (R1-wake: the executor waits on
a slot's wake channel), Perennial `3afd77e35`; the lab's statement `dsv_goal_check : SafeDist
(orchNode :: clientNodes ++ serverNodes) rabiaNetCfg`, axioms Lean's three and porcupine's
`CheckOperations.wp_proof`. The lab's proof is 40.6k lines under `proof/Proof/` (plus its harness
pieces under `proof/Harness/`).

**State (2026-11-23, third agent, ~11:30): done.** `rabia_remote_robust :
rabia_remote_robust.spec` (`Dsverify/Proof/rabia/examples/rabianet/TopLevelRobustness.lean`;
statement `Dsverify/Spec/rabia/examples/rabianet/TopLevelRobustness.lean`): twelve machines
(`TopLevelDefs.system`) deployed at `rabiaKitAddrs` (`DistDeploy`) are `Robust [] … (2^63)`, for
every Go semantics with the twelve programs' `Assumptions`, `net.FieldAssumptions`,
`go.BasicIntoValInj` and these **visible premises** (each quantified over the machine's heap,
`heapAt G L`): the `InitHyp`s of zerolog, gogo `proto`, `gogoproto`, go-redis v8, `os/signal`,
`math/rand` (go-redis' `internal/proto` `InitHyp` is not needed: no initializer reaches it),
`github_com.gogo.protobuf.proto.Hyps` (the three `Register*` calls), `github_com.rs.zerolog.Hyps`,
`math.rand.Hyps`, and the environment assumption `os.signal.NoSignals` (SIGINT/SIGTERM): ten in all
(after review #24, below; `log.Println` is proved, so there is no `log.Hyps`). `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
`lake build` of the top module (2937 jobs): ok. `etc/theorem-loc.py --file … rabia_remote_robust`
counts every one of these classes as a statement premise (`--list-tcb`: `stmt class …InitHyp`, …,
`os.signal.NoSignals`, `NotifyQuiet.spec`). Not run: `etc/tcb-report.py --check` of the collection
(it wants a full `lake build`, which the shared host's rules forbid here); the baseline is written
by hand from `#print axioms`. Files: the kit's `Kit`, `ConfProof`, `ConnReadFull`, `GhostAux`,
`ClientProof`, `ServerProof`, `OrchProof`, `KitModel`, `ModelSet`, `ModelProof`, `CodecProof`,
`Mains`, `Linked`, `TopLevelRobustness`; the start `Core/{StartAlloc,Start}`; tcp, the layers and the
server as above. **zerolog's names-only translation now sees `io`** (`Dsverify/Code/github_com/rs/
zerolog.toml`): `Logger`'s field `w : LevelWriter` embeds `io.Writer`, and without `io` goose
axiomatized the type with a `sorry` instance, which the server's proofs reached (the claim below
that no linked result reaches those instances was wrong for this one; the remaining ones, e.g.
`encoder`, `BurstSampler`, `syncWriter`, are not reached: `#print axioms` is clean).

**Landing prep (2026-11-23, fourth agent):** merged `lean` `e20bbac22f` (Perennial `c95e92207`,
checkout `/shared/perennial-c95e92207`). The server's `Link.lean` is in `EtcdGrove.dsvrabia` (as
paxos's: `etc/proof_roots.py`'s `namespace()` is the Links' common prefix; in
`Perennial.rabia.roles.server` it shrank to `Perennial.` and renamed every trust-base entry).
`lake build` of the top module and `#print axioms` (Lean's three) redone at that pin.
**Import tiers (2026-11-23, fifth agent):** `etc/tier-check.py --check` passes with no new baseline
entry (it refused 106 edges: 88 proof->proof, 14 defs->proof, 4 spec->proof). Every proof file now
sees its callees through their specs only, taken as hypotheses, and the two linking modules compose
them: `roles/server/Link.lean` (bottom up: `bufio`'s and `message`'s framing, tcp's endpoints, the
queue and the ledger, the three layers, `wp_ServerInit`/`wp_Prologue`/`wp_ServerMain`) and
`examples/rabianet/Linked.lean` (`kitNetDeps`, `wp_configure_linked`, `wp_waitConf`, `wp_New`,
`wp_newClient`, `wp_Server`/`wp_Client`/`wp_Orch`). What moved:
- the library classes' `wp_proof`s (`zerolog`, `log`, `math/rand`, `os/signal`) are in
  `HypsLinked.lean` beside each `Spec.lean` (linking tier, imported by nothing yet); a proof file uses
  the class's field (`github_com.rs.zerolog.Hyps.Event_Msg`, `math.rand.Hyps.Intn`, ...), so the
  `Spec.lean`s are defs and the statement imports no proof;
- a hypothesis-taking `X.wp_of` became `X.wp_proof` and the old composing `X.wp_proof` moved to the
  Link (`ServerInit`, `Server.{Prologue,ServerMain,TerminalLogger}`, `ProxyInit`, `Proxy.{Prologue,
  KVSExecutor}`, `NetworkInit`, `Network.{Prologue,MsgRouter,MsgSerializer}`, `BufWrite`, `BufRead`,
  `WriteFlush`, `{Command,Msg}.{MarshalWriteFlush,ReadUnmarshal}`, `Msg.Unmarshal`);
  `ExecutorMain.lean`/`MsgHandlerFinal.lean` merged into `ExecutorFinal.lean`/`MsgHandler.lean`;
- structures of callee specs, as consensus's `ExDeps`: `tcp/Basics.lean`'s `TcpDeps` (`net`'s
  connection calls, `bufio`'s constructors, `message`'s framing; every tcp connection lemma takes
  `D`), `examples/rabianet/KitSpecs.lean`'s `KitNetDeps` (`ConfProof`'s network calls,
  `io.ReadFull.specLt`, `Config.CalcConstants`);
- specs and lemmas out of proof files into defs: `message/SpecInternal.lean` (`BufRead.specB`,
  `BufWrite.specTooLong`), `message/UnmarshalLemmas.lean`, `examples/rabianet/KitSpecs.lean`
  (the address functions' and `attempt`'s specs, `Client.spec`/`Orch.spec`/`Server.spec`,
  `range_map_get`, `take_peers`, `cfgIs_ok'`, `conf_claim`), `ModelLemmas.lean` (out of
  `ModelProof.lean`), `ConnRead.lean` (`io.*.specLt`, `wp_connReadFull` over its two callees'
  specs; `ConnReadFull.lean` keeps the two `wp_proofLt`s).
`lake build` of the top module and `#print axioms rabia_remote_robust` (Lean's three) redone after
it; all 230 modules under `Dsverify/{Proof,Spec}/rabia` and the libraries' build; `gen-init.py
--check` and `goose.py --check --project dsv-rabia` pass.

**Review #24 (2026-11-23, sixth agent):** upamanyus's review of `1a7990d86b` ("close; fix 1-3,
4-6 if cheap"): the premises claimed more than the real libraries do. Now:
1. `os.signal.NotifyQuiet.spec` requires `sig ↦*{dq} quietSigs` (`[SIGINT, SIGTERM]` as the
   `os.Signal` values `SigListen`'s literal makes) and gives it back: Go's `Notify(c)` with no
   signals relays every signal, the runtime's `SIGURG` included. `NoSignals` stays the environment
   assumption, over exactly those two. `os.signal.Hyps` (`Notify`, `Stop`) was unused: removed.
   (2026-11-23, dsv-swiftpaxos review fix 3: one `NotifyQuiet.spec (sigs : List os.Signal)`, with
   `sigs ≠ []`, and one class `NoSignals sigs`, shared with swiftpaxos (`[SIGUSR1]`); rabia's
   premise is `os.signal.NoSignals quietSigs`.)
2. gogo `proto`'s `InitHyp` holds only its `wp_initialize'` (`etc/dsv/README.md`'s rule); the three
   `Register*` specs are a premise of their own, `github_com.gogo.protobuf.proto.Hyps`
   (`proto/Spec.lean`): each holds the package state `ownGoState σ` (registrations are made by
   initializers, one at a time; with `True` they claimed concurrent calls safe), and `RegisterEnum`
   is required to be called inside `message`'s initialization, once: stated for `"message.MsgType"`
   only, it consumes the points-to of `message`'s `MsgType_value`, which only `message`'s
   initializer holds (it allocates it). `message`'s generated `Init` unpacks `Hown`
   (`EtcdGrove.ownInitLb`) for the calls and repacks it (`etc/dsv/rabia.py`'s `after`; its
   `vars`/`imports` give every package above `message` the instance).
3. zerolog: `Logger.level.spec ownEvent m` requires `l ≠ null` and returns the event's token
   `ownEvent e`, only for the five levels whose `Msg` neither panics nor exits; the field methods
   take and return the token, `Msg` consumes it (an event is not safe for concurrent use). The token
   is abstract: `Hyps.events : ∃ ownEvent, EventSpecs GF ownEvent`; the proofs use the chosen
   `zerolog.ownEvent`/`eventSpecs` (`Classical.choose`: with an `obtain`ed predicate, `wp_apply` of
   `TerminalLogger`'s event calls aborted silently, leaving a `sorry` the build only warned about). The proxy's `proxyFields`
   carries `⌜structFieldRef Proxy "Logger" p ≠ null⌝` (from `ProxyInit`'s field points-to) for
   `KVSExecutor`'s `p.Logger.Debug()`; `TerminalLogger` has its local's points-to.
4. math/rand: `NewSource` gives a source token `isSource src`, `New` takes it and gives a `Rand`
   token `ownRand r`, `Rand.Intn` takes the latter (`Hyps.rands : ∃ isSource ownRand, RandSpecs`):
   a zero `Rand` (nil source) is not covered. The consensus's `coinOk`/`exCoinOk` hold `∃ R, R r ∗
   ⌜Rand.Intn.spec R⌝` instead of `r ↦ v`.
5. `log.Hyps` is gone: `log.Println.wp_proof` (`Net/Proof/log/Println.lean`, Net's, shared with the epaxos kit; rabia's own copy
   `Dsverify/Proof/log/` was dropped, its names clashing with Net's when both kits are loaded) is proved from
   Perennial's trusted `log.Println.impl` (it does nothing), its spec requiring `fmt.ArgsWf` of the
   arguments as Perennial's `log.Printf.spec` does (`send` passes one string); `KitNetDeps.println`.
The statement's premises are now: the six `InitHyp`s, `proto.Hyps`, `zerolog.Hyps`, `math.rand.Hyps`,
`os.signal.NoSignals`. Not done (optional in the review): moving `sentLb_prefix`, `sentLb_agree`,
`recvTokL_sentLb` into `GooseLang/Ext/Net/Proto.lean` (a base-tier change that rebuilds every
module over `Proto.lean`; a follow-up).

**Kit Go changes (third agent and its agents):** `Sys` has a mutex, `Op` locks it (`op1` the body);
`op1` answers unknown once the sequence numbers reach `SeqBudget = 2^29` (`proxyP`'s budget;
remote serves unboundedly many operations); the model's `Entry` has `Old` (puts overwritten while
pending, `cat`): the earlier `State` could not represent the pending set exactly (two histories with
equal states allowed different configurations, so `Equal`'s spec was false); `gens()` answers
`Gen(c, 0)` for `c` outside `[0, NC)` (`genSpec` quantifies every id). `go test` passes.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/rabia/` (module `rabia`, the fork's path): the fork's packages `internal/{config,message,queue,ledger,tcp,logger,system}`, `roles/server` (with `layers/{network,consensus,proxy}`), their tests, over the **real** zerolog v1.23.0, gogo/protobuf v1.3.2, go-redis v8.11.5 (the fork pins v8.8.2; bumped 2026-11-23, issue #24, so that rabia and QuePaxa share one go-redis translation, the version QuePaxa needs: below) (the lab replaced these by its models, `harness/rpcmodel/{zerolog,gogoprotobuf,goredis}`); the kit `examples/rabianet` (rewritten onto remote, below) and its twelve commands `cmd/{orch,client0..5,server1..5}`. `go vet`, `go test ./...` pass (the deployment test 8 runs in a row, random configurations, 40-48 of 48 operations answered). Not copied: Rabia's client, controller, `main.go`, deployment scripts, `redis-raft`, the lab's `cmd/dsrig` |
| translation | `etc/goose.py` project `dsv-rabia` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/rabia/...`): rabia's packages with bodies; zerolog, gogo `proto`/`gogoproto`, go-redis (and its `internal/proto`) and `os/signal` **names only** with their types (`Dsverify/Code/**.toml`); remote and `net` the part `Net/`'s; lintest, porcupine, `bufio`, `container/heap`, `path`, `os`, `syscall` the main tree's; the rest Perennial's. Identical to the lab's translation but for the imports' module roots (checked file by file). Builds (`lake build Dsverify.GeneratedProof.rabia.examples.rabianet` and the twelve commands) |
| initializers | `etc/gen-init.py` `dsv_inits`: `DSV_PKGS`/`DSV_PROGRAMS` extended with rabia's packages and programs; `DSV_MAIN` (`bufio`, `container.heap`, `path`, `internal.bytealg`: their `Init.lean` generated into the part over `Net/`'s `PkgInitExt`, the last three with instances of the part's own, `Dsverify/Proof/{container/heap,path,internal/bytealg}/Base.lean`, since the main tree declares them in etcd's packages); `DSV_HYP_INITS` (dsv-vr's mechanism, `dsv_hyp_fix`, copied verbatim; math/rand as dsv-quepaxa: the names-only libraries' and math/rand's `wp_initialize'` are hypotheses, below); `SPECIAL['rabia.internal.config']` (`Conf`'s invariant) and `SPECIAL['rabia.internal.message']` (its errors, maps, descriptor and the `Register*` calls). Package facts: `Dsverify/Proof/**/Base.lean`, `True` but `config`'s |
| proofs | `Dsverify/Proof/rabia/Lib/OrdChan.lean` (the lab's ordered multi-producer channel); `Dsverify/Proof/rabia/Core/`: `Model` (pure: values, wire format, the key-value map `kv` restated from the lab's `Harness.Model`), `Protocol` (pure, unchanged), `Ghost` (the record of facts and `rabiaInv`; the client's update is remote's, below), `Proto` (the protocols onto `GooseLang/Ext/Net/Proto.lean`), `PkgState` (`confClaim`) |
| statement | `rabia_remote_robust` (`Dsverify/Spec/rabia/examples/rabianet/TopLevelRobustness.lean`, `DistDeploy … → Robust [] …`, as `paxos_remote_robust`), proved in `Dsverify/Proof/rabia/examples/rabianet/TopLevelRobustness.lean` |
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
  `Dsverify/GeneratedProof/` (zerolog 14, gogo `proto` 26, `gogoproto` 2, go-redis 102 over its
  chunks (88 at v8.8.2), `internal/proto` 4, `os/signal` 4): types of those libraries goose cannot translate (their
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
  as an instance (`variable [<pkg>.InitHyp GF]`). Each asserts only that the initializer runs
  without panicking; the specs of gogo `proto`'s `RegisterEnum`/`RegisterType`/`RegisterFile`, which
  `message`'s init calls, are the separate premise `proto.Hyps` (review #24, above; until then fields
  of `proto.InitHyp` with precondition `True`).
  The generated `os/signal`/library initializers with `initFuncsOk` axioms are gone: no axiom under
  `Dsverify/` (`path/Init.lean` mentions `opaqueInitsOk` in its doc only).
- **OrdChan:** the channel idioms' atomic updates are crash-aware at Perennial `9c3b81f3`
  (`notCrashed ={⊤,∅}=∗ notCrashed ∗ …`): `ncfupd_of_fupd` at the start of each update's proof.
- **go-redis v8.11.5, not the fork's v8.8.2** (2026-11-23, issue #24): the QuePaxa kit builds with
  go-redis v8.11.5 and cannot take v8.8.2 (v8.8.2 imports otel v0.19's `metric/global`, which the otel
  v1 that QuePaxa's grpc v1.84 requires no longer has), and two goose projects cannot own one module
  path, so this project's go.mod moved to v8.11.5 (go.mod and go.sum only, the fork's code unchanged:
  `go vet`, `go test ./...` pass, `TestDeployment` included) and the one names-only go-redis
  translation in `Dsverify/` is v8.11.5's, the version both kits run. Rabia reaches go-redis only in
  `roles/server/layers/proxy/redis.go` (`redis.NewClient`, `redis.Options`, `redis.Nil`), all
  present in v8.11.5. Before, QuePaxa's theorem (`github_com.go_redis.redis.v8.InitHyp`) named
  v8.8.2's translation while v8.11.5 ran.

## Design findings

- **remote's `ServeClient`** (as paxos's finding): its `newClient` triple has precondition `True`, so
  the system it returns can hold no exclusive resource; rabia's `Op` mutates its `Sys` (`next`, the
  send channel's single producer), so the kit's `Sys` got a `sync.Mutex` and `Op` locks it (`op1` is
  the body). `remote.Serve` runs one operation at a time, so the lock never waits in practice.
- **bufio's `NewWriterSize` asks `□ Q W` of what was already written** (revised bufio): a writer
  made over a fresh connection needs the protocol to allow the empty stream; rabia's framed
  protocols (`proxyP`, `proxyQ`, `netP`) now do outright (the proxy makes its writer before it has
  read the client's handshake, on which `proxyQ` depends).
- **A connection read through a `*bufio.Reader` gives its protocol fact one step later**
  (`net.connReader_proto`): each frame's fact costs a later credit (`wp_auto_lc`).
- **Missing laws of `GooseLang/Ext/Net/Proto.lean`** (proved here from its definitions, in
  `tcp/ProtoLemmas.lean`): `sentLb_prefix`, `sentLb_agree`, `recvTokL_sentLb`.
- **`os/signal`**: the coordinator's decision: the **environment assumption**
  `os.signal.NoSignals` (nobody sends SIGINT or SIGTERM to the deployment's processes), a class of
  its own, which `SigListen` takes: `NotifyQuiet.spec`, `Notify(c, SIGINT, SIGTERM)` (its signal
  slice `↦*{dq} quietSigs`, review #24) on a non-`nil` channel, with no requirement on the channel's
  protocol, so `SigListen`'s signal branch is unreachable. Go's `Notify` relays the listed signals
  only (with none listed, every signal, the runtime's own `SIGURG` included), so the assumption
  is about those two. No library spec of `os/signal` is used (the earlier `os.signal.Hyps`,
  `Notify` with `□ ∀ s, P s` and `Stop`, was unused and is gone). **For the user:** the honest
  alternative (no environment assumption) costs a
  proof that every routine selecting on a server's `Done` channel is safe once `Done` is closed
  (SigListen closes it on a signal): the tcp endpoints' loops, the layers' routines, `ServerMain`,
  `TerminalLogger`, which today treat `Done` as never closed (safety only, not liveness).

- **Linked packages vs the facts used** (the coordinator's check from dsv-vr's finding 7, 2026-11-23):
  the rabia package facts that are not `True` are `internal/config`'s (`confInv`) and
  `internal/message`'s (`msgFact`: its two `errors.New` globals); both packages are imported by the
  kit (`kit.go` imports `config`, `message`, `tcp`, `roles/server`), so every one of the twelve
  programs links them, and each program's `PkgTable.lean` lists them (checked for orch, client0,
  server1; the tables are generated from the same closure). No fact rests on a hook another package's
  `init` sets; gogo proto's `Register*` calls are in `message`'s own `init`.

## The hypotheses (missing model pieces; named after the lab's specs)

**Stated** (classes, instance arguments of every theorem above them, each a premise of the closed
statement; no instance anywhere):
- `github_com.rs.zerolog.InitHyp`, `github_com.gogo.protobuf.proto.InitHyp`,
  `github_com.gogo.protobuf.gogoproto.InitHyp`, `github_com.go_redis.redis.v8.InitHyp`,
  `os.signal.InitHyp`, `math.rand.InitHyp` (each the package's `wp_initialize'`, the lab's
  `<pkg>.init.spec`: the initializer runs without panicking); go-redis' `internal/proto.InitHyp` is
  declared but no initializer of the programs reaches it;
- `github_com.gogo.protobuf.proto.Hyps` (`proto/Spec.lean`): `RegisterEnum` (`"message.MsgType"`,
  once, inside `message`'s initialization), `RegisterType`, `RegisterFile`, each with the package
  state;
- `github_com.rs.zerolog.Hyps` (`zerolog/Spec.lean`): `New`, `SetGlobalLevel`, `ParseLevel("warn")`,
  and `∃ ownEvent, EventSpecs`: the five levels on a non-`nil` logger, `Event.{Str,Int,Ints,Int64,
  Uint32,Bool,Float64}`, `Event.Msg`, with an exclusive event token;
- `math.rand.Hyps` (`math/rand/Spec.lean`): the package-level `Intn`, and `∃ isSource ownRand,
  RandSpecs`: `NewSource`, `New`, `Rand.Intn` with exclusive tokens;
- `os.signal.NoSignals` (`os/signal/Spec.lean`): the environment assumption.

**Proved** from a model: `log.Println` (Perennial's trusted `log` model, Net's
`Net/Proof/log/Println.lean`; until review #24 the premise `log.Hyps`); bufio (the shared change on #24: the
main tree's `Spec/bufio/`, `Proof/bufio/`).

## State, in detail

- Porting recipe: imports `Proof.Rabia.X` -> `Dsverify.Proof.rabia.Core.X`, `Proof.…` ->
  `Dsverify.Proof.…`, `Rabia.GeneratedProof` -> `Dsverify.GeneratedProof`, the lab's
  `<pkg>/Base.lean` -> `Basics.lean` (`Base.lean` is the generated package fact), `message.Spec` ->
  `message.SpecPure` (until message's bufio half), `Harness.Proof.math.rand` ->
  `Dsverify.Proof.math.rand.Spec`, `Harness.Proof.os.signal` -> `Dsverify.Proof.os.signal.Spec`,
  `zerolog.Methods` -> `zerolog.Spec`; `attribute [local instance] Dsv.netConnExts … pkgStates` ->
  `variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]`; `open … NetConn Dsv` ->
  `open … Net`; `[π : NetProtoGS]` on each section's GF line lacking one; a Spec file imports its
  package's `Base.lean`; `dsverify_lab.harness.KvInput` -> `model.KvInput`.
- Namespaces: whatever invariant may be open when the client's update fires is below `rabiaR`
  (`cliE = ⊤ \ rabiaE`): `slotN` (consensus `Spec`), `srvKeysN`, tcp's `wgN` and `rcptN` moved there;
  the lab's `clientN` lemmas (`keys_client_disj`, `client_rabia_disj`) are stated with `cliE`.
- Perennial drift fixed in place: `decide` on goals with `W32` literals -> `simp`;
  `nonblockingRecvAuAlt`/`nonblockingRecvAuInner` are `|NC={⊤,∅}=>`: `iapply ncfupd_of_fupd` before
  `iinv`; proxy's `StoreRel` takes `(kv GoString GoString).State` (with `KStore` a later goal was
  ill-typed at `implicit` transparency).
- Hypothesis classes (no instance anywhere): "The hypotheses" above; each is a premise of
  `rabia_remote_robust`.
- tcp's `Spec`: the lab's `net.ownListener l lid a` is `ownListener li l a` = `net.isListener li l ∗
  netLis NL l a true ∗ netLisAt NL l a` (`net.Listen`'s post); `ProxyTcpInit`/`NetTCPInit` take
  `shared γ` (it holds the address's `addrProto`, which `listen_au` needs) instead of the lab's
  `addrTok`; `tableEntry` holds `net.isConn cv cid true a` (`cid : Nat`) instead of
  `net.rpc.connIface`.

## Next steps

1. Landing: `etc/land.sh` from the worktree (not done by the review's fix; the coordinator queues it).
2. Optional (review #24): move `sentLb_prefix`, `sentLb_agree`, `recvTokL_sentLb` from
   `tcp/ProtoLemmas.lean` into `GooseLang/Ext/Net/Proto.lean` (a follow-up: it rebuilds every module
   over `Proto.lean`).
3. Models of the names-only libraries (zerolog, gogo `proto`, math/rand's `Rand`) would turn the
   remaining premises into proofs.
