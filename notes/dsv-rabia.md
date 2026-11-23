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
`github_com.rs.zerolog.Hyps`, `math.rand.Hyps`, `log.Hyps` (`log.Println`), and the environment
assumption `os.signal.NoSignals`. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
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
**Open for the gates:** `etc/tier-check.py --check` refuses 106 new edges (88 proof->proof, 14
defs->proof, 4 spec->proof), all under `Dsverify/{Spec,Proof}/rabia` and the part's library
`Spec.lean`s (which declare `wp_proof`s, so are proof tier); the baseline only shrinks, so they
need the proofs to take callees' specs as hypotheses (linked in `Link`/`Linked`) before landing.

**Kit Go changes (third agent and its agents):** `Sys` has a mutex, `Op` locks it (`op1` the body);
`op1` answers unknown once the sequence numbers reach `SeqBudget = 2^29` (`proxyP`'s budget;
remote serves unboundedly many operations); the model's `Entry` has `Old` (puts overwritten while
pending, `cat`): the earlier `State` could not represent the pending set exactly (two histories with
equal states allowed different configurations, so `Equal`'s spec was false); `gens()` answers
`Gen(c, 0)` for `c` outside `[0, NC)` (`genSpec` quantifies every id). `go test` passes.

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
- **`os/signal`**: the coordinator's decision, implemented by the third agent's fork:
  `os.signal.Hyps` holds the library's behaviour (`Notify` registers a channel on which the
  runtime may deliver any signal; `Stop`), and the **environment assumption** `os.signal.NoSignals`
  (nobody sends SIGINT/SIGTERM to the deployment's processes; `NotifyQuiet`) is a class of its own,
  which `SigListen` takes. **For the user:** the honest alternative (only `Hyps.Notify`) costs a
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
- Hypothesis classes (no instance anywhere): `github_com.rs.zerolog.Hyps`, `os.signal.Hyps`
  (`Notify` says **no signal is delivered**: an assumption on the environment, the lab's model's;
  `Stop`), `math.rand.Hyps` (`NewSource`, `New`, `Rand.Intn`, the package-level `Intn` for the kit's
  `choose`; taken by the coin's theorems and the executor's proof sections). With the `InitHyp`s,
  each must be a premise of `rabia_remote_robust`.
- tcp's `Spec`: the lab's `net.ownListener l lid a` is `ownListener li l a` = `net.isListener li l ∗
  netLis NL l a true ∗ netLisAt NL l a` (`net.Listen`'s post); `ProxyTcpInit`/`NetTCPInit` take
  `shared γ` (it holds the address's `addrProto`, which `listen_au` needs) instead of the lab's
  `addrTok`; `tableEntry` holds `net.isConn cv cid true a` (`cid : Nat`) instead of
  `net.rpc.connIface`.

## Next steps

1. (done) message's bufio half. Design: the read specs fix the reader's condition to a connection's
   (`connPre`, a non-empty buffer); `BufRead` is generic in the stream `S`, the `ReadUnmarshal`s are
   over a connection end (`S = recvTokL cn s P`), their payload premise `frameIs P cn R D` is over the
   protocol (`protoPrefix P cn (R ++ frame bs) -∗ ⌜D bs⌝`), reached through the reader by
   `net.connReader_proto` with a later credit; the write specs take `io.writerOk wi J Q Ew` (its
   prefix closure: the header's write). `message`'s fact is `msgFact` (`errFrameTooLarge`,
   `errFrameTooLong` non-`nil`; `etc/dsv/rabia.py`'s `finish`).
2. tcp's transport: base done (`Basics.lean`: a connection end's reader/writer `rdOwn br cn s P R`,
   `wrOwn bw cn s P W pend err` (existentials over the bufio predicates' contract parameters),
   `wp_GetReaderWriter` (socket options through `sockopt_au`, readers/writers from
   `net.conn_readerOk`/`conn_writerOk`), message's specs over them; `ProtoLemmas.lean`
   (`ProtoPrefixClosed` of the protocols, `sentLb_prefix`/`sentLb_agree`/`recvTokL_sentLb`: missing
   laws of `Proto.lean`, proved from its definitions); `Hub.lean`). **The framed protocols `proxyP`,
   `proxyQ`, `netP` allow the empty stream outright** (`⌜W = []⌝ ∨ …`, `Core/Proto.lean`): the
   revised `bufio.NewWriterSize` asks `□ Q W` when the writer is made, and the proxy makes its writer
   before it reads the client's handshake (the lab made `ownWriter` later). The endpoints: in
   progress (above).
3. network `Prologue`, proxy `ProxyInit`/`Prologue`, server: in progress (above).
4. The kit (`Configure` with `confClaim`, `NewClient`, `Op` with `opAU`/`lin_opAU`, `Server`, the
   porcupine model's proof as paxos's `ModelSet`/`ModelProof`, `gens()`'s `genSpec`), mains, a
   `Link`, `TopLevelDefs`, `TopLevelRobustness` (`rabia_remote_robust`; every `InitHyp` and `Hyps`
   class and `os.signal.NoSignals` a visible premise; confirm `etc/theorem-loc.py` counts them),
   `#print axioms`, the collection's baseline, `lake build` of everything new.
