# dsv-epaxos: dsverify-lab's EPaxos kit on the net extension (phase 6)

Branch `dsv-epaxos` (2026-11-23), off `origin/dsv-paxos` (`e3eaf5cd0d`; paxos has not landed on
`lean` yet). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/epaxos/` (run **`epaxos-e1nogs-1`**, the final
verified run of EPaxos: clients on nodes of their own, Perennial `3afd77e35`, the E1-opt1/opt2 perf
fixes; proof `c276a91` tag `final`; fork `71d99d4`). Read only: nothing in the lab changed.

**Merges (2026-11-23):** `origin/dsv-infra` (`a1046d9c4f`, then `884cb306c9`): the kit's goose
project and gen-init configuration are now `etc/dsv/epaxos.py` only (no shared lines of
`etc/goose.py`/`etc/gen-init.py` are this kit's; `gen-init.py --check`, `goose.py --check --project
dsv-epaxos` up to date). `origin/models-rpc-server` (`040ef5e808`, not landed: waits for the human
reviewer; the coordinator's instruction): the whole net/rpc server proved on Lean's three axioms;
the kit builds against its server specs directly (no mirrored hypotheses for net/rpc's server).
It also brought `origin/lean` (`92eb404dbc`: dsv-tpmodels' gods/uuid/concurrent-map/slog models).

**State (2026-11-23):** the Go, the translation, the package initializers (all 32 packages and the
17 programs' `PkgTable`s build, no axiom: the names-only inits are `InitHyp` hypotheses) and the
mechanical port of the pure model (below, "Proof port: progress") are done. The code proofs, the
kit's model proof and `epaxos_remote_robust` are not started; every layer of them rests on library
specs that are hypotheses here ("Hypotheses").

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/epaxos/` (module `github.com/imdea-software/swiftpaxos-epaxos`: the fork's path with `-epaxos`, see below): the fork's packages the kit runs (`rpc` = fastrpc, `dlog`, `config`, `state`, `replica/defs`, `replica`, `epaxos`, `master`, with the fork's `fix_*_test.go` regression tests) and the kit `examples/epaxosnet` with its 17 commands `cmd/{orch,client0..9,server1..6}` |
| the kit | `examples/epaxosnet/kit.go` (configuration, addresses, `Gen`, `Op`, `Orch`, `Client`, `Server`, the replicas' registration), `model.go` (the porcupine model and remote's `Codec`), `rpc.toml` + `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` (rpcgen's codec of the master's and the replica's net/rpc receivers), `kit_test.go` |
| translation | `etc/goose.py` project `dsv-epaxos` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/github_com/imdea_software/swiftpaxos_epaxos/**`, and gods v1.18.1 at `Dsverify/{Code,GeneratedProof}/github_com/emirpasic/gods/**`); remote, `net`, net/rpc and net/http the part `Net/`'s (std_models `net/rpc`, `net/http`); `encoding/json` the part's names-only translation of the model (dsv-vr's, std_models `encoding/json`; files identical to dsv-vr's); lintest, porcupine, `bufio`, `os` the main tree's; the rest Perennial's |
| initializers | `etc/gen-init.py` (additive: `DSV_EPAXOS`, `DSV_MAIN`, `DSV_MAIN_COPY`, the epaxos `SPECIAL`s, `DSV_PKGS`/`DSV_PROGRAMS`; dsv-vr's `dsv_hyp_fix`/`DSV_HYP_NEED` taken over verbatim, `DSV_HYP_INITS` the union `encoding.json`, `net.rpc`, `net.http`): `Init.lean` of every package, `PkgTable.lean` of the 17 programs; `Base.lean` facts all `True` (hand-written, `Dsverify/Proof/**/Base.lean`); `Dsverify/Proof/bufio/Init.lean` a generated copy of the main tree's; hypotheses `Dsverify/Proof/{net/rpc,net/http,encoding/json}/Init.lean` (the first two from `scratchpad`'s template, the same shape as dsv-vr's) |
| pure model | `Dsverify/Proof/github_com/imdea_software/swiftpaxos_epaxos/{Model/**,Interface/Wire.lean,epaxos/{Tarjan,ExecModel}.lean}` (the lab's, renamed), `Model/KvScan.lean` (the lab harness's `kvScan`, pure) |
| goose configuration | `Dsverify/Code/github_com/emirpasic/gods/trees/redblacktree.toml` (the iterator's `Next`/`Prev` names only: `goto`) |

The translation builds (2026-11-23, `lake build` of `Dsverify.GeneratedProof...examples.epaxosnet.cmd.{server2,orch,client0}`, which import every translated package; build seeded from `/shared/etcd-grove-dsvvr/.lake/build`, Perennial from `/shared/perennial-9c3b81f30` through `.lake/package-overrides.json`). `etc/tcb-collections/dsv-epaxos.txt`: the roots, an empty baseline (nothing proved yet). Not yet: initializers (`etc/gen-init.py`), the proof, the statement.

## What changed against the lab

- **The source.** The lab's `examples/epaxos/fork/swiftpaxos` lacks the `epaxos/` package (the
  archive's exclusion meant for Rabia's prebuilt `epaxos/` dropped it: SOURCE.md, "Left out"). The
  port takes the fork from the lab's perf cache, `cache/perf-epaxos/e1nogs.bundle`, commit
  `71d99d4` (the run's; identical to `examples/epaxos/fork/swiftpaxos` but for `epaxos/`).
- **The module path** is `github.com/imdea-software/swiftpaxos-epaxos` (Lean
  `github_com.imdea_software.swiftpaxos_epaxos`), not the fork's: the swiftpaxos kit
  (`examples/dsverify/swiftpaxos`, branch `dsv-swiftpaxos`) translates another fork of the same
  repository into the same part, and the two would write the same module files
  (`Dsverify/Code/github_com/imdea_software/swiftpaxos/replica.lean`, ...) with different contents.
  Every import of the fork's packages was rewritten; nothing else in them changed.
- **gods is the real module** (v1.18.1), not the lab's cut-down copy (`harness/rpcmodel/gods`); its
  red-black tree's iterator (`Next`, `Prev`) uses `goto`, which goose refuses, so those two are
  names only (above), and the state package's scans reach them.
- **The deployment is remote's** (as paxos's): the orchestrator runs `remote.Check` against this
  kit's model; each client is a machine of its own (`remote.ServeClient`); the lab's kitgen-generated
  configuration, driver (`RunRemote`), `remote.KVScan` codec and `check.KVScan` checker are gone.
  17 machines as in the lab: orchestrator, 10 client machines, the master, 5 replicas. Addresses
  `127.0.0.1:75xx` (server id at port 7500+id, a replica's net/rpc 1000 above; clients 7511..7520).
- **The model** (`model.go`) is the key-value store with scans and **pending writes**, as a set of
  configurations (each: the store, and the puts of unknown outcome that may still take effect, each
  at most once, at any later point): a put of unknown outcome is added to every configuration's
  pending puts; a get or scan answered with V keeps the configurations (and their pending puts'
  effects, chosen per key) whose values give V. Exact for any history (no premise on values: no
  distinctness or fixed length needed). The value "" is a missing key (SwiftPaxos's GET/SCAN replies
  do not tell them apart). The lab's model (the harness's `kvScan` with the escrow of fired outputs)
  is not used.
- **The workload.** remote's `gen` has no operation index, so `Gen(c)` draws at random
  (`primitive.RandomUint64`): a put of a random key (value `v<c><digit>`) or a read of a random key
  (a get for clients 0..4, a scan of 2 keys for 5..9); `Ops = 2` per client. The lab's fixed
  schedule (a put, then a read of the same key) is not expressible.
- `Op` is the lab's but returns `Out` (unknown on any error); the start delay (the lab's `Start`,
  the orchestrator's) is in the client machine's first operation; `serve` uses a hand-written
  `host` and `itoa` in place of `strings.Split` and `fmt.Sprintf` (fewer library specs).
- **rpcgen**: the codec is the repository's `models/net/rpc/rpcgen.py` (not the lab's kitgen), but
  generated **with a one-line fix** to `rpcgen_core.py` (not committed: `models/` is not this
  branch's): `codec_go` imports the receivers' packages, which `rpc_gen.go` does not use when the
  receivers' packages differ from the argument types' (`master`, `epaxos` vs `replica/defs`), so Go
  refuses the file. The fix: `codec_go` calls `S.imports(receivers=False)` (the receivers' packages
  only in `rpc_model_gen.go`). Until `models/` takes it, `rpcgen.py ... --check` on this kit
  differs. Regenerating needs `go get models.lab` in the kit's module first (rpcgen's dump imports
  `models.lab/rpcdesc`; `go mod tidy` drops it again).

## Tests

`cd examples/dsverify/epaxos; GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./...`: the fork's regression
tests, and the kit's `TestDeployment` (the 16 machines as processes of the test binary at the
kit's own addresses, the orchestrator in the test with its outputs counted: porcupine accepts and
all 20 operations are answered; about 21 s), `TestModel`, `TestCodec`, and rpcgen's
`TestRPCCodec*`. With the models: a GOROOT from `models/goroot.py farm DIR`, then
`GOROOT=DIR GOTOOLCHAIN=local PATH=DIR/bin:$PATH go test -tags netmodel ./examples/...`. Both pass
(2026-11-23).

## Proof port: progress

1. **Initializers: done** (`01ac72f60b`, `c7617216ca`). Notes: `gen-init`'s closure stops at a
   hypothesis package (its `imports=[]` and `pkginfo_imports` → `[]`: its `GetIsPkgInitWf` is
   hand-written, `g p = isPkgInit p ∧ True`), so a program's table does not need facts of net/http's
   untranslated closure. `epaxos`' initializer: `deferMap` is `make(map[uint64]uint64)`
   (`wp_map_make1`), `errVarintOverflow` an `errors.New`. The facts the lab proves
   (`Epaxos/Top/PkgState.lean`: `errVarintOverflow`, `deferMap` ↦□, `LatencyConf` ↦□ "") are not
   yet in `Base.lean`: add them (gen-init `finish` steps) when a code proof reads them.
2. **Pure model: ported mechanically** (`etc/dsv-epaxos/port.py`: module
   `Epaxos.{Model,Interface}.X` → `Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.
   {Model,Interface}.X`, `Epaxos.Proof.X` → `…swiftpaxos_epaxos.X`; identifier `swiftpaxos` →
   `swiftpaxos_epaxos`; `dsverify_lab.harness` → `…swiftpaxos_epaxos.kvs`; `KvsInput/KvsOutput/
   Option GoString` → `(List w8)`, as this Perennial's `GoString` is not `List w8`). By hand:
   `Interface/Wire.lean` imports `Model/KvScan.lean` in place of `Interface/Names.lean` (the lab's
   net harness) and drops the harness's local instances. **Builds** (2026-11-23, `lake build
   …Model.Proof.{ExecWfInv,G1Replay,NoneRec}`, the leaves; 63 files, 32k lines, no `sorry`;
   `#print axioms model.inv_step_deliver`: Lean's three). Also `Interface/PeerWire.lean` (the peer
   messages' pure encoders and `Countable` instances; by hand: imports `Perennial.Std.Countable`,
   which the lab's `Names` brought, and keeps `open Iris`).
3. **Interface layer, by hand (in progress).** `Interface/Names.lean` (`EpNames`, without the
   lab's `rpc : RpcWorld netDistGF` field: Net/'s net/rpc world is passed on its own when needed),
   `Interface/Net.lean` (the peer streams' ghost vocabulary; GF generic under `GooseGlobalGS`,
   statements annotated `(GF := GF)`; connection ids are the extension's `Nat`, so `peerConn`'s
   variable is `Option Nat` and `cwriters` maps a writer to a `Nat`), **`Interface/Client.lean`
   redesigned**: the op's update is `opU γ i Φ`, exactly remote's `lin` of the store (`sysState =
   own_state γ`, `Eop = epEop = ↑epN`, `B.step = kvStep`, the function form of `kvScan`,
   `kvStep_spec`), in place of the lab's `AU … @ ↑clientN`; the escrow keeps `Φ o` (not the lab's
   `Q σ σ' o`); `escrow_fire` needs `⊤ ∖ epEop ⊆ E` (was `↑clientN ⊆ E`) and still gives the
   lab's `(kvScan w8).step σ i σ' o`; `escrow_claim` gives `Φ o`; `inPre` is the lab's `kit.pre`;
   `serverAddrs`/`replicaAddrs` the kit's `ServerAddrs()` (7501..7506; replicas 7502..7506); the
   lab's `is_sys`, `orchShareEp`, `clientShareEp` are gone (remote's start and `Op(addrs, c, in)`
   replace them). `solve_ndisj` (the lab harness's) → `nclose_subseteq`.
3b. **`Interface/Treemap.lean`**: gods' treemap as the hypothesis class `TreemapHyp GF` (abstract
   `isTreeMap`/`iterVal`/`ownIter`; `NewWith_spec`, `Put_spec`, `Get_spec`, `Select_spec`,
   `Iterator_spec`, `iter_alloc`, `Next_spec`, `Value_spec`); `Interface/State.lean` over it.
   Every theorem that uses the store takes `[TreemapHyp GF]`. (dsv-tpmodels' Go model
   `models/gods` has landed but no spec of it is proved; once one is, translate gods through
   `module_models` and discharge the class.)
3c. **The `state` package's proofs: done** (`wire/State/*.lean`, the lab's files via
   `etc/dsv-epaxos/port.py`, which now also rewrites the proof-file headers to the generic `GF`):
   `InitState`, `NIL`, `NOOP`, `Conflict`, `ConflictBatch`, `concat`, `formatUint10`,
   `Key/Value/Command.String`, `KeyComparator`, `Command.Execute`. Changed: the lab's
   `Treemap*.lean` (its cut-down treemap's proofs) are not ported; `Execute`'s `SCAN` case is
   re-proved over `TreemapHyp` (`Select_spec` with the closure's triple, `Iterator_spec`, a loop
   over `ownIter`; pure: `ScanPure.scan_flatten_sorted`, `Execute.vals_es`); `ScanPure` defines
   `keysSorted` (was `TreemapLemmas`'). `#print axioms`: Lean's three (2026-11-23).
4. **Not started:** the rest of the model layer's bridge to remote and the kit's model (the lab's
   `Interface/*` beyond `Wire`: they are stated over the lab's harness `EpaxosNetSpec`, the
   `netConnExts` world and its `kvScan` escrow; here they must be restated over `Net/`'s specs and
   `Proto.lean`'s laws and the kit's set-of-configurations model), the code proofs
   (`Epaxos/Proof/**`, ~40k lines), the model proof (Go `step` vs the set semantics, as paxos's
   `ModelSet`/`ModelProof`), `epaxos_remote_robust`.

## Hypotheses

Stated in Lean (no axiom, no `sorry`; each a `Prop` class taken as an instance by every theorem
that needs it):

- `net.rpc.InitHyp GF` (`Dsverify/Proof/net/rpc/Init.lean`): net/rpc's initializer.
- `net.http.InitHyp GF` (`Dsverify/Proof/net/http/Init.lean`): net/http's initializer.
- `encoding.json.InitHyp GF` (`Dsverify/Proof/encoding/json/Init.lean`, dsv-vr's): encoding/json's.

To be stated when the code proofs reach them (the library specs below, named after the lab's):

(The coordinator's instruction, 2026-11-23: state each as a hypothesis named after the lab's spec,
list it here, do not widen shared translations or add models.)

1. **bufio** (the main tree's `Code/bufio.toml` translates only `NewReader(Size)`, `Reader.Read`):
   the kit's `Op`, fastrpc's `Marshal`/`Unmarshal` of every message, the replica's peer and client
   streams use `NewWriter(Size)`, `Writer.{Write,WriteByte,WriteString,Flush}`,
   `Reader.{ReadByte,...}` and `io.ReadFull`/`ReadAtLeast` over a reader. The lab's specs:
   `Harness/Proof/bufio/{Base,Reader,Writer,ReadFull,Net}.lean`. One shared change (the
   coordinator, #24).
2. **net/rpc's server** (`Register` over `DefaultServer`, `HandleHTTP`, `ServeHTTP`/`ServeConn`/
   `ServeCodec`, the package's initializer), proved only in part on `models-rpc-server`
   (`NewServer`, `Server.Register(Name)`, the free lists, the server codec), and its client's
   **`DialHTTP`** (the CONNECT handshake, `http.ReadResponse`): the master serves net/rpc over HTTP
   and dials every replica with `DialHTTP`; each replica registers with the master (`DialHTTP`,
   `Client.Call`) and serves net/rpc over HTTP (`Ping`, `BeTheLeader`). The lab's:
   `Harness/Proof/net/rpc/{Setup,Wire,Results,Client,initialize}.lean`.
3. **net/http's server** (`http.Serve` up to a hijack, `DefaultServeMux`): plan 5.2 item 7. The
   lab's: `Harness/Proof/net/http/` (over 34 axioms there).
4. **gods' treemap** (`NewWith`, `Put`, `Get`, `Select`, `Iterator`, `Next`, `Key`, `Value`): the
   real red-black tree is translated, but `Iterator.Next`/`Prev` are not translatable (`goto`), and
   nothing proves the rest. The lab used a cut-down copy with its own proof. dsv-tpmodels is
   building a gods treemap model; until then treemap's specs are hypotheses (the coordinator).
5. Also used, with specs to check before the port: `log` (`Logger.Printf`/`Println`/`Fatal`,
   through dlog), `encoding/json` (names only; the replica's latency config, never read: `LatencyConf` ""),
   `sort`, `math`, `strconv`, `fmt.Sprintf` (the master), `time`, `os`.

**bufio (coordinator, 2026-11-23):** the shared change is `origin/dsv-bufio` (`bb18c0f3ef`, in
review; `/shared/etcd-grove-dsvbufio/notes/dsv-bufio.md`). Use its names (or merge it): namespace
`Perennial.EtcdGrove`: `bufio.NewReaderSize.spec`, `NewReader.specOk`, `Reader.Read.specOk`,
`Reader.ReadByte.spec`, `NewWriterSize.spec`, `NewWriter.spec`, `Writer.Flush.spec`,
`Writer.Write.spec`, `Writer.WriteByte.spec` over `ownBufReader`/`ownBufWriter` with contracts
`io.readerOk`/`io.writerOk`; law `ownBufReader_readerOk` (Perennial's `io.wp_ReadFull`/`ReadAtLeast`
through bufio); `Net/Proof/net/ConnIo.lean`: `conn_readerOk`, `conn_writerOk` (needs
`ProtoPrefixClosed P`). The lab's `Interface/BufioLocal.lean`, `Proof/wire/BufioSticky` and
`Harness/Proof/bufio/*` are replaced by these, not ported.

## Next (for a successor)

1. Model layer over remote. The first file that is not pure is `Interface/Net.lean` (the peer
   streams' ghost vocabulary: `msgSent`, `sentHalf`, `delivTok`, `dialTok`, `peerConn`, `addrId`,
   `peerStreamOk`), stated in the lab over `netDistGF` and the ghost names `EpNames` of `Names.lean`
   (the lab harness's `EpaxosNetSpec`). Decide its GF and names over the part's world (as the paxos
   port did for its ghost state), then restate the lab's `Interface/{Client,ClientSpec,Epaxos,EpaxosGhost,
   EpaxosRep,Replica,ReplicaSpec,State,PeerWire,Net,Marshal,Misc,Servers}` over `Net/`'s `net.Conn`
   specs (as `Dsverify/Proof/…/paxos`'s port did) and the kit's model; drop `Names`/
   `EpaxosNetSpec`, the harness's `kvScan` escrow and `RunRemote`.
2. Code proofs (`Epaxos/Proof/{epaxos,replica,examples/epaxosnet,...}`), over the hypotheses
   above (state each as a `Prop` class in `Dsverify/Proof/<pkg>/…`, named after the lab's spec).
3. The kit's model proof, the mains/links, `epaxos_remote_robust`, the TCB baseline.
