# dsv-quepaxa: dsverify-lab's QuePaxa kit on the net extension (phase 6)

Branch `dsv-quepaxa` (2026-11-23, off `origin/dsv-paxos` e3eaf5cd0d; worktree
`/shared/etcd-grove-dsvquepaxa`). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/quepaxa/` (run
**`quepaxa-bump-1`**, the chain's final verified run: proof `4ae902e` tag `final`, fork `77b5258`,
Perennial `3afd77e35`; read only, nothing in the lab changed). The lab's top-level theorem:
`dsv_goal_check : SafeDist (orchNode :: clientNodes ++ serverNodes) quepaxaNetCfg`, axioms Lean's
three and porcupine's `CheckOperations.wp_proof`.

**The coordinator's rule for missing model pieces** (2026-11-23, all seven ports): a model piece
that is not proved here (gRPC's unary path, bufio beyond `NewReader`/`Read`, third-party libraries
the lab replaced by cut-down copies, ...) is neither added nor a reason to stop: its spec is a
hypothesis (a section variable named after the lab's spec), listed below, and the port goes on
(Go, translation, protocol proof, kit, statement over the hypotheses). Shared pieces come as one
change each.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/quepaxa/` (module `raxos`, the fork's path): the fork's `common`, `configuration`, `proto`, `proto/client`, `replica/src` (with the lab's `finding_*_test.go`), and the kit `examples/quepaxanet` (`kit.go`, `model.go`, `kit_test.go`) with its twelve commands `cmd/{orch,client0..5,server1..5}`. Not copied: the fork's benchmark client `client/`, `replica/main.go`, `integration-test/`, `model-checker/`, `docs/`, the lab's dsrig commands and generated `pb_*gen.go` |
| translation | `etc/goose.py` project `dsv-quepaxa` into the part `Dsverify/`: `Dsverify/{Code,GeneratedProof}/raxos/**` (configs `Dsverify/Code/raxos/{replica/src,proto/client}.toml`, the lab's); names only into the part: `gopkg_in/yaml_v2`, `github_com/go_redis/redis/v8`, `io/ioutil`, `encoding/gob` (common's `GetRealSizeOf`), and grpc's `google_golang_org/grpc{,/codes,/status}` (types and names; the main tree's grpc imports the main tree's `net`, which clashes with `Net/`'s), configs beside them; remote and `net` the part `Net/`'s; protobuf, bufio, os, math/rand, lintest, porcupine the main tree's translation |
| trusted code | `Dsverify/TrustedCode/{raxos/replica/src,raxos/proto/client}.lean` (the lab's no-op `init`s of protoc-gen-go's descriptor plumbing); `Dsverify/TrustedCode/{gopkg_in/yaml_v2,github_com/go_redis/redis/v8,io/ioutil,encoding/gob,google_golang_org/grpc,google_golang_org/grpc/codes}.lean`: no-op models of the names-only packages' variable initializers and `init` functions (the lab's kind, `lean.trusted_init`; made by a script from the translation's `initialize'`, listed as `trusted` in each config); empty `Dsverify/ManualProof/` modules beside them |
| package facts and initialization | `Dsverify/Proof/<pkg>/Base.lean` (`True` for every QuePaxa package and names-only library; each imports its imports' fact modules), `Dsverify/Proof/google_golang_org/protobuf/Base.lean` (protobuf's five packages' facts: the main tree's live in `cache/v3/Base`, `raft/v3/Base`, which import the main tree's `net`); `etc/gen-init.py` `dsv_inits` (additive: `DSV_QP*`, `DSV_MAIN` = bufio, math/rand, protobuf's `Init` made in the part as `NET_MAIN`'s in `Net/`, `DSV_OWN` = the part's grpc without the main tree's `SPECIAL`, `SPECIAL['raxos.replica.src']` for `Consensus_ServiceDesc`); generated `Init.lean` and the twelve commands' `PkgTable.lean` all build |
| the protocol's proof | `Dsverify/Proof/raxos/` (the lab's `Quepaxa/Proof/` layout): so far `Pure/Conf.lean`, `Pure/Consensus.lean` (verbatim, build) |
| trust base | `etc/tcb-collections/dsv-quepaxa.txt` (to come with the statement) |

## What changed against the lab (Go)

- **The deployment is remote's** (as paxos): the orchestrator (`Orch`: `New`, a wait of `StartMs`,
  then `remote.Check`) checks the history against **the kit's key-value map with pending puts**
  (`model.go`: per key the known value and the values of puts of unknown outcome; an answered get
  may fire one pending put; a get of unknown outcome changes nothing). No porcupine partition (the
  verified porcupine has none): the state is a list of per-key entries. Exact (not only sound): a get
  that sees the current value keeps every pending put, one that sees a pending value fires that one
  only; any other configuration's future is included in the kept one's. `TestModel` checks cases.
  The lab used its own driver, recorder and `check.KV` over `models.KvIn/KvOut`, an unknown
  outcome being porcupine's pending operation (output `nil`); here `Out{Unknown: true}`, remote's.
- Inputs/outputs are the kit's `In`/`Out` (in place of the lab's `models.KvIn/KvOut`), with the
  kit's codec (`EncIn`/`DecIn`/`EncOut`/`DecOut`; a get is a read, so `remote.Do` may retry it).
- `Gen(c, j)` is unchanged; remote's generator `gen(c)` has no operation index, so `Gens()` keeps
  one counter per client (each touched only by its own client's goroutine of the driver).
- The start delays: the lab's `Start(c)` (`StartMs + c*StaggerMs`, given to its driver) is now
  `StartMs` in `Orch` after `New` and `c*StaggerMs` in client `c`'s first `Op`.
- `AttemptMs` (one call orchestrator → client machine) is `OpMs + NC*StaggerMs + 2000`.
- **Addresses**: every machine's ports are distinct ports of `127.0.0.1` (`Addrs`, `RecAddrs`,
  `CfgAddrs`, `ClientAddrs`: `76xx`, outside Linux's ephemeral range), in place of the lab's
  `10.77.0.(10+i)` hosts with the same ports on each (`ports(addrs, p)` is gone). The replicas still
  listen on `0.0.0.0:port` (the net extension's wildcard, D21).
- The client machine's QuePaxa client is made once, before `remote.ServeClient` (`clientNode`), as
  paxos's: `ServeClient.spec` takes `newClient` as a persistent triple with precondition `True`, and
  a second `Sys` of client `c` would listen at the same address again (the paxos design finding).
- `registerProto` is a no-op: the lab's build replaced `google.golang.org/protobuf` by its model
  with `proto.SetCodec` and the kit's generated codec (`pb_gen.go`, the lab's pbgen); here the Go
  build runs the real protobuf and `models/grpc`'s or grpc-go's proto codec. The Lean side's
  `proto.Marshal`/`Unmarshal` are hypotheses (below); the kit's codec, regenerated with
  `models/protobuf/pbgen.py`, is the way to discharge them (not done).
- `examples/dsverify/quepaxa/go.work` (`use .`): `etc/goose.py`'s `module_models` route through
  `-modfile` fails under goose ("build flag -modfile only valid when using modules"); its `GOWORK`
  route works. (A finding for `etc/goose.py`: only project `etcd`, which has a `go.work`, used
  `module_models` before.)

Tests: `go test ./examples/quepaxanet/` (the unit tests; `TestDeployment` runs the eleven machines
as processes on free loopback ports, in a random configuration or `QPNET_CONF`): passes over grpc-go
and over `models/grpc` (`models/grpc/gomodel.py examples/dsverify/quepaxa test ...`), configurations
`3,0,1,1,5000` and `5,1,5,5,40000` and random ones; `go test ./replica/...` (the lab's findings) passes.

## Hypotheses (missing model pieces)

The lab proved these in its `Harness/` (its own models); here they are hypotheses of the port,
named after the lab's specs, until each comes as one shared change:

- **gRPC, unary** (the lab's `Harness/Proof/grpc/`, over its own `rpcmodel/grpc`; here `models/grpc`,
  whose Lean half is not written, `notes/dsverify-net-port-plan.md` phase 5 item 4): the
  vocabulary `GrpcWorld`, `UnarySpec`, `handlerOk`, `grpcAddr`; the specs `grpc.Dial.spec`
  (with `WithInsecure`), `grpc.NewServer.spec`, `grpc.Server.RegisterService.spec`,
  `grpc.Server.Serve.spec`, `grpc.ClientConn.Invoke.spec` (the recorders' `ESP`, `FetchBatches`,
  `InformDecision`, `Consensus_ServiceDesc`'s handlers). The main tree's grpc specs are etcd's
  trust-boundary axioms, not usable here.
- **protobuf** (the lab's `Harness/Proof/grpc/Pb.lean` and its protobuf model's `SetCodec`):
  `proto.Marshal`/`proto.Unmarshal` of `ClientBatch`, `ProposerMessage`, `RecorderResponse`,
  `DecideRequest`, `DecideResponse`, `Decisions`, `Empty` (QuePaxa's `clientwrapper.go` and gRPC's
  codec).
- **`sync.Map`** (the lab's `Harness/Proof/sync/Map.lean`; `replica/src/clientbatchstore.go`'s
  store): Perennial has no `sync.Map` spec.
- **bufio's `Writer`** (`NewWriter`, `WriteByte`, `Write`, `Flush`) and `Reader.ReadByte`, `io.ReadFull`
  over a `bufio.Reader` over a `net.Conn` (the lab's `Harness/Proof/bufio/{Writer,ReadFull,Net}`): the
  main tree has `NewReader` and `Reader.Read` only.
- **math/rand's untranslated initializers** (`Dsverify/Proof/math/rand/Init.lean`'s generated
  `axiom opaqueInitsOk`, the same trust-boundary axiom as the main tree's `Proof/math/rand/Init.lean`;
  Perennial translates `math/rand` with its variables' initializers untranslated): an axiom under
  `Dsverify/` until it is a hypothesis threaded through the init chain or Perennial translates them.
  The only axiom under `Dsverify/` now.
- **go-redis, yaml.v2, io/ioutil, encoding/gob, grpc's initialization**: names only, never reached (benchmark mode 0; the configuration
  made in code). Their calls need no spec unless the proof must show them unreachable (it does:
  `Init`'s mode-1 branch is excluded by the configuration).
- `log` (`Println`, `Fatal`), `math/rand` (`Intn`, `Seed`, `NewSource`/`New`/`(*Rand).Intn`), `os`
  (`Create`, `Exit`, `Stderr`), `fmt.Fprintf`, `strconv.Atoi`, `sort.Ints`, `time` extras (the lab's
  `Harness/Proof/{log,math/rand,os,fmt/Extra,strconv/Atoi,sort/Ints,time/Extra}`): to check against
  Perennial's and the main tree's (`Proof/math/rand`, `Proof/strconv`, Perennial's `log`, `sort`)
  when the proof reaches them; hypotheses where missing.

## State

- Done: the Go (commit `0fbd49207a`); the translation, building (`28eddbe98d`; Go comments with tabs
  expanded in `common/common.go` and `replica/src/server.go`, as the lab's goose.sh did: Lean rejects
  tabs in the doc comments goose copies); `Pure/Conf`, `Pure/Consensus`; the package facts and
  initialization, all twelve `PkgTable`s building (`0e2763910c`).
- Build: `PERENNIAL_DIR=/shared/perennial-9c3b81f30 etc/goose.py --project dsv-quepaxa`, then
  `PERENNIAL_DIR=... python3 etc/gen-init.py`, then `lake build
  Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.PkgTable` (and the other eleven).
- Next: the proof port in the lab's dependency order (`Pure` → `PkgState`/`Msg`/`Ghost` re-based on the
  statement here (remote's `pendCtx`, `DistDeploy`), not the lab's `QuepaxaNetSpec` → `Cons`, `Smr`,
  `Codec`, `Proposer`, `Replica`, `Proxy`, `Kit`), the net calls ported onto `Net/Spec/net/*` and
  `Proto.lean`'s laws as `paxos/NetProof.lean` did, the hypotheses above as section variables; then
  `quepaxa_remote_robust` (`DistDeploy … → Robust [] …`) over them, its collection.
  First steps: `Pure/Smr.lean` (imports the lab's `Harness.Model` `kv`: re-base its law
  `execCmd`-is-a-`kv`-step onto the kit's model here, `model.go`'s Lean form, a `ModelSet` analog as
  paxos's, against linkv's `pSeq`); then `PkgState`/`Msg`/`Ghost` (the lab's `QuepaxaNetSpec`,
  `Harness.ClientSpec`, `Harness.Models` replaced by remote's statement). The lab's modules that
  import `Harness.Proof.{grpc,sync.Map,bufio.*}` take the hypotheses above.
- Size: the lab's protocol proof is 37k lines (`Quepaxa/Proof/`, without the translation), against
  paxos's 8k: this port spans several sessions.

## Which lab run

`quepaxa-bump-1` (dsverify-lab `master` `915f964`, `examples/quepaxa/SOURCE.md`): proof `4ae902e`
(tag `final`), fork `77b5258`, harness `cd3a97b` (lab commit `71cae38`), Perennial `3afd77e35`;
verified there in 671 s (`verify-final.log`).
