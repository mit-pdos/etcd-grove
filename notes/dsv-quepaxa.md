# dsv-quepaxa: dsverify-lab's QuePaxa kit on the net extension (phase 6)

Branch `dsv-quepaxa` (2026-11-23, off `origin/dsv-paxos` e3eaf5cd0d; worktree
`/shared/etcd-grove-dsvquepaxa`). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/quepaxa/` (run
**`quepaxa-bump-1`**, the chain's final verified run: proof `4ae902e` tag `final`, fork `77b5258`,
Perennial `3afd77e35`; read only, nothing in the lab changed). The lab's top-level theorem:
`dsv_goal_check : SafeDist (orchNode :: clientNodes ++ serverNodes) quepaxaNetCfg`, axioms Lean's
three and porcupine's `CheckOperations.wp_proof`.

**Status (2026-11-23): done.** `quepaxa_remote_robust` (twelve machines, `Robust []` under
`DistDeploy`, the library hypotheses visible premises) rests on Lean's three axioms; "The statement
and its premises" and "State" below.

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
| trusted code | only `Dsverify/TrustedCode/{raxos/replica/src,raxos/proto/client}.lean` (the lab's no-op `init`s of protoc-gen-go's descriptor tables in QuePaxa's own packages; empty `ManualProof/` beside them). They stay trusted code, not `InitHyp`s: those packages' other initializers (`Consensus_ServiceDesc`) are translated and proved, and a hypothesis would cover the whole package's `initialize'`; untranslated instead, they would be `opaque` initializers and gen-init's `opaqueInitsOk` axiom. (The names-only libraries' no-op models of 0e2763910c are gone: `InitHyp`s, below.) |
| initialization hypotheses | `Dsverify/Proof/{gopkg_in/yaml_v2,github_com/go_redis/redis/v8,io/ioutil,encoding/gob,google_golang_org/grpc,google_golang_org/grpc/codes,math/rand}/Init.lean`, hand-written (dsv-vr's pattern): `class InitHyp GF : Prop` holding the package's `wp_initialize'`; gen-init's `DSV_HYP_INITS` / `dsv_hyp_fix` (vr's code) treat them as external and add `variable [<pkg>.InitHyp GF]` to every generated init file above them |
| package facts and initialization | `Dsverify/Proof/<pkg>/Base.lean` (`True` for every QuePaxa package and names-only library; each imports its imports' fact modules), `Dsverify/Proof/google_golang_org/protobuf/Base.lean` (protobuf's five packages' facts: the main tree's live in `cache/v3/Base`, `raft/v3/Base`, which import the main tree's `net`); `etc/gen-init.py` `dsv_inits` (additive: `DSV_QP*`, `DSV_MAIN` = bufio, math/rand, protobuf's `Init` made in the part as `NET_MAIN`'s in `Net/`, `DSV_OWN` = the part's grpc without the main tree's `SPECIAL`, `SPECIAL['raxos.replica.src']` for `Consensus_ServiceDesc`); generated `Init.lean` and the twelve commands' `PkgTable.lean` all build |
| the protocol's proof | `Dsverify/Proof/raxos/` (the lab's `Quepaxa/Proof/` layout), all building: `Pure/Conf.lean`, `Pure/Consensus.lean` (verbatim), `Pure/Smr.lean` (edited: the kit's `KIn`/`KOut`, linkv's `kvB`, `execCmd_step`; the lab's `Harness.Models` `kvAbs` moved here, recursive, `kvAbs_put` by `rfl`), `Pure/ModelSet.lean` (new: `mSet`, `step_mSet`, `mSet_empty`, `stepE_ok`); `Msg.lean` (the lab's; its `pbCodec` instance dropped: `marshalPre`/`unmarshalPre` are the shapes the protobuf hypotheses will take), `Ghost.lean` (edited, below), `Cons/{Lemmas,Laws}.lean` (the lab's; connections numbered by the net extension), `Smr/{OpId,SumId,Exec}.lean` (Exec edited: `kvAbs_mem`, `cmdPut_cmdOf`/`goodVal_of_put` over `KIn`) |
| the kit's model | `.../raxos/examples/quepaxanet/Model.lean` (the spec `qS`: the Go state as a list `E` of keys and `Ent`s, `qRep`, `qDec`/`qDec_box`, `stepL`/`stepL_pSeq`, bounds; `Model.spec`) and `ModelProof.lean` (`Model.wp_proof`: `Model()` meets `isModel qS`; helpers `push`/`has`/`erase` (paxos's proofs), `cat`, `lookup`, `set`, `stepE`, `step`, `equalS`/`equalE`/`equal`) |
| hypotheses | `Dsverify/Proof/raxos/Hyp.lean` (protobuf `PbHyp`, math/rand `RandHyp`, gRPC `GrpcVocab`/`GrpcHyp`/`GrpcWorldHyp` and the instance class `QpVocab`, `sync.Map` `MapVocab`/`MapHyp`; below) |
| the kit | `.../raxos/examples/quepaxanet/`: `Kit.lean` (the store `qR γ`, the shares, the specs `Codec`, `Gens`, `Orch`, `Client`, `Server`), `Kit*.lean` (their proofs; `KitClient` the client machine's), `StartAddr`/`StartGhost`/`Start.lean` (`kitAddrs`, `kitLis`, `kit_start`), the bridge with wildcard listeners is dsv-epaxos's (`robust_of_distProtoLisRB` of `.../swiftpaxos_epaxos/examples/epaxosnet/Bridge.lean`; the kit's own copy `DistBridgeLis.lean` deleted 2026-11-23, review #24 finding 4), `Linked.lean` (`wp_Codec`, `wp_Gens`, `wp_Orch`, `wp_Server`, `wp_Client`), `Mains.lean` (the twelve commands' `wp_main`) |
| the statement | `Dsverify/Spec/raxos/examples/quepaxanet/TopLevelRobustness.lean`: `quepaxa_remote_robust.spec` (`DistDeploy quepaxaKitAddrs (system σ) g → Robust [] (system σ) g threads (2^63)` under the premises below); definitions in `Proof/raxos/examples/quepaxanet/TopLevelDefs.lean` (`boot`, `system`, `quepaxaKitAddrs := kitAddrs`); proof `Proof/raxos/examples/quepaxanet/TopLevelRobustness.lean` |
| trust base | `etc/tcb-collections/dsv-quepaxa.txt` (roots `^Dsverify/Proof/raxos/`, empty baseline; the two trusted descriptor-table inits and their justification) |

## What changed against the lab (Go)

- **The deployment is remote's** (as paxos): the orchestrator (`Orch`: `New`, a wait of `StartMs`,
  then `remote.Check`) checks the history against **the kit's key-value map with pending puts**
  (`model.go`): per key the known state (`Found`, `V`) and the values of puts of unknown outcome,
  `Old` (made pending before the known state was learned) and `New` (after). An answered put makes
  its value known and every pending put `Old`; an answered get that sees the known state changes
  nothing, one that sees a pending value makes it known (that put took effect last) and the others
  `Old`; a get of unknown outcome changes nothing. No porcupine partition (the verified porcupine has
  none): the state is a list of per-key entries. The `Old`/`New` split makes the entry's set of
  linkv configurations exact (`Pure/ModelSet.lean`): with the known state, every `New` put is still
  pending but any `Old` one may have taken effect before (overwritten). (A single pending list, the
  first version, accepted the same histories but its set was not exact.) `TestModel` checks cases.
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
named after the lab's specs, until each comes as one shared change. **All are in
`Dsverify/Proof/raxos/Hyp.lean`** (no axiom, no trusted code; `Prop`s the statement will take):

- **protobuf**: `hyp.proto.Marshal.spec`, `hyp.proto.Unmarshal.spec` (the lab's `Marshal.spec`,
  `Unmarshal.spec` with its codec), over the codec of QuePaxa's messages `hyp.qpCodec :=
  ⟨msg.marshalPre, msg.unmarshalPre⟩` (an instance of `Net/Proof/models_lab/pbcodec`'s `PbCodec`);
  errors `models_lab.errAny`. Bundled as `class hyp.PbHyp GF`. Discharge: the kit's codec from
  `models/protobuf/pbgen.py` and protobuf's model. **Unknown fields** (audit, 2026-11-23): every
  `rep*` of `Msg.lean` says the message has none (`⌜x.unknownFields'.len = W64 0⌝`, in every
  nested message; `repCBVal`'s pure conjunct for `client.ClientBatch` values): real protobuf appends
  a message's unknown fields to its encoding (`internal/impl/encode.go`), so `Marshal`'s output is
  `enc*` only without them. `decInto` (the decoding's success) gives the `rep` only behind
  `⌜∃ v0, ok v0 ∧ enc v0 = bs⌝ -∗` (the bytes are a well-formed encoding, which carries no unknown
  field); the callers apply it once the protocol tells them the bytes' origin (`Esp`, `Replica/
  {Handlers,Fetch}`, `NetUnmarshal`'s `unmarshalB.spec` → `NetListen`).
- **gRPC, unary**: the vocabulary `hyp.grpc.GrpcVocab GF` (abstract data: `reqProto`/`respProto`
  (`Net/` `Proto`s of a gRPC address), `worldOk`, `isServer`, `srvOwn`, `srvServed`,
  `isClientConn`, `handlerErr`, with their persistence as fields), `UnarySpec`, `GrpcWorld`
  (`MS`, `reg`), and defined over it as the lab's: `grpcAddr V W a := addrProto a (reqProto W a)
  (respProto W a) ∗ worldOk W`, `replyOk`, `descOk`, `encPre`; `handlerOk` and `decOk` restated
  after review #24 (the deposit `S bs Φ` comes out of `dec`'s success, with a receipt `Got Φ` the
  reply obligation is stated for; "Review #24" below). The specs
  (the lab's statements): `NewServer.spec`, `Server.RegisterService.spec`, `Server.Serve.spec`
  (**changed for the wildcard**: the listener at `la` as `net.Listen`'s success post gives it,
  `isListener li l ∗ netLis l la true ∗ netLisOn l la`, with `lisProto la (reqProto W a)
  (respProto W a) ∗ worldOk W` for the server's address `a`, in place of the lab's listener at
  `a` and `grpcAddr W a`), `WithInsecure.spec` and `Dial.spec` (**as the lab's `dialPost`**: the
  vocabulary's `credsOpt o` (the lab's `DialOption.creds = true`) for `WithInsecure()`'s option;
  `Dial` fails only if no option sets credentials, so QuePaxa's error branch, `fmt.Fprintf` +
  `os.Exit`, is unreachable and needs no spec), `ClientConn.Invoke.spec`;
  bundled as `class hyp.grpc.GrpcHyp V` (over `[PbCodec GF]`, to be `qpCodec`). The law `world_alloc`
  (a world's registry for any method specs) is its own class `hyp.grpc.GrpcWorldHyp V` over the
  global ghost state `GooseGlobalGS` (2026-11-23, top-level session): the start
  (`robust_of_distProtoLisRB`'s obligation, `kit_start`) has no machine's heap. **Audit fixes
  (2026-11-23)**: `Invoke` takes `⌜opts.len = W64 0⌝` (QuePaxa's generated client passes no call
  options; `Esp.lean`'s `wp_ESP`/`wp_FetchBatches`/`wp_InformDecision` take it as an auto-param
  `by rfl` for `slice.nil`) and its error branch gives `D ∨ ∃ rep b, Θ rep b` (a trailer error
  after the reply decoded); `NewServer` takes `⌜opt.len = W64 0⌝`; `descOk` owns (read-only)
  the descriptor's `HandlerType` (a typed nil `*T`, `T` an interface type, `isInterfaceType
  (underlying T)`) and `Metadata` fields, and asks `ss = interface.ok ii` with
  `typeSetContains ii.ty T` (`RegisterService` evaluates `reflect.TypeOf(sd.HandlerType).Elem()`
  and checks `ss` implements it); `srcState` gained `sd.HandlerType' = (*ConsensusServer)(nil)`
  (`etc/dsv/quepaxa.py`'s `finish`); `Dial` asks every option to be a `credsOpt`, the list
  nonempty and the target `dialTarget` (`127.0.0.1:port`, `port` in `1..65535`: gRPC's
  `passthrough` fallback), and is success-only. **The deployment's
  vocabulary is an instance `[qv : hyp.QpVocab GF]`** (data only, field `grpc`): the definitions
  (`netProtos`, `peersP`, `replicaRes`, the proxy's state) mention `qv.grpc`; theorems that call
  gRPC take `[GrpcHyp qv.grpc]`. The statement will quantify over the instance and the hypothesis.
- **`strconv.Atoi`: proved, no longer a hypothesis** (2026-11-23). `hyp.strconv.Atoi.spec` (for
  1 to 18 decimal digits, the value `decVal s` and `nil`) and the class `hyp.AtoiSpec GF` carrying
  it are in `Dsverify/Proof/raxos/AtoiSpec.lean` (defs); `AtoiProof.lean` (proof tier) proves
  `wp_internal_Atoi_digits` over Perennial's translation of `internal/strconv.Atoi`'s fast path and
  `hyp.strconv.Atoi.wp_proof`, with the instance `atoiSpec_inst [strconv.Assumptions]`, which the
  `Results` modules import (so `AtoiSpec` is no premise of the results; they take
  `[strconv.Assumptions]`).
- **`fmt.Println`**: `hyp.fmt.Println.spec`, `class hyp.PrintlnHyp GF` (operands `printOk`:
  `ArgWf`, or `errAny` whose dynamic type does not implement `fmt.Formatter`, `typeSetContains
  ii.ty fmt.Formatter.ty = false`: Go calls a `Formatter`'s `Format` first); Perennial leaves
  `fmt.Println` untranslated. The proxy's accept routine prints its errors (`*net.OpError`,
  `*errors.errorString`: `NetAcceptLib`'s `opError_ptr_notFormatter`,
  `errorString_ptr_notFormatter`, under `[fmt.Assumptions]`, now a premise of the
  `NetworkInit` results).
- **`sort.Ints`**: `hyp.sort.Ints.spec`, `class hyp.SortHyp GF` (the lab's `wp_Ints`: a
  permutation into ascending signed order; precondition `isPkgInit pkg_id.sort`); Perennial leaves
  `sort.Ints` untranslated. Discharge:
  Perennial translates it, then the lab's proof over `slices.wp_Sort` applies.
- **`sync.Map`**: vocabulary `hyp.sync.MapVocab GF` (`own m M`, string keys; `tp`, the points-to
  of a `sync.Map` value), `class hyp.sync.MapHyp V` (`ivt`: `tp`'s `IntoValTypedUnderlying`,
  `own_timeless`, `own_zero` from `m ↦ zero_val sync.Map`, logically atomic `Map.Load.spec`,
  `Map.Store.spec`, `Map.Delete.spec`). The deployment's is `qv.map` (`QpVocab`'s field), whose
  `tp` is `sync.Map`'s instance (`StoreInst.lean`). The proxy's store packs a vocabulary and its
  hypothesis in `isStoreDef` (`∃ MV, ⌜MapHyp MV⌝ ∗ ...`, `Proxy/StoreDefs.lean`). `ivt` is a
  hypothesis about Perennial's model, not Go's library: it stands in for Perennial's `sorry`
  `TypedPointsto`/`IntoValTypedUnderlying` instances of `internal/sync.HashTrieMap`
  (notes/perennial-changes.md); `raxos.New`'s
  proof allocates with `qv.map` and takes `[MapHyp qv.map]`. (`ClientBatchStore.Range`,
  used by `Remove`-less paths only, has no spec: add one if a proof reaches it.)
- **bufio**: not a hypothesis: origin/dsv-bufio (75ef5881aa, revised after Upamanyu's review, merged
  here at 0493c6f8bc; not landed) is used directly: `EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz
  sent pend err` (the proxy's writers, `Proxy/SharedNet.lean`'s `wSlot`, size 4096), `ownBufReader br
  ri Pre S E R` (`Wire.lean`), specs `bufio.NewWriter.spec`, `Writer.Write/WriteByte/Flush.spec`,
  `Reader.Read.specOk`, laws `ownBufWriter_fact`, `ownBufReader_fact`, `ownBufReader_readerOk`,
  `net.conn_streamWriterOk`/`conn_readerOk` (`Net/Proof/net/ConnIo.lean`), `recvTokL_proto`. Never unfold
  the bufio predicates. If dsv-bufio changes again before landing, re-merge it.
- **Package initialization** (`<pkg>.InitHyp GF`, `Dsverify/Proof/<pkg>/Init.lean`): yaml.v2,
  go-redis, io/ioutil, encoding/gob, grpc, grpc/codes (names only, their variables' initializers and
  `init` functions untranslated), math/rand (Perennial's translation leaves its initializers
  untranslated; the main tree's `opaqueInitsOk` axiom). No axiom and no trusted code for them.
- **go-redis, yaml.v2, io/ioutil, encoding/gob**: names only, never reached (benchmark mode 0; the
  configuration made in code). Their calls need no spec unless the proof must show them
  unreachable (it does: `Init`'s mode-1 branch is excluded by the configuration).
- `fmt.Printf` (the main tree's `Proof/fmt/Printf.lean`), `time.Sleep` (Perennial's), `net.Listen`
  (`Net/`): proved specs, used by `Replica/{Serve,Server}`.
- **math/rand**: `hyp.RandHyp` holds only `Seed` and the package-level `Intn` (`0 < n`). The
  audit's `NewSource`/`New`/`(*Rand).Intn` specs (true of a zero `Rand`, where Go panics, and
  claiming races safe) are deleted: QuePaxa calls them only when `isAsynchronous`, which the
  deployment never sets (`Proposer/Slots.lean`).
- `log` (`Println`, `Fatal`), `math/rand` (`Intn`, `Seed`), `os`
  (`Create`, `Exit`, `Stderr`), `fmt.Fprintf`, `sort.Ints`, `time` extras (the lab's
  `Harness/Proof/{log,math/rand,os,fmt/Extra,strconv/Atoi,sort/Ints,time/Extra}`): to check against
  Perennial's and the main tree's (`Proof/math/rand`, `Proof/strconv`, Perennial's `log`, `sort`)
  when the proof reaches them; hypotheses (in `Hyp.lean`) where missing.

## The statement and its premises

`quepaxa_remote_robust : quepaxa_remote_robust.spec` (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`). Every hypothesis is a visible premise, ∀-bound; no instance of
any `InitHyp` (or other hypothesis class) exists anywhere. The heap premises are stated for every
machine's heap over `remoteGF` at the deployment's local context, `heapAt G L` (rabia's form):

- `[GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]`, the twelve commands'
  `cmd.{orch,client0..5,server1..5}.Assumptions`, `net.FieldAssumptions`, `go.BasicIntoValInj`
  (paxos's list). The other packages' `Assumptions` the proofs use (`net`, `fmt`, `strconv`,
  `time`, `bufio`, `errors`, `io`, `log`, `strings`, remote's, lintest's, perclient's,
  `raxos/replica/src`, `raxos/proto/client`, `raxos/examples/quepaxanet`) are not separate
  premises: each command's `Assumptions` carries its imports' (`import_*_Assumption` fields,
  instances), transitively, and the proof finds them through it.
- `InitHyp remoteGF` of yaml.v2, go-redis v8, io/ioutil, encoding/gob, grpc, grpc/codes,
  math/rand (seven; each: Go runs the package's untranslated initializers without panicking).
- `∀ qv : hyp.QpVocab remoteGF` (the abstract gRPC and `sync.Map` vocabulary), then
  `hyp.PbHyp`, `hyp.RandHyp`, `hyp.UtcHyp`, `hyp.SortHyp`, `hyp.PrintlnHyp`,
  `hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc` (also for every `NetProtoGS`),
  `hyp.grpc.GrpcWorldHyp (Gg := G) qv.grpc` (for every global ghost state `G`),
  `hyp.sync.MapHyp qv.map`.
- `∀ σ g threads, DistDeploy quepaxaKitAddrs (system σ) g → Robust [] (system σ) g threads (2^63)`.

**Vacuity check** (by inspection): `DistDeploy` is satisfiable (`kitAddrs_nodup`, `kitAddrs_ok`
proved; the network and listener states' `init` are the empty ones). The premises are jointly
satisfiable in principle: each is a property of the real library on a Go global context that
gives the names-only functions (grpc, yaml, go-redis, ...) their bodies (the statement is ∀
`GoGlobalContext`/`go.Semantics`, and the commands' `Assumptions` fix only the translated
packages' unfoldings, so they do not clash with a body for a names-only function), the
vocabulary existentially chosen by a model (`GrpcWorldHyp` holds of any vocabulary whose
`worldOk` is fresh ghost state). Doubts: (1) **`MapHyp.ivt` is a claim about Perennial's model
of an opaque type, not about Go**: `sync.Map`'s field `internal/sync.HashTrieMap` is an
axiomatized type whose `TypedPointsto`/`IntoValTypedUnderlying` instances are `sorry`, and `ivt`
says the vocabulary's points-to `tp` is coherent with the semantics Perennial gives allocation,
loads and stores at that type. Its satisfiability depends on that semantics at opaque types, which
nothing here shows. Believed satisfiable: the semantics of an opaque type's memory operations is
the untyped one over its underlying value (`Perennial.sync.Map.underlying`), and the heap's
points-to over that representation (what goose generates for any translated struct, with
`solve_into_val_typed_struct`) meets it; Perennial's own instances, once given, would be one.
(2) `PbHyp` speaks of Perennial's translation of protobuf's `proto.Marshal`/`Unmarshal` (the main
tree's), which must actually behave as the real protobuf on QuePaxa's messages (the audit of
2026-11-23 checked the spec against Go's behaviour, not the translation's reachability). Its reps
were false of protobuf-go v1.36.12 until review #24's finding 2 was fixed ("Review #24" below:
`Msg.lean`'s `pt*`).
(3) `GrpcHyp`'s `Invoke` and `Serve` describe the lab's model's behaviour (audited against
grpc-go, "Hypotheses" above); `handlerOk`/`decOk` restated after review #24 to grpc-go v1.84's
server (below). (4) **`QpVocab` is fixed before the heaps**: the statement quantifies `∀ qv :
QpVocab remoteGF` outside the heap premises (`heapAt G L`), so a model of `qv.grpc`'s and
`qv.map`'s predicates (`own m M`, `isClientConn`, `srvOwn`, ...) cannot mention invariants or
ghost names allocated in a particular global ghost state `G` or heap. Believed satisfiable: each
predicate can be a ghost-only representation whose ghost names are carried in its arguments or
existentially inside it (`own m M` as an authoritative map element at a name stored in the
predicate's own existential, allocated by `own_zero`'s update; the gRPC world's registry name is
already the argument `W.reg`, allocated by `GrpcWorldHyp`), and the specs that need shared state
(`sync.Map`'s `Load`/`Store`/`Delete`) are logically atomic. Since `qv` is fixed before any heap,
`own` cannot carry an invariant across calls: a model needs a ghost-only or physical representation
(the map's cells themselves, or ghost state at a name inside `own`'s existential), reached through
the specs' update and atomic steps, not an invariant named by the vocabulary (review #24). `MapHyp.ivt`
remains an honest open doubt: a claim about Perennial's model at an opaque type, believed satisfiable.
Nothing here constructs such a model.

`etc/theorem-loc.py quepaxa_remote_robust --no-go`: `tcb 787` lines (582 before review #24's
finding 2: `Msg.lean`'s `fields*`/`rt*`/`pt*`), all statement premises (`tcb_premises 787`, `tcb_axioms 0`, `axioms 0`); `--list-tcb` lists the seven `InitHyp` classes
(6 lines each, `Dsverify/Proof/<pkg>/Init.lean:27-33`), `Hyp.lean`'s classes and specs
(`PbHyp` ... `GrpcWorldHyp`, `MapHyp`, `QpVocab`), `Msg.lean`'s encodings, `Proto.lean`,
`TopLevelDefs`. So the `InitHyp` premises are counted (dsv README's requirement, confirmed here).
(paxos's: 28.)

## State

**Done (2026-11-23)**: the whole port, prepared for landing. The Go, the translation, the
protocol's proof (`Replica`, `Proxy`, `Proposer` `Results`), the kit's proofs and links, the start,
the mains and **`quepaxa_remote_robust`** (`lake build Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness`
OK, and every module under `Dsverify/{Proof,Spec}/raxos/`; `#print axioms` Lean's three). No
`sorry` and no `axiom` declaration in `Dsverify/` (the generated
`GeneratedProof/google_golang_org/grpc/chunk*.lean` hold goose's `sorry -- axiomatized type`
instances of the names-only grpc's opaque types, which nothing reaches: `#print axioms`). The only
trusted code: the two descriptor-table init files (collection).

**Landing preparation (2026-11-23)**:
- **Import tiers**: `etc/tier-check.py --check` passes with no new baseline or `etc/tier-linking.txt`
  entry (the 19 raxos violations fixed, dsv-epaxos's pattern). The library callees of the proxy,
  replica and kit proofs are hypotheses, `Dsverify/Proof/raxos/LibDeps.lean` (defs tier, specs
  only): `QpBufioDeps` (bufio's `Writer.{Flush,WriteByte,Write}`, `Reader.{ReadByte,Read}`,
  `NewWriter`), `QpNetDeps` (`Conn.{Write,Close}`, `Dial`, `Listen`), `QpFormatIntDeps`,
  `QpPrintfDeps`; the modules take them as section variables (`MabCalc`, `NetDial`, `NetListen`,
  `NetSend`, `NetUnmarshal`, `Serve`, `Server`, `KitConn`, `KitRecv`, `KitWire`, `KitOp`,
  `KitNewClient`, `KitClient`); `Proxy/Results.lean` proves them from the libraries' proofs
  (`qpBufioDeps_holds`, `qpNetDeps_holds`, `qpFormatIntDeps_holds`, `qpPrintfDeps_holds`), local
  instances there, in `Replica/Results.lean` and in `examples/quepaxanet/Linked.lean`; no `instance`
  of them exists, and they are no premise of the statement. `io.ReadFull`'s local statements moved to
  `IoReadFullSpec.lean` (`NetSpecs` imports them, not the proofs); `Replica/Server.lean` uses
  `Proposer/Run.lean`'s `prop.wp_NewProposer`/`prop.wp_runProposer` (was `Proposer/Results`, a
  linking module).
- **Merged `lean` 20cfe852d5** (Perennial 71de6f043, `/shared/perennial-71de6f043`): conflicts only in
  go-redis's names-only translation and `Init`/`Base` and math/rand's `Init` (both kits add them;
  taken from `lean`, dsv-rabia's). `Proxy/NetAcceptLib.lean`'s `opError_resErr`: `net.OpError.Error`
  now maps an empty string to `"error"` (a branch). No local copy of dsv-protolaws' laws here (QuePaxa
  uses no `sentLb`).
- **go-redis**: one translation for both kits. dsv-rabia (landed) owns go-redis's names-only
  translation (`Dsverify/{Code,GeneratedProof}/github_com/go_redis`); `dsv-goredis` moved rabia's go.mod
  from v8.8.2 to **v8.11.5**, QuePaxa's version (pinning QuePaxa to v8.8.2 fails: v8.8.2 needs otel
  v0.19, grpc v1.84 a 1.x otel), and regenerated the translation. QuePaxa's goose project does not
  translate or own go-redis: its references resolve to that v8.11.5 translation, the version its
  go.mod builds with.
- Link namespace: the kit has no `Link.lean` (its links are `examples/quepaxanet/Linked.lean` and the
  `Results` modules, which `etc/proof_roots.py`'s `namespace()` does not read); `namespace()` stays
  `Perennial.EtcdGrove.`.
- Checks (2026-11-23, at Perennial 71de6f043): `PERENNIAL_DIR=/shared/perennial-71de6f043
  etc/gen-init.py --check` (266 files up to date), `etc/goose.py --check` (all projects up to date
  once go-redis left this project), `etc/copy-part.py --check`, `etc/tier-check.py --check`,
  `errorf-wrap-check`'s `init_errors()` `[]`, `etc/theorem-loc.py quepaxa_remote_robust --no-go
  --list-tcb` (tcb 582 then, 787 since review #24's finding 2; all premises, 0 axioms). `etc/tcb-report.py --collection
  etc/tcb-collections/dsv-quepaxa.txt --check` not run (it needs every root of the repository built;
  `etc/gates.sh` runs it).

Last session's changes (top level): `Hyp.lean` `GrpcHyp.world_alloc` → `class GrpcWorldHyp`
over `GooseGlobalGS`, `kit_start` takes it as an instance (was the premise `hW`); `Wire.lean`'s
unused `ClientBatch.Marshal.spec`/`Unmarshal.spec` deleted (`KitWire`'s `cbMarshal.spec` and
`NetUnmarshal`'s `unmarshalB.spec` are the ones used); new `TopLevelDefs.lean`, `Mains.lean`,
`TopLevelRobustness.lean` (Proof and Spec), `etc/tcb-collections/dsv-quepaxa.txt`.

Build: `PERENNIAL_DIR=/shared/perennial-71de6f043 etc/goose.py --project dsv-quepaxa`, `... etc/gen-init.py`,
`lake build Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness`.

## Design findings

- **remote's `ServeClient.spec`** takes `newClient` as a persistent triple with precondition `True`:
  a client that needs exclusive resources or must run once is made before `ServeClient` (as paxos);
  remote's `op` may overlap (retried reads): the lock invariant holds `s.next` with the counter's
  half; `tok sys` can be pure (kit fork 5).
- **Wildcard listeners**: the replicas listen at `0.0.0.0:port`; `Net/`'s bridge
  (`robust_of_distProtoRB`) only knows listed addresses, so dsv-epaxos's `epaxosnet/Bridge.lean`
  (formerly the kit's own `DistBridgeLis.lean`) adds the wildcards (`addrs_lis_start`, `lis_set_proto`; pairwise disjoint, none taking a listed address).
  A candidate for `Net/Statement/` (it is a copy with listeners).
- **Hypotheses over the global ghost state**: a hypothesis used at the start (before any machine's
  heap exists) must be a class over `GooseGlobalGS`, not `HeapGS` (`GrpcWorldHyp`).
- **`addrTok` is persistent in `Net/`** (exclusive in the lab): the proxy's uniqueness comes from a
  ghost token, not the address (Session log, "Design points found" 2).
- **`sync.Map`'s points-to is `sorry` in Perennial**: `MapHyp.ivt` stands in
  (`notes/perennial-changes.md`).
- Kernel rejections from `omega` inside Iris proofs: factored into pure lemmas (`MabCalc`).

## Follow-ups

- Discharge the hypotheses as shared changes: protobuf (the kit's codec from
  `models/protobuf/pbgen.py`), gRPC's unary path (the Lean half of `models/grpc`, phase 7 S2),
  `sort.Ints` (Perennial's translation + the lab's proof over `slices.wp_Sort`), `time.Time.UTC`,
  `fmt.Println`, math/rand, `sync.Map` (Perennial's `HashTrieMap` instances), the `InitHyp`s.
- epaxos's `Bridge.lean` (`robust_of_distProtoLisRB`, which QuePaxa now uses) into `Net/Statement/`,
  since two kits need wildcards.
- One go-redis version for QuePaxa and rabia (the State's "go-redis").
- The per-function spec/proof layout and generated Links, as paxos's follow-ups.

## Review #24 (Upamanyu, of f3c69b4f7a; 2026-11-23)

Verdict "not ready": `GrpcHyp.handlerOk` was false of grpc-go v1.84.

- **Finding 1 (high), fixed.** The old `handlerOk` handed the handler the caller's deposit
  `S bs Φ` before `dec`. grpc-go v1.84 wraps a unary method as a stream handler
  (`server.go:810-812`, `wrapUnaryHandler` `server.go:1281-1289`: `dec` is `stream.RecvMsg`) and
  `processRPC` calls it as soon as the headers arrive (`server.go:1446-1450`), before any request
  bytes; the client queues HEADERS in `newClientStream` (`call.go:70`) and only then marshals in
  `SendMsg` (`stream.go:1072`, `prepareMsg`), which can fail (invalid UTF-8). A method with
  `S := False` and a handler that panics before `dec` was covered as safe. Now (`Hyp.lean`):
  `handlerOk impl h S` gives the handler the context and `decOk V S Got dec` for an arbitrary
  receipt `Got : (List w8 → IProp) → IProp`, and asks, on a nil error, `∃ Φ, Got Φ ∗ replyOk reply
  Φ`; `decOk` (one use, no longer persistent) takes the codec's premise for every byte string
  (`∀ bs, unmarshal bs v (Ψ bs)`) and returns nil with `∃ bs Φ, S bs Φ ∗ Got Φ ∗ Ψ bs true`, or a
  `handlerErr` error with `v` decoded or failed (`∃ bs b, Ψ bs b`: `serverStream.RecvMsg`
  `stream.go:1891-1971` decodes, then reads again expecting EOF) or the premise back. Only `dec` makes
  a `Got Φ`, so a handler can succeed only after `dec` did, and holds nothing of the caller's
  before. `Invoke`'s statement is unchanged (its doc now says the handler may run with no request).
  QuePaxa's three handler proofs (`Replica/Handlers.lean` `esp_handlerOk`, `Replica/Fetch.lean`
  `fetch_handlerOk`, `inform_handlerOk`) adapted directly: the generated handlers call `dec(in)`
  first.
- **Finding 2 (medium), fixed (2026-11-23).** `PbHyp`'s reps (`Msg.lean`) held `l ↦{dq} x` for
  any `dq`, but `proto.Marshal` stores every message's `sizeCache` (protobuf-go v1.36.12
  `internal/impl/encode.go:67,123,128`, `atomic.StoreInt32`, reached through `proto/encode.go:183-190`
  (`Size` first) and `codec_field.go:160,164` for sub-messages; also through gRPC's codec,
  `encoding/proto/proto.go:51-64`, `proto.Size` then `Marshal` with `UseCachedSize`) and its
  `state` on first reflection (the generated `ProtoReflect`, `proto/encode.go:111`;
  `internal/impl/pointer_unsafe.go:207-208`, `StoreMessageInfo`, `atomic.StorePointer`); it only
  reads the other fields.
  - **The fix** (`Msg.lean`, "Ownership of a message"): every message in a rep is `pt* l dq x`:
    with `dq = 1` the whole struct `l ↦ x` (so the runtime fields are owned, existentially, and a
    whole-message copy is a plain struct load); with any other `dq`, `fields* l dq x` (every field
    but `state`/`sizeCache`, field by field, with `dq`) and `inv pbRtN (rt* l)` (the two runtime
    fields, owned by the invariant; protobuf's stores are atomic, so a marshal opens it per
    store). `marshalPre`/`unmarshalPre`/`PbHyp`'s statements are unchanged in shape: `Marshal` gives
    the rep back, which is true now (at `dq = 1` the existential `x` covers the new runtime fields;
    shared, the other fields are unchanged and the invariant is kept), and `Unmarshal` produces
    owned (`dq = 1`) reps. `pt*_persist`/`pt*_share` (sharing allocates the invariant: a fancy
    update, so the persist lemmas `rep*_persist`, `repList_persist`, `repCBVal_persist`,
    `repDResp_persist` are now `|={E}=>`), `pt*_own`/`pt*_shared` (the two cases), `pt*_not_null`,
    `pt*_fields`, and `Access` instances (priority high; `Access`'s `P` is an input, so they apply
    only to a `pt*` hypothesis) for field loads from a `pt*` at any `dq`.
  - **The copy sites** keep owned messages: the proxy's incoming batch (`incomingP`) is now
    `repCB l 1 b` (was `.discard`), and `Run` copies `*clientBatch` from `l ↦ x` and only then
    persists the copied value's slices (`repCBVal_persist`); the proposer's replies
    (`repRR_persist`, `rpRep`) and the other copies were already of owned messages.
  - **Shared messages** (fresh allocations given to several goroutines or persisted: the proposer's
    requests and their `Proposal`, `ClientBatch`, `DecidedSlot` sub-messages, `FetchBatches`'
    `DecideRequest`, `InformDecision`'s `Decisions`, the replica's replies, the proxy's answers)
    are made `.discard` by `pt*_share` where the proof used `ipersist`. The proxy's answers
    (`sendClientResponse`, `&batches[i]` marshalled by the writers while the loop reads
    `batches[i].Sender`) are shared element by element (`ownSlice_elems`, `Proxy/Defs.lean`;
    `wp_sendClientResponse` takes the elements' `ptCB … .discard`). `wp_espImpl` reads the
    proposal from `ptProp pl .discard pv` (was `pl ↦{dq} pv`).
  - **Consequences**: a shared rep holds an invariant, so it is not timeless: the store's entries
    (`storeEnt`) lost their `Timeless` instance, and `Get` strips the later from the entry after the
    load (`later_exists_except0`, then `wp_auto`'s pure steps). `etc/theorem-loc.py`: tcb 787 (was
    582).
  - **History**: the review's suggestion, reps of the user fields only, was tried on the local
    branch `dsv-quepaxa-pbfields-wip` (a535c13b2d, not pushed; its `fields*` predicates are reused
    here) and stopped: (a) QuePaxa copies whole messages (16 struct loads of message types), which
    read `state`/`sizeCache` too; (b) a precondition that leaves the runtime fields out is still
    not true if a caller can frame their points-to. Owned reps (the whole struct) answer (a), the
    invariant answers (b).
  - **The race question is answered: QuePaxa has no data race here** (the investigation of
    2026-11-23, at 21a8aca145). (i) Go's race detector (go1.27.3, `-race`, nodes too) reported
    nothing: `go test -race ./examples/quepaxanet -run TestDeployment -count=3` with three
    configurations, four more `QPNET_CONF`s (server modes 0 and 1, leader mode 2), and the fork's
    own tests; a planted copy of a proposal while `ESP` marshals it (a goroutine copying `pi` into
    a channel) was reported on every server node, so the detector reaches the nodes. (ii) By
    reading, none of the 16 whole-message copies is of a message marshalled or reflected at that
    point or later: each is freshly unmarshalled and handed over through a channel, or a local value
    never marshalled; every marshalled request is allocated for its send (`&ProposerMessage{…}`
    with `P: &pi`, `pi` the goroutine's own copy); grpc-go v1.84 marshals synchronously in
    `Invoke` (`call.go:75` → `stream.go:1072`), so nothing is marshalled after `ESP` returns. The
    memory several marshals share — the `Proposal`'s `ClientBatches` and the `DecidedSlots`
    sub-messages in every goroutine's request, the proxy's answers — is never copied whole:
    concurrent marshals of it are atomic/atomic stores plus plain reads of other fields, no race.
    (iii) `go vet`'s 31 copylocks warnings are protobuf's do-not-copy lint, not races. (iv) The
    lab's proof did not have to show any of this because its protobuf model
    (`harness/rpcmodel/protobuf`) has an empty `MessageState` and a read-only codec; the gap was in
    the model, not a missed bug. No Bug to report.
- **Finding 3 (low), recorded** in the doubts above ((1) `MapHyp.ivt`, (4) `QpVocab`).
- **Finding 4 (low).** `origin/lean` (b6ad6a8f54) has no `robust_of_distProtoLisRB` (dsv-epaxos has
  not landed), so `DistBridgeLis.lean` stays: a copy, apart from namespace and doc, of the first two
  theorems of dsv-epaxos's `epaxosnet/Bridge.lean`. Whichever lands second replaces its copy by
  the first's (or both move to `Net/Statement/`). **Done (2026-11-23, after merging lean
  `d1c432a3ca`, which has dsv-epaxos):** the statements of `robust_of_distBootLisRB` and
  `robust_of_distProtoLisRB` in the two files were identical (binders, hypotheses, conclusion), so
  `DistBridgeLis.lean` is deleted and `TopLevelRobustness.lean` imports epaxos's `Bridge` and applies
  `github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.robust_of_distProtoLisRB`
  (a defs-tier module importing only `Net.Statement.DistBridge`; tier-check unchanged).
- **Landing lessons (coordinator, 2026-11-23).** Duplicate declarations: every declaration of the
  files this branch adds was compared with every declaration of the repository's `.lean` files
  (namespaces resolved by a script); the only shared names are the names-only grpc translation
  (`Dsverify/Code/google_golang_org/grpc{,/codes,/status}.lean` vs the main tree's `Code/...`) and
  protobuf/grpc `Init` names, which are part copies (as `RaftNoAx/`'s); none of them is in the
  import closure of `Dsverify/` together with its twin (checked over the closure of every
  `Dsverify/` module), and none clashes with `origin/dsv-epaxos`'s files. No `log`, `net`,
  `bufio`, `io`, `sort`, `time`, `fmt`, `strconv` or `io.ReadFull` spec is declared twice (QuePaxa's
  library hypotheses live in `Perennial.raxos.hyp.*`). Link files: QuePaxa has no `Link.lean`
  (its links are `Linked.lean` and the `Results` modules); `proof_roots.namespace()` prints
  `Perennial.EtcdGrove.`.

## Which lab run

`quepaxa-bump-1` (dsverify-lab `master` `915f964`, `examples/quepaxa/SOURCE.md`): proof `4ae902e`
(tag `final`), fork `77b5258`, harness `cd3a97b` (lab commit `71cae38`), Perennial `3afd77e35`;
verified there in 671 s (`verify-final.log`).

## Session log (the port's history, newest last)

- Done: the Go (commit `0fbd49207a`; the fork's files byte-identical to the lab's since the
  dsv-infra merge: goose's `expand_comment_tabs` expands the tabs of Go comments, which Lean rejects,
  in the translation); the translation, building (`28eddbe98d`); `Pure/Conf`, `Pure/Consensus`; the package facts and
  initialization, all twelve `PkgTable`s building (`0e2763910c`).
- Configuration: `etc/dsv/quepaxa.py` (dsv-infra's per-kit file: goose project, gen-init lists and
  `special(g)`).
- Build: `PERENNIAL_DIR=/shared/perennial-7b2259a12 etc/goose.py --project dsv-quepaxa`, then
  `PERENNIAL_DIR=... python3 etc/gen-init.py`, then `lake build
  Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.PkgTable` (and the other eleven).
- Done (this session, 2026-11-23): **the kit model's proof** (`Model.wp_proof`, no sorry);
  `Msg`, `Ghost`, `Cons/*`, `Smr/{OpId,SumId,Exec}` ported and building (`etc/lean-check.py -a`).
- **`Ghost.lean`'s changes** (the remote re-basing): a request's update is `opAU γ inp Φ`
  `= |={⊤ \ raxosN, ∅}=> ∃ σ, ownState γ σ ∗ (ownState γ (kvB.step inp σ).1 ={∅, ⊤ \ raxosN}=∗ Φ
  (kvB.step inp σ).2)`, exactly `remote.lin` of the kit's store (to be `lin_opAU` in `Kit.lean`,
  definitional as paxos's: `RBase` with `B := kvB`, `sysState := ownState γ`, `Eop := ↑raxosN`,
  `iv i := inV ⟨i.put, i.k, i.v⟩`, `ov o := outV ⟨false, o.found, o.v⟩`, `unk _ := outV ⟨true,
  false, []⟩`, `encIn`/`encOut` `EncIn`/`EncOut`'s bytes); the registry holds `opUpd` (a put's
  `opAU`, a get's `□ opAU`: remote's `slotUpd`) and a saved `Φ : KOut → IProp` (in place of the
  lab's `Q σ σ' o`); executed: `▷ Φ o ∨ token tok`. `Ticket`/`tixAt`/`rdCtr`/`Rd` use the net
  extension's connection numbers (`Nat`) and `netFresh (extGlobalGS netExt) cid true` (exclusive
  by `netDir_excl`; `netFresh_timeless` in `Ghost.lean`) for the lab's `NetConn.connFresh`.
- **PkgState (done)**: `raxos/replica/src`'s package fact is the lab's `srcState` (the
  `Consensus_ServiceDesc` points-to: its three methods with their generated handlers, no streams;
  `Dsverify/Proof/raxos/replica/src/Base.lean`), proved by the generated `Init.lean` through
  `etc/dsv/quepaxa.py`'s `special(g)` entry (`before['$inits']` keeps the methods' slice literal,
  `finish` frames the fact).
- Done (2026-11-23, second session): `Smr/{Step,Register,Laws}` (a request's update fires by
  `opAU_commit`, paxos's shape, from any mask holding `⊤ \ raxosN`; `smr_exec_slot` shrinks to it
  after opening `smrN` (`raxos_mask`); the registry saves `Φ : KOut → IProp`; `op_register` takes
  `opUpd`, `op_collect` gives `Φ o`); `Hyp.lean`; `Proto.lean`; `ReplicaDefs.lean`; the replica's
  interface layer `Proxy/{Pure,StoreDefs,StateDefs,OwnProp,SharedNet,SharedLoop,ProxyState,Slots}`,
  `Replica/{Defs,Slots}`, `Proposer/Slots`, `Replica.lean` (the specs of `NewProxy`,
  `Proxy.NetworkInit/Run`, `NewProposer`, `runProposer`, `New`, `Server.NetworkInit/StartProposers/
  Run`), `Wire.lean`. All check with `etc/lean-check.py -a`; `lake build
  Dsverify.Proof.raxos.Smr.Laws` built. The lab's `StoreInst.lean` is not needed (Perennial's
  generated `ClientBatchStore` points-to has no sorry here); `PkgState.lean` not ported (below).
- Common edits beyond the helper (`etc/dsv/tools/quepaxa-port.py`, which now also maps imports,
  `NetConn` → `Net`, `isClientConn`): add `[π : NetProtoGS] [qv : hyp.QpVocab GF]` to every HeapGS
  section that mentions `netProtos`/`sharedFacts`/`peersP`; drop the lab's `codecSet`/`kitCodecOk`
  conjuncts (protobuf is a hypothesis: no resource) and `nodeIp` (`Net/` has none); addresses
  `portAddr (76xx)` (`Proto.lean`), listen addresses `"0.0.0.0:" ++ decStr port`; a `Countable` of a
  protobuf message encodes `state'`'s `DoNotCompare'`, `DoNotCopy'`, `atomicMessageInfo'`
  (`Proxy/SharedLoop.lean` has the instances for `NoUnkeyedLiterals`, `sync.noCopy`, `sync.Mutex`).
- **Design points found**:
  1. **Wildcard listeners** (settled for the recorder, open for the proxy). The replicas listen on
     `0.0.0.0:port`, the dialers dial `127.0.0.1:port`. Recorder: `netProtos` holds, per recorder
     `r`, `recLisP qv.grpc (world γ) r := lisProto (recLis r) (reqProto W (recAddr r)) (respProto W
     (recAddr r)) ∗ worldOk W` (`Proto.lean`; `recLis r = "0.0.0.0:" ++ decStr (7626 + r)`), in
     place of the lab's `grpcAddr (recAddr r)`; dialers get `grpcAddr` from it
     (`recLisP_grpcAddr`, `lisProto_addr`, `Replica/Serve.lean`); `wp_serve` listens by
     `listen_lis_au` and gives `Serve` the listener's `lisProto`. **The kit's start must set it**:
     `addrs_lis_start` with the recorders' (and proxies') wildcards in `las` and their dialed
     addresses out of `addrs` (`hdisj`), then `lis_set_proto` per wildcard. Proxy (`Proxy/NetAccept`,
     to port): the same with `accept_lis_au`; `netProtos`' `addrProto (proxyAddr k)` must become a
     `lisProto` of `"0.0.0.0:" ++ decStr (7606 + k)` likewise.
  2. **`addrTok` is persistent** in `Net/` (exclusive in the lab). The recorder needs none (its
     `addrTok (recAddr k)` is gone from `replicaRes` and `srvRecorder`). Still there:
     `addrTok (proxyAddr k)` in `replicaRes`, `srvRecorder` and `Proxy.NetworkInit.spec`, for
     `sharedNet`'s invariant `netOwn pr rm ∨ addrTok (proxyAddr k)`: its swap no longer proves a
     second caller cannot exist; replace it by a ghost token of the proxy's (or `lisUnset` of its
     wildcard) when porting `Proxy/NetAccept`.
  3. **PkgState**: done (above).
- Done (third part of this session): `Proposer/*` (all; `Results`' `NewProposer.wp_proof`,
  `Proposer.runProposer.wp_proof` take `[GrpcHyp (cd := hyp.qpCodec) qv.grpc] [hyp.RandHyp GF]`;
  `#print axioms`: Lean's three); math/rand's hypotheses (`hyp.RandHyp`, `Hyp.lean`); `Proxy/Store`
  (`store_add_proof`, `store_get_proof` over `MapHyp`; `isStore_alloc_proof` from `MapVocab.zero`);
  `Replica/{RecDefs,ReqPersist,Helpers,EspImpl,HandleESP,Handlers,Fetch}` (`esp_handlerOk`,
  `fetch_handlerOk`, `inform_handlerOk`: the recorder's three methods meet `handlerOk qv.grpc`).
  `lake build` of `Replica.Fetch`, `Replica.Handlers`, `Proxy.Store`, `Proposer.Results`, `Smr.Laws`,
  `Proxy.Slots`, `ModelProof`: OK. `RecDefs` no longer imports `Proxy.Results`/`Proposer.Results`
  (it used neither).
- **`sync.Map`'s points-to is `sorry` in Perennial** (settled): `StoreInst.lean`'s high-priority
  instances over `qv.map.tp`/`MapHyp.ivt`; files that step through `ClientBatchStore` code erase the
  generated instances (`attribute [-instance]` block of `Proxy/Store.lean`, `Replica/Server.lean`);
  `notes/perennial-changes.md`.
- Done (2026-11-23, fourth part): `Replica/Serve` (`consensus_descOk` from `srcState` and the three
  `handlerOk`s; `wp_RegisterConsensusServer`, `wp_serve`, `wp_Recorder_NetworkInit`; address
  lemmas `recLis_k`, `recAddr_ok`, `recLis_listenOk`, `decStr_small`), `Replica/Server`
  (`wp_Server_Run`, `wp_Server_NetworkInit`, `wp_setupgRPC`, `wp_createProposers`,
  `wp_Server_StartProposers`, `wp_NewRecorder`, `wp_make_bag`, `wp_New`), `Replica/Results`
  (`New.wp_proof [MapHyp qv.map] [GrpcHyp] [RandHyp] [AtoiHyp] (hNP : NewProxy.spec)`,
  `Server.NetworkInit.wp_proof (hNI : Proxy.NetworkInit.spec)`, `Server.StartProposers.wp_proof`,
  `Server.Run.wp_proof (hRun : Proxy.Run.spec)`: the proxy's three entry points are premises
  until `Proxy/` is ported). `#print axioms` of all four and of `wp_serve`, `consensus_descOk`:
  Lean's three. **Not ported (subsumed)**: the lab's `Replica/{Init,Inits,HarnessInit}.lean` (its
  `src_initialize'` from its imports' initializers, the harness's grpc/protobuf initializer
  proofs): the generated `raxos.replica.src.wp_initialize'` and the `InitHyp`s replace them.
  `lake build Dsverify.Proof.raxos.Replica.Results Dsverify.Proof.raxos.Replica
  Dsverify.Proof.raxos.Proxy.Slots`: OK.
- Done (2026-11-23, fifth part, the Proxy group's first half): `Proxy/{Kv,Exec,Defs,Send,SumPure,
  SmrGhost,Usm,Issue,MabSpecs,SliceLit,MabCalc,MabLeader,RunDefs,RunClientBatch,RunClientBatch2,
  RunFetch,RunLoop,RunNotify,RunTimer,RunSmrHelpers,RunRemove,RunDecideGhost,RunSmrCode,RunDecide,
  RunRecorder,RunProposeLemmas,RunSummary,RunPropose,Run}` and a new `Proxy/Results.lean`
  (`Proxy.Run.wp_proof [AtoiHyp] [SortHyp] [strconv.Assumptions] [time.Assumptions]`). With it
  `Replica/Results`' `Server.Run.wp_proof` has no `hRun` premise any more. `#print axioms` of
  `Proxy.Run.wp_proof`, `Server.Run.wp_proof`, `New.wp_proof`, `Server.NetworkInit.wp_proof`,
  `wp_calculateSequence`, `wp_updateEpochTime`: Lean's three. `lake build
  Dsverify.Proof.raxos.Replica.Results`: OK. Changes against the lab:
  * `sort.Ints` is a hypothesis, `hyp.SortHyp` / `hyp.sort.Ints.spec` (`Hyp.lean`; the lab's
    `wp_Ints` shape). Perennial leaves `sort.Ints` untranslated; the lab had translated it itself.
  * `strconv.FormatInt` uses the main tree's proved `EtcdGrove.strconv.FormatInt.wp_proof`
    (`fmtInt`). `MabCalc`'s `fmtInt_digit` and `wp_FormatInt_digit` restate it as the lab's
    one-digit spec, so the lab's loop proof is unchanged. (Using `fmtInt` directly in the loop
    proof made the kernel reject `wp_calculateSequence`: an auxiliary `omega` proof was
    abstracted over a different context.)
  * `time`: Perennial's `Proof/time/{Link,Results}` (`time.wp_Now`, `Time.wp_ptr_Sub`,
    `Duration.wp_Microseconds`) in place of the lab's `time.Extra`.
  * `strconv.Atoi`: `ha.Atoi` (`hyp.AtoiHyp`); `strconv.smallDigits`/`decVal` are `hyp.strconv.*`.
  * `proxySharedDef` lost the lab's `storeAssm` existential, so its destruct patterns lose
    `%_h`. `sharedFacts` lost the two codec conjuncts, so its 9-place patterns lose places 7-8
    (`scratchpad sf.py`'s rule, now in `etc/dsv/tools/quepaxa-port.py` for `%_h`).
  * `Run.lean`'s `run_proof_of` drops the lab's unused `[raxos.examples.quepaxanet.Assumptions]`.
  * MabLeader's section `variable [ha : hyp.AtoiHyp GF]` makes every theorem there (and in the
    Run* files that add the same variable) take `AtoiHyp`. That is harmless, since the statement
    takes it anyway.
- **Proxy network side and constructor (third Proxy session, 2026-11-23)**. Done, each
  `lean-check -a` clean and `lake build` of `Proxy.{NetDial,NetSend,NetListen,NewProxy}` and
  `IoReadFull` OK; `#print axioms` Lean's three for `newProxy_proof`, `connectToClient_proof`,
  `internalSendMessage_proof`, `startOutgoingLinks_proof`, `connectionListener_proof`,
  `unmarshal_bounded`, `marshal_buf`, `ioLt.ReadFull.wp_proof`:
  * `MsgBuf` (`marshal_buf` over `PbHyp`; the lab's `WireProof` lemmas on little-endian lengths
    moved here; the lab's `WireProof` proofs of `Wire.lean`'s specs over the lab's bufio are
    dropped: the kit's client proves `ClientBatch.Marshal/Unmarshal.spec` over the landed bufio
    when `Kit/` is ported; note that `Wire.lean`'s `Marshal.spec` must then also ask `Q` of the
    length prefix (`ownBufWriter`'s prefix closure is sealed) and `Unmarshal.spec` should take the
    stream fact `Φ` as `NetUnmarshal`'s `unmarshalB.spec` does);
  * `NetSpecs` (the statements: `connectionListener.spec` over `ownBufReader br ri Pre (recvTokL cn
    true (proxyInProto γ k)) E (hs (21+cl))`; `waitForConnections.spec` takes `netTok γ k`),
    `NetFrames` (`recv_frames` over `protoPrefix`), `NetUnmarshal` (`unmarshalB.spec`: the length
    bound from a prefix-closed stream fact `Φ` that `S` gives a step later; Perennial's
    `io.wp_ReadFull` over `bufio.ownBufReader_readerOk`), `NetReader` (`reader_code/len/frame`
    over `protoPrefix`, the reader's pending buffer is never looked at), `NetListen`
    (`connectionListener_proof`, `net.connReader_proto` after each read), `NetWriter` (only
    `clientInProto_prefixClosed : ProtoPrefixClosed`; the lab's sticky `WriteByte` and
    `marshal_strong` go), `NetSend` (`internalSendMessage_proof` over the landed `WriteByte`/
    `Write`/`Flush` specs), `NetDial` (`connectToClient_proof`: `net.Dial.wp_proof` with
    `dial_au`, `net.Conn.Write.wp_proof` with `writeP_init`/`write_acc`, `Close` with `close_au`,
    `net.conn_streamWriterOk` and `bufio.NewWriter`; `ed` from `examples/net/wire`'s `ed_of_poll`);
  * `NewHelpers`, `NewOwn`, `NewShared`, `NewProxy` (`newProxy_proof [AtoiHyp] [UtcHyp] [RandHyp]`:
    `NewProxy.spec`; `np_sharedNet` allocates `inv netN (netOwn pr rm ∨ netTok γ k)`).
  * **The wildcard and the token** (done): `netProtos`' proxies' conjunct is `lisProto (proxyLis k)
    (proxyInProto γ k) silentProto` (`Proto.lean`, `proxyLis k = "0.0.0.0:" ++ decStr (7606+k)`);
    clients get `addrProto (proxyAddr k)` by `lisProto_addr`. `addrTok (proxyAddr k)` is replaced by
    `netTok γ k := ghostMapElem γ.net k (own 1) ()` (`Ghost.lean`, new field `QNames.net`,
    `netTok_excl`) in `replicaRes`, `srvRecorder`, `Proxy.NetworkInit.spec`, `sharedNet`'s
    invariant: the kit's start must allocate `γ.net` with keys `1..5` and hand `netTok γ k` to
    replica `k`.
  * **New hypotheses** (`Hyp.lean`): `hyp.time.Time.UTC.spec`, class `hyp.UtcHyp` (Perennial
    leaves `time.Time.UTC` untranslated, `Perennial/Code/time.toml`; the lab's `Time.wp_UTC`).
  * **Local copy of a Perennial branch**: `Dsverify/Proof/raxos/IoReadFull.lean` is Perennial
    `readatleast-prefix` (`af905abba`)'s `io.ReadAtLeast`/`io.ReadFull` specs and proofs under
    `raxos.ioLt.*` (premise only at the reads made): `waitForConnections`' `io.ReadFull(conn, bs)`
    needs it (a connection's `conn_readerOk` refuses empty reads). Drop it at the pin bump.
  * **The proxy's network side is done** (third Proxy session, 2026-11-23): `NetPrint`
    (`wp_Println_ok` from the hypothesis `hyp.fmt.Println.spec`, `printOk_str_err`),
    `NetAcceptLib` (`proxyLis_1..5`, `proxyLis_listenOk`, `hs_of_prefix`, `net_claim` over
    `netTok`, `errAny_resErr'`/`errAny_newVar'`/`readFull_errAny`: the printed errors are
    `errAny`, local copies of `net.rpc`'s lemmas without `net.rpc.Assumptions`), `NetAccept`
    (`waitForConnections_of`, the library specs as parameters: `net.Listen` with `listen_lis_au`
    on `proxyLis k`'s `lisProto`, `net_claim`, `Listener.Accept` with `accept_lis_au`,
    `rd_alloc_top` from `connFresh`, `ioLt.ReadFull` over `net.conn_readerOk`, the handshake from
    `recvTokL_proto`'s `protoPrefix`, `bufio.NewReader.specOk` with `preUpTo_of_pure`, `Conn.Close`
    with `close_au` on a failed handshake), `NetInit` (`networkInit_of`); `Proxy/Results`:
    `NewProxy.wp_proof`, `Proxy.NetworkInit.wp_proof` (composing `net`'s, `IoReadFull`'s and
    bufio's proofs); `Replica/Results`: `hNP`/`hNI` discharged (`New.wp_proof`,
    `Server.NetworkInit.wp_proof`, `Server.Run.wp_proof` take only hypothesis classes and
    `Assumptions` instances). `#print axioms` of all of them: Lean's three.
  * **`consInv`'s fresh-connection token is `Proto.lean`'s `connFresh`** (what `accept_lis_au`
    gives), in place of the raw `netFresh`: `consInv` takes `[NetProtoGS]`; `rd_alloc`
    (`Cons/Laws`) refutes a second allocation with `connFresh_excl` and takes `[GoGlobalContext]`;
    `Cons/{Lemmas,Laws}`, `Smr/Laws`, `Proxy/Issue`, `Proposer/Pure` gained `[π : NetProtoGS]`.
  * **New hypothesis** `hyp.fmt.Println.spec`, class `hyp.PrintlnHyp GF` (`Hyp.lean`; operands
    `hyp.fmt.printOk`: `ArgWf` or `models_lab.errAny`; the lab's `wp_Println_ok`). Perennial leaves
    `fmt.Println`/`Fprintln` untranslated. Discharge: Perennial translates them and proves this
    from `printArg` as `Printf`'s spec (`argOk` under `%v`).
  * Not ported: the lab's `Proxy/WireProof.lean` (`ClientBatch.Marshal`/`Unmarshal`, `Wire.lean`'s
    specs): the proxy does not use them (it marshals into a `msgBuffer`); the kit's client will
    (see the second Proxy session's finding: `Marshal.spec` must ask `Q` of the 8-byte length
    prefix; `Unmarshal.spec` should take the stream fact as `unmarshalB.spec`).
  * Import tiers: no new violation (`etc/tier-check.py`: 19 non-scratch `raxos` violations, as
    before: 18 defs->proof, 1 defs->linking).
- **Kit design point found before porting `Kit/*` (2026-11-23, kit fork; nothing of the kit
  written yet)**: remote's `RBase` needs `encIn_len : ∀ i, (encIn i).length < 2^63`, and
  `codecOk` asks `EncIn(iv i)` to return exactly `encIn i` for *every* `i : I`. The kit's `KIn`
  (`Pure/Smr.lean`) has unbounded strings, so `I := KIn` cannot satisfy `encIn_len` (`EncIn`'s
  bytes are `1 + 8 + |k| + 8 + |v|`). paxos bounds its inputs (`BStr`, `bnd`). And `kit.go`'s
  `result` reads a get's value at `r[1+KeyLen:]`, so the kit is only correct for keys of
  `keyLen` bytes (`inputOk`, which `Gen` meets). Two ways:
  (A) remote's `I := QIn := {i : KIn // inputOk i ∧ (i.k.length + i.v.length : Int) < 2^48}`,
  `qB : PendSpec Store QIn KOut` with `step i := kvB.step i.1` (so `lin_opAU` stays definitional:
  `opAU γ i.1 Φ`); but the porcupine model `qS` (`Model.lean`, `Pure/ModelSet.lean`, ~2k lines) is
  over `PSet Store KIn` and must be over `PSet Store QIn` (remote's `pendCtx`/`pendLib` take the
  same `I`): either restate `mSet`/`step_mSet`/`mSet_empty` for `QIn` (their proofs only use
  `i.put`, `i.k`, `i.v`: generalize `ModelSet` over a projection `I → KIn`), with `qDec` checking
  `inputOk` and the bound (`ioOk` asks them; `Gen.spec` gives them); or
  (B) give `KIn` itself the bound (a fourth, `Prop` field), touching every `KIn` literal in
  `Ghost`, `Smr/*`, `Proxy/Kv`, `Model*`. (A) leaves the protocol proof alone; recommended.
  Next for the kit, in order: `Kit.lean` (defs tier: `QIn`, `qB`, `qR γ` with `sysState :=
  ownState γ`, `Eop := ↑raxosN`, `iv`, `ov`, `unk`, `encIn`/`encOut` from `EncIn`/`EncOut`'s
  bytes, `lin_opAU`, the generalized model spec, `clientAddrs`, and `Model/Codec/Gen/Orch/Client/
  Server.spec` as paxos's `Kit.lean`); `KitProof.lean` (Codec: the byte loops of `appendStr`/
  `takeStr`; Gen: `mix`/`digit(s)`; Orch: `send`/`sendConf` (net.Dial, Write, `ioLt.ReadFull`,
  Close) and `remote.Check` with `Model.wp_proof`); Client (`awaitConf` (Listen/Accept with
  retry, as `Proxy/NetAccept`), `newClient` (replicas, `accept`/`receive` over bufio and
  `ClientBatch.Unmarshal` from `PbHyp`, `tryConnect`/`connect`/`send` with `Marshal`), `Op`
  (`opRegister`'s ticket and `op_collect`, the lab's `Kit/Op*`), then `remote.ServeClient`);
  Server (`awaitConf`, then `New`/`NetworkInit`/`StartProposers`/`Run` from `Replica/Results`, the
  `id > conf.N` branch sleeping forever); the start (`γ.net` with `netTok 1..5`,
  `addrs_lis_start` with the proxies' and recorders' wildcards, `lis_set_proto` for each,
  `NetProtoGS`); then `TopLevelRobustness.lean`.
- **The kit, session of 2026-11-23 (kit fork 2)**. Done:
  * **Option A taken**: `Pure/QIn.lean` (pure, generic): `subB B p` (a pending-writes store on a
    subtype of its inputs), `cmap`/`pre`/`AllP`; `ppost_sub`, **`pSeq_sub_step`** (`pSeq (subB B p)`
    on `pre S` is `pSeq B` on `S`, mapped by `pre`, when `S`'s pending inputs satisfy `p`),
    `AllP_step`, `pInit_sub`. `qInOk i := inputOk i ∧ |k| + |v| < 2^48`, `QIn := {i // qInOk i}`,
    `qB := subB kvB qInOk`. `ModelSet.lean` is unchanged (over `KIn`); the porcupine model `qS`
    (`Model.lean`) is now over `PSet Store QIn`: `qDecQ` (`qDec` and `qInOk`), `qRep`'s set is
    `pre (mSet (lk E))` with `AllP qInOk (mSet (lk E))`, `ioOk` asks `qInOk (kin x)`.
    `Model.wp_proof` re-proved (`lake build ...ModelProof` OK).
  * `Kit.lean` (defs): `QIn.countable`/`QIn.beq`, `flagB`, `strB` (`u64Le` length ++ bytes),
    `encInB`, `encOutB`, `qiv`/`qov`/`qunk`, `encOutV` (a boxed `Out`'s bytes **if they fit**
    `2^63`, else `[]`: no bound on outputs is needed; `EncOut`'s proof derives the bound from the
    slice it builds), **`qR γ : RBase GF Store QIn KOut`** (`sysState := ownState γ`, `Eop :=
    ↑raxosN`), `lin_opAU : lin (qR γ) i Φ ⊣⊢ opAU γ i.1 Φ := .rfl` (definitional, no `bnd`), the
    shares `sharedRes`, `orchRes` (`confTok ∗ sharedRes`), `ticketsOf`, `clientRes` (cnt half at 0,
    tickets, shared), `serverRes` (`netTok`, `recHalf`, `initFront`, shared), `clientAddrs`
    (`7661..7666`), and the specs `Codec.spec`, `Gens.spec`, `Orch.spec`, `Client.spec`,
    `Server.spec`. lean-check clean; `lake build ...Kit` OK.
  * `KitCodec.lean` (defs tier: no `wp_proof` names): `wp_flag`, `wp_appendStr`, `wp_takeStr`
    (success on `strB s ++ r`, the slice given back, the rest `slice.slice b (8+|s|) b.len`),
    `wp_EncIn`, `wp_DecIn`, `wp_EncOut`, `wp_DecOut`, `encOutV_outV`. `KitCodecFn.lean` (defs
    tier): **`codec_proof : Codec.spec`** (the seven closures; `DecOut` of an output too long to
    encode gets `[]` and fails, `wp_DecOut_nil`). `#print axioms` of `codec_proof`,
    `Model.wp_proof`, `pSeq_sub_step`: Lean's three. `lake build ...KitCodecFn` OK.
    (`encOutV_outV` needs `GoLocalContext`, so it sits in its own section as `Model.lean`'s `dec`;
    stated in the `HeapGS` section, the instance search did not end: the lean-check server hung.)
  * **Go changes to the kit** (`kit.go`, retranslated with `etc/goose.py --project dsv-quepaxa`,
    `gen-init --check` up to date, Go tests pass): (1) `Gens()` takes its counters under a
    `sync.Mutex`, index `c mod NC`: lintest's `genSpec` is persistent, for any `id ≥ 0` and
    concurrent calls (the old closure indexed `next[c]` unguarded: out of range for `c ≥ NC`, racy).
    (2) `Op` takes its sequence number under `s.mu` and sends **at most `K` requests**: past the
    budget it answers `Out{Unknown: true}` without sending.
  * **Design findings (remote vs the protocol proof)**: (a) remote's `ServeClient` runs `op` any
    number of times, possibly overlapping (its `svcOp` is persistent with `tok sys` from a
    `True`-precondition `newClient`; `Do` retries reads, and a retry may overlap the call it
    retries): the lab's `nextInv` (an exclusive `s.next` taken by the one running `Op`) and its
    per-operation `clientTok γ c j` do not fit; the client machine's invariant must hold `s.next`
    under `s.mu` (new lock invariant: `waiting` and `next` with the client's quarter of `γ.cnt`).
    (b) QuePaxa's protocol proof has a **finite ticket supply** (600 tickets: 5 replicas × 6 clients
    × 20 requests; `consInv`'s slot bound `spentLb ≤ 600`, `smrInv`'s `Cnt ≤ 20`): hence the Go
    budget (2). Neither needs a change to remote.
  * **Next for the kit, precisely**: (i) `Gens.spec` (`Gens`' closure: a `sync.Mutex` and the
    `next` slice in a lock invariant `next ↦* l`, `|l| = NC`; `Gen(c, j)`'s output meets `qInOk`:
    key `"key0000" ++ digit` (8 bytes), value `"v" ++ digit c ++ digits j` (nonempty, not `"nil"`,
    at most 22 bytes); `mix` is wrapping arithmetic, anything); (ii) `Orch.spec`: `New` (`choose`
    over `RandHyp.Intn`, `send`/`sendConf`: `net.Dial`, `Conn.Write` of `encConf c` under
    `confInProto` (the orchestrator turns `confTok` into `confIs γ c` first), `ioLt.ReadFull`,
    `Close`; retry loop), `time.Sleep`, `remote.Check` with `Model.wp_proof`, `codec_proof`, Gens,
    `PendDec (qR γ) qS` (from `qDecQ_box`, as paxos's `woS_pendDec`), `pendN`/`lintestN`
    disjoint from `raxosN`, `encOut` injectivity on `qov`, `qR_timeless`; (iii) `Server.spec`
    (`awaitConf` as `Proxy/NetAccept`'s accept loop over `confInProto`/`ackProto`, then
    `replicaRes` from `serverRes` + `confIs`, `config`'s `strings.Split` (a spec is needed:
    Perennial's?), `New`/`NetworkInit`/`StartProposers`/`Run` from `Replica/Results`; the `id > n`
    branch sleeps forever); (iv) `Client.spec` (the lab's `Kit/{NewClient,Recv*,Conn*,Op*}`,
    re-based: the lock invariant of `s.mu` holds `waiting` and `next` with the client's quarter of
    `γ.cnt` and the unused tickets; `ClientBatch.Marshal/Unmarshal` from `PbHyp` over dsv-bufio);
    (v) the start; (vi) `TopLevelRobustness.lean`.
- **The kit, session of 2026-11-23 (kit fork 3: steps 1, 2, 3 of the kit plan)**. Done, each
  `lean-check -a` clean, `lake build Dsverify.Proof.raxos.examples.quepaxanet.Linked` OK (2772
  jobs), `#print axioms` of `wp_Codec`, `wp_Gens`, `wp_Orch`, `wp_Server`: Lean's three; tiers: 19
  raxos non-scratch violations (none added); no sorry, no axiom, no new hypothesis:
  * **Design finding, fixed: the kit's outputs must be bounded.** `remote.Check` asks
    `∀ o o', R.encOut (R.ov o) = R.encOut (R.ov o') → o = o'`, and `RBase.encOut_len` bounds every
    encoding by `2^63`: no codec of the unbounded `KOut` is both (the previous `encOutV` sent every
    output too long to encode to `[]`). Now remote's `O` is **`QOut := {o : KOut // qOutOk o}`**
    (`qOutOk o := |o.v| + 2 < 2^63`, `Pure/QIn.lean`) and **`qB := outB (subB kvB qInOk) qOutOk
    qOut0`**: `outB` clamps a store's answers into an output subtype (`clampO`); on states of an
    invariant `g` whose outputs are in `q` (`OutInv`; `qB_outInv` with `shortSt`: every stored
    value below `2^48`, kept by the kit's inputs) it is the store itself (`ppost_out`,
    `pSeq_out_step`, `AllG_step`). `Model.lean`: `qDecQ` decodes to `Ans QOut` (`kansQ`,
    `ansVal_kansQ`), `ioOk` asks the output `qOutOk`, `qRep` keeps `AllG shortSt (pre (mSet (lk
    E)))` (`allG_pInit`); `ModelProof` re-proved (three small edits). `Kit.lean`: `qR γ : RBase GF
    Store QIn QOut`, `qov (o : QOut)`, **`lin_opAU : lin (qR γ) i Φ ⊣⊢ opAU γ i.1 (fun o => Φ
    (clampO qOut0 o))`** (still `.rfl`). For `Client.spec` (step 4): the client returns
    `outV ⟨false, f, v⟩` from the answer's result string, so it must show `clampO qOut0 o` is `o`,
    i.e. `qOutOk o`: `|v| ≤ |r|` and the answer batch is `batchFit` (`encBatch` below `2^63`).
  * `KitGen.lean` (defs): `wp_digit`, `wp_digits` (`opid.bstr (toString n)` = `decStr`),
    `wp_mix`, `wp_Gen` (`qInOk (kin x)`), **`gens_proof : Gens.spec`** (the lock invariant
    `gensInv sl`: `next ↦* l`, `|l| = 6`; `next` persisted after its store: `wp_alloc_auto`,
    `wp_store`, `ipersist`). Index arithmetic in `gens_idx` (an `omega` inside the Iris proof made
    the kernel reject it: keep such facts in separate lemmas, also `KitServer`'s `cv_*`, `srv_idx`).
  * `KitConf.lean` (defs): `decStr_76`, `cfgAddrsL`/`addrsL`/`recAddrsL` (`portAddr (76xx)`, their
    literals), `split_portAddr` (Perennial's `strings.split` of `127.0.0.1:76xx` at `":"`),
    `goConf`, `wp_CfgAddrs`, `wp_ClientAddrs`, `wp_attempt`, `wp_choose` (over `RandHyp.Intn`),
    `wp_encode`, `wp_String`, `wp_decode`, `wp_log_Println` (Perennial's trusted model of
    `log.Println` is `λ vs, #()`: proved, no hypothesis).
  * `KitAwait.lean` (defs): `confProto_of_shared` (node `n`'s configuration address's
    `addrProto … (confInProto γ) ackProto` from `sharedRes`), `confP γ` (the configuration channel's
    contract), **`wp_awaitConf_of`** (library specs as parameters: `Listen.spec_addrOk` with
    `listen_au`, `Accept.spec_addrOk` with `accept_au`, `ioLt.ReadFull` over `conn_readerOk`, the
    configuration from `recvTokL_proto`, `wp_decode`, `wp_bag_send` once, the ack under `ackProto`
    with `writeP`/`write_acc`, `close_au`).
  * `KitOrch.lean` (proof): `wp_closeConn`, `wp_sendConf_of` (`net.Dial` with `dial_au`, `Write`
    of `encConf c` under `confInProto` (`confIs γ c`), `ioLt.ReadFull` of the ack, `Close`),
    `wp_send_of`, `wp_New_of` (`confTok γ ==∗ confIs γ c`, `conf_choose`), `pendN_raxos`,
    `lintestN_raxos`, `qR_encOut_inj`, **`qS_pendDec : PendDec (qR γ) qS`** (stated in the
    `HeapGS` section: fine here), `pendCtx_qS`/`pendLib_qS` (`rfl`), **`Orch.wp_proof`** (premises
    `Model.spec`, remote's `Check.spec`, `net.Conn.Read/Write/Close`, `ioLt.ReadFull`, `net.Dial`
    specs; `[RandHyp]`, `[log.Assumptions]`).
  * `KitServer.lean` (proof): `peer_fields`, `client_fields`, `wp_Addrs`, `wp_RecAddrs`,
    **`wp_config`** (`cfg ↦□ cv ∗ cfgVal n cv`, over `strings.Split.spec`: Perennial's, no
    hypothesis), `wp_registerProto`, `wp_make_bag1`, `replicaRes_of` (`serverRes γ k ∗ confIs γ c ⊢
    replicaRes γ c k`), **`Server.wp_proof`** (awaitConf forked at `confAddr k`, the first
    configuration from the bag, `k ≤ c.n` → `raxos.New`/`NetworkInit`/`StartProposers`/`Run`; both
    branches end in the sleep loop).
  * `Linked.lean` (linking): `wp_Codec`, `wp_Gens`, `wp_Orch [RandHyp]`, `wp_Server [MapHyp]
    [GrpcHyp] [RandHyp] [UtcHyp] [PrintlnHyp] [PbHyp] [SortHyp]` (callees: `Model.wp_proof`,
    `EtcdGrove.remote.wp_Check`, `net.*.wp_proof`, `ioLt.ReadFull.wp_proof ReadAtLeast.wp_proof`,
    `strings.wp_Split`, `Replica/Results`).
  * **Next, precisely** (done since, kit fork 4 below): (5) **the start**. Two pieces. (a) **A bridge with wildcards is
    missing**: `Net/Statement/DistBridge.lean`'s `robust_of_distProtoRB` gives `regCtx` and the
    listed addresses' `addrUnset` only (`addrs_start`); QuePaxa's proxies and recorders listen on
    `0.0.0.0:76xx`, whose protocols need `lisUnset la` from `addrs_lis_start` (`las` = the five
    `proxyLis k` and five `recLis r`; pairwise disjoint: distinct ports; `hdisj`: the listed
    addresses must leave out `127.0.0.1:7607..7611` and `7627..7631`). Not in `Net/` (which this
    branch must not change): either Net/ gains `robust_of_distProtoLisRB` (the proof of
    `robust_of_distBootRB` with `addrs_lis_start` in place of `addrs_start`, `netProto_alloc`
    then), or the kit's `TopLevelRobustness` proves that copy itself from Net's public lemmas
    (`net_globalStart`, `goose_dist_adequacy`, `nodeWp_of_distBootG`). (b) **The ghost start**
    (the lab's `Kit/{StartGhost,Start,Shares}.lean`, ~600 lines, to re-base): allocate every
    `QNames` name (now also `γ.net` with `netTok γ k` for `k ∈ 1..5`, `γ.tick` with the clients'
    tickets `ticketsOf c`, `γ.grpc` from `GrpcHyp.world_alloc`), `consInv`/`smrInv` at their
    initial states (this branch's `Ghost.lean` definitions), `pend_alloc (qR γ) ⊤ qS0` from
    `ownState γ init` (`sysState := ownState γ`), `mapCtx_alloc (I := QIn)`, the protocols:
    `addrs_set_proto` for the listed ones (`orchAddr`, `unusedAddrs`, `clientAddr c`, `cconfAddr c`,
    `confAddr k`, remote's `reqP`/`repP` on `clientAddrs`) and `lis_set_proto` for each wildcard
    (`proxyInProto γ k`/`silentProto`; `recLisP`'s gRPC `reqProto`/`respProto` of `recAddr r`),
    giving `orchRes`, `clientRes γ c`, `serverRes γ k` (`Kit.lean`). Then (4) `Client.spec` and
    (6) `TopLevelRobustness.lean` as paxos's.
- **The kit, session of 2026-11-23 (kit fork 4: step 5, the start)**. Done, each `lean-check -a`
  clean, `lake build Dsverify.Proof.raxos.examples.quepaxanet.Start ...DistBridgeLis` OK, `#print
  axioms` of `kit_start`, `robust_of_distProtoLisRB`, `robust_of_distBootLisRB`, `consInv_init`,
  `smrInv_init`, `alloc_init`, `kitLis_disj`, `kitLis_pairwise`, `kitAddrs_nodup`, `kitAddrs_ok`:
  Lean's three; no sorry, no axiom, no new hypothesis, `Hyp.lean` unchanged; all four files are
  defs tier (no proof imported), so `etc/tier-linking.txt` is unchanged; tiers: 19 raxos non-scratch
  violations (none added):
  * `DistBridgeLis.lean` (5a): **`robust_of_distBootLisRB`/`robust_of_distProtoLisRB`**, the copies
    of `Net/Statement/DistBridge.lean`'s `robust_of_distBootRB`/`robust_of_distProtoRB` whose start
    obligation also receives `[∗list] la ∈ las, lisUnset la` (`addrs_lis_start` in place of
    `addrs_start`; premises `hlas` (no two listeners take a common address) and `hdisj` (no
    listener takes a listed address)), proved from Net's public lemmas (`goose_dist_adequacy`,
    `net_globalStart`, `addrs_lis_start`, `netProto_alloc`, `nodeWp_of_distBootG`). **Design
    finding for `Net/`**: it should offer this variant as `Net.robust_of_distProtoLisRB` (and
    `robust_of_distBootLisRB`); `robust_of_distProtoRB` is its case `las = []`. Any deployment with a
    wildcard listener (QuePaxa's replicas: `0.0.0.0:port`, D21) needs it.
  * `StartAddr.lean`: `kitAddrs` (32 listed addresses, in `netProtos`' order: `orchAddr`,
    `unusedAddrs`, `clientAddr c`, `cconfAddr c`, `confAddr k`, remote's `clientAddrs`; literal
    `kitAddrs_lit`), `kitLis` (`proxyLis 1..5`, `recLis 1..5`, `kitLis_lit`), `kitAddrs_nodup`,
    `kitAddrs_ok`, `kitLis_pairwise` (from `lis_pairwise`: wildcards of distinct ports, generic),
    `kitLis_disj` (`decide` over `lisAcceptsB`): the side conditions of `DistDeploy` and of the
    bridge. The deployment's `DistDeploy` address list must be `kitAddrs`.
  * `StartGhost.lean` (the lab's `Kit/StartGhost.lean`): `mkMap`, `bigSepM_mkMap`,
    `clientTickets_nodup`, `consRes`/`smrRes`/`ownRes` (now with `netTok γ k`, `k = 1..5`, and the
    abstract state's half for the pending library), **`alloc_init`** (every `QNames` name but
    `grpc`), **`consInv_init`**, **`smrInv_init`**.
  * `Start.lean` (the lab's `Kit/Start.lean`, 5b): `addrs_set_proto_map`, `lis_set_proto_map`,
    `recs_setup` (`recLisP` from `lis_set_proto` and the world's registry), `net_setup`
    (`netProtos γ`), `clients_dist`, `servers_dist`, and **`kit_start`**: under `[NetProtoGS]
    [QpVocab GF]` and the premise `hW` (a gRPC world's registry for any method specs, over the global
    ghost state), `regCtx -∗ ([∗list] a ∈ kitAddrs, addrUnset a) -∗ ([∗list] la ∈ kitLis, lisUnset
    la) ={⊤}=∗ ∃ γ ρ γp, orchRes γ ∗ ([∗list] a ∈ clientAddrs, remoteAddr (qR γ) a) ∗ mapCtx (I :=
    QIn) ∗ pendCtx (qR γ) qS0 γp ∗ pendLib qS0 γp qS0.M.init ∗ ([∗list] c ∈ List.range 6, clientRes
    γ c) ∗ [∗list] k ∈ [1..5], serverRes γ k`: exactly the preconditions of `Orch.spec`,
    `Client.spec` and `Server.spec` but `isPkgInit` (the world's registry via the lab's trick:
    `world_alloc (consensusMS γ0)`, then `γ := {γ0 with grpc := g}`, the resources equal by `rfl`).
  * **Design finding for `Hyp.lean`** (to do with the top level): `GrpcHyp.world_alloc` is a field
    of a class over a `HeapGS`, but the start obligation (`robust_of_distProtoLisRB`'s `Hstart`) has
    only the global ghost state `[GooseGlobalGS .hasLC GF]`: move `world_alloc` into its own class
    over `GooseGlobalGS` (e.g. `hyp.GrpcWorldHyp qv.grpc`) and pass it as `kit_start`'s `hW`. (Not
    done here: `Hyp.lean` is imported by the whole protocol proof, a rebuild of everything.)
  * **Next, precisely**: (4) `Client.spec` (unchanged plan above); (6) the top level, as paxos's:
    `TopLevelDefs.lean` (`quepaxaKitAddrs := kitAddrs`, `system σ`: orch, client0..5, server1..5 with
    their `PkgTable`s), the statement `quepaxa_remote_robust.spec` in
    `Dsverify/Spec/raxos/examples/quepaxanet/TopLevelRobustness.lean` (premises: every `InitHyp`,
    `PbHyp`, `RandHyp`, `SortHyp`, `UtcHyp`, `PrintlnHyp`, `GrpcHyp`, `MapHyp`, the world class
    above, the `Assumptions`), the commands' `wp_main`s (`Mains.lean`: `cmd.*.main` calls
    `Orch`/`Client(c)`/`Server(k)`), and `TopLevelRobustness.lean`: `robust_of_distProtoLisRB
    kitAddrs kitLis (system σ) g threads (2^63) kitLis_pairwise kitLis_disj`, then `kit_start` and,
    per machine, paxos's `wp_boot` with `wp_Orch` (orchRes, remoteAddr list, mapCtx, pendCtx,
    pendLib), `wp_Client` (clientRes γ c, `remoteAddr (clientAddrs.getD c [])` from the list,
    mapCtx) and `wp_Server` (serverRes γ k). (`Client.spec`'s proof: done, kit fork 5 below.)
- **The kit, session of 2026-11-23 (kit fork 5: step 4, `Client.spec`)**. Done, each `lean-check -a`
  clean, `lake build Dsverify.Proof.raxos.examples.quepaxanet.Linked` OK (2781 jobs), `#print axioms`
  of `wp_Codec`, `wp_Gens`, `wp_Orch`, `wp_Server`, **`wp_Client`**: Lean's three; no sorry, no axiom,
  no new hypothesis (`Hyp.lean` unchanged), no Go change; tiers: 19 raxos non-scratch violations
  (none added). New files (all defs tier but `KitClient`, proof tier):
  * `KitWire.lean`: **`cbMarshal.spec`** (`ClientBatch.Marshal` into a `*bufio.Writer`: the writer's
    protocol `Q` is asked of the stream after the 8-byte length prefix too, `□ (⌜batchFit b⌝ → Q (…
    ++ le8 len) ∗ Q (… ++ le8 len ++ enc))`; on `nil` the batch fits and its frame body was appended)
    and **`cbMarshal_proof`** over `PbHyp.marshal` and bufio's `Writer.Write` (two writes).
    `Unmarshal` is `Proxy/NetUnmarshal`'s `unmarshalB.spec`/`unmarshal_bounded` (stream fact `Φ`).
    **To do when `Wire.lean` is next edited** (it rebuilds the protocol proof): delete its
    `ClientBatch.Marshal.spec`/`ClientBatch.Unmarshal.spec` (unused, superseded by these two).
  * `KitConn.lean`: `connInv` (dialer end of a connection to `proxyAddr k`, `net.connAt` + `connIs`,
    a bufio writer under `proxyInProto γ k`, stream `hs (21+c) ++ frs L`, `framesOk`: each frame's
    `batchReg` and ticket `tixAt (k, c, j) cn n`), `repInv`, `isReplica`, `replica_init`,
    `proxyAddr_ok` (`lisProto_addr` from the proxies' wildcard `lisProto`), `wp_drop`, `wp_connect`
    (Dial with `dial_au`, the handshake `Write`, `NewWriter`), `wp_tryConnect`, `wp_reset`,
    **`wp_send`** (the ticket registered before the code byte, `frameBatch` for a batch the codec
    rejects, WriteByte/`cbMarshal_proof`/Flush, drop on any error).
  * `KitSys.lean`: **the lock invariant `sysInv γ c s`** of `s.mu`: the `waiting` map (futures with
    `ansContract`: an answer batch, fit, one result with `opAns`), `s.next = n ≤ 20`, `cntHalf γ c n`
    (client `c`'s whole half of the registry counter: no quarters, the lab's `nextInv` is gone) and
    `ticketsFrom γ c n` (requests `n..19` at replicas `1..5`; `ticketsOf_perm` reorders
    `clientRes`'s tickets); `isSysL γ c s` (persistent); `wp_deliver`.
  * `KitRecv.lean`: the client port's stream (`cl_hs`, `cl_len`, `cl_frame` over `NetFrames`'
    parsing), **`wp_receive`** (bufio reader, `io.ReadFull` of the handshake, `ReadByte`/
    `unmarshal_bounded` loop, `deliver`, close, `reset` of the replica named), `wp_accept`.
  * `KitOpLib.lean`: `resultOf_ansOf`, **`qOutOk_of_ans`** (a fit answer's output is encodable:
    `|v| + 9 ≤ |r| ≤ |encBatch b| < 2^63`), `cmd_len_le`, `wp_command`, `wp_result`.
  * `KitOp.lean`: `regPost` (remote's `Φ` of the clamped output and "the output is a step's"),
    `slotUpd_opUpd` (remote's `slotUpd (qR γ)` is `opUpd`: `lin_opAU`), **`wp_Op`**: `s.next` read
    and, if `< 20`, the request registered (`op_register`) and its five tickets taken in one critical
    section; else the unknown output, nothing sent; stagger sleep; the future; the batch literal;
    `wp_send` to every replica; `select` on the future (`op_collect`, `wp_result`, `clampO_of`) or
    `time.After` (delete, unknown).
  * `KitNewClient.lean`: **`wp_newClient`** (awaitConf forked, the configuration from the bag,
    the `Sys` literal, the replicas appended with `replica_init`, `sysInv` from `clientRes`, Listen
    retry at `clientAddr c`, `accept` forked, `tryConnect` loops).
  * `KitClient.lean` (proof): **`Client.wp_proof`** (premises: remote's `ServeClient.spec` at
    `QIn`/`QOut`, `Codec.spec`, `net.Listen/Accept/Read/Write/Close/Dial`, `ioLt.ReadFull`,
    `bufio.NewReader.specOk`, `time.After.spec`): `tok sys := ⌜sys = *Sys s⌝` (the closures reload
    `s` from a variable, persisted), `opMaybe_svcOp`.
  * Moved (no change): `wp_Addrs` from `KitServer` to `KitConf`; `wp_registerProto`,
    `wp_make_bag1` from `KitServer` to `KitAwait` (the client needs them; proofs see only defs).
  * `Linked.lean`: **`wp_Client`** (remote's `wp_ServeClient`, `wp_Codec`, `net`'s, `IoReadFull`'s,
    bufio's `NewReader`, Perennial's `time.After.wp_proof`).
  * **Design findings (remote)**: none requiring a change. Remote's `op` is persistent and may
    overlap (retried reads): handled by the lock invariant holding `s.next` with the counter's half
    (each call takes its own sequence number; a call past the 20-request budget registers nothing).
    `ServeClient`'s `tok sys` is returned by every `op`: a pure `tok` (the client's `*Sys` value)
    suffices, its facts persistent (`isSysL`). The 20-request budget is the Go guard (fork 2).
  * **Next, precisely**: (6) the top level as paxos's (unchanged plan in kit fork 4's "Next"):
    `TopLevelDefs.lean`, the statement `quepaxa_remote_robust.spec`, `Mains.lean`, and
    `TopLevelRobustness.lean` composing `kit_start` with `wp_Orch`, `wp_Client`, `wp_Server` (the
    client's premises now include remote's/lintest's/perclient's `Assumptions`, `time.Assumptions`,
    `errors.Assumptions`); with it, `Hyp.lean`'s `GrpcHyp.world_alloc` into its own class over
    `GooseGlobalGS` (kit fork 4's finding), and the deletion of `Wire.lean`'s two stale specs (both
    edits rebuild the protocol proof: batch them).
- **Hypothesis audit (2026-11-23, after the kit's codec session)**: the reviewer's rule (a
  hypothesis no stronger than the real Go library: real preconditions, no spec where Go panics or
  races; nothing Perennial gives a body for) applied to `Hyp.lean`; the changes are in
  "Hypotheses" above: `GrpcHyp` (`Invoke`'s empty `opts` and trailer-error branch, `NewServer`'s
  empty options, `descOk`'s `HandlerType`/`Metadata` and the implements check with `srcState`'s
  `HandlerType`, `Dial`'s options and `dialTarget`), `RandHyp` (only `Seed`, `Intn`), `PbHyp`
  (no unknown fields in the `rep*`; `decInto` gives the `rep` only for a well-formed encoding),
  `strconv.Atoi` proved (`AtoiSpec.lean`/`AtoiProof.lean`; `AtoiHyp` gone; the earlier entries'
  `[AtoiHyp]` binders are now `[hyp.AtoiSpec GF]` in the proof files and nothing in the
  `Results`), `printOk` excludes `fmt.Formatter` (`[fmt.Assumptions]` now a premise of the
  `NetworkInit` results), `SortHyp`'s `isPkgInit pkg_id.sort`, `UtcHyp`'s doc, `MapHyp.ivt`'s note.
  `lake build` of `Replica.Results`, `Proxy.Results`, `Proposer.Results`,
  `examples.quepaxanet.KitCodecFn`: OK; `#print axioms` of `Replica/Results`' four
  theorems: Lean's three. Tiers: 19 raxos non-scratch violations, as before.
- **Next, in order** (ported ~20k of 37k lab lines; Replica and Proxy done but `WireProof`):
  2. `Codec/*` (7.3k: only the pure
     parts port; the generated-codec proofs are replaced by the protobuf hypotheses, so
     `Codec/Switch`, `Enc*`, `Dec*` mostly go; `Wire.lean`'s `ClientBatch.Marshal/Unmarshal` are
     proved from `PbHyp` and dsv-bufio), `Kit/*` (5.8k, onto remote: `Kit.lean` with `qR`,
     `lin_opAU`, `Codec.spec`, `Gen.spec`, `Orch.spec`, `Client.spec`, `Server.spec` as paxos's
     `Kit.lean`; `Orch.wp_proof` takes `Model.wp_proof`).
  3. `quepaxa_remote_robust` (`TopLevelRobustness.lean`): premises every `InitHyp`, `PbHyp`,
     `RandHyp`, `SortHyp`, `UtcHyp`, `PrintlnHyp`, `GrpcHyp qv.grpc` and `MapHyp qv.map` (over the `QpVocab` instance; `strconv.Atoi` is proved, `AtoiProof.lean`),
     `net.Assumptions`/`net.FieldAssumptions`/`go.BasicIntoValInj` as paxos's, all visible in
     the `.spec`; check `etc/theorem-loc.py` counts them. `etc/tcb-collections/dsv-quepaxa.txt`
     (the two trusted descriptor-table inits of `TrustedCode/raxos/{replica/src,proto/client}.lean`,
     the etcd #32 justification).
- Porting recipe (now mostly in `etc/dsv/tools/quepaxa-port.py`): run it, then by hand: `#Hcs,
  #Hko` and the two codec conjuncts out of patterns/preconditions; `proposerP`'s destruct
  patterns lose two `-`; library specs: the lab's `*.wp_proof` of its harness become the
  hypotheses' fields (`gh.Invoke`, `hyp.RandHyp.Intn (GF := GF)`, `hMV.Load`), Perennial's
  results where they exist (`Perennial.Proof.sync.Results` for the WaitGroup join idiom).

- Environment: `lake` is `~/.elan/bin/lake` (put `~/.elan/bin` on `PATH` for `etc/lean-check.py`).

- **Linking check (the coordinator's VR finding 7, 2026-11-23)**: the only package fact under
  `Dsverify/` that is not `True` is `raxos/replica/src`'s `srcState`, established by that package's
  own variable initializer (`Consensus_ServiceDesc`), not by a hook another package's `init` sets;
  `raxos/replica/src` is in every node's `PkgTable` and `go list -deps` links it into every command
  (orch, client0..5, server1..5). No fact relies on a package the program does not link. (The lab's
  `registerProto` codec hook is gone: protobuf is the hypothesis `PbHyp`, not a package fact.)
- **Merge of lean `d1c432a3ca` (2026-11-23)**: dsv-epaxos, the namespace hard-check, Perennial pin
  `70706ce5e` (worktree `/shared/perennial-70706ce5e`, `.lake/package-overrides.json` repointed).
  `gen-init` (twice) changed nothing; `etc/goose.py`, `etc/gen-init.py` equal lean's. Finding 4
  closed (above). Checks: `proof_roots.namespace()` = `Perennial.EtcdGrove.`; `gen-init --check`,
  `goose --check` (all projects), `copy-part --check`, `tier-check --check` (227 known, baseline
  equal to lean's, none quepaxa's) pass; `errorf-wrap` `init_errors() == []`. Duplicates: the
  coordinator's `dups.py` over the Dsverify roots (2706 modules) finds 4 names, all false positives
  (comment lines starting `instance`/`structure`/`lemma`, and Perennial's `go.inductive`), none
  QuePaxa's; a scratch file importing rabia's, epaxos's and QuePaxa's `TopLevelRobustness` together
  checks with `lake env lean` without "environment already contains". `lake build` of QuePaxa's
  `TopLevelRobustness` (statement and proof) green; `#print axioms quepaxa_remote_robust`:
  `propext`, `Classical.choice`, `Quot.sound`.

## dsv-fix3: initializer premises become axioms (2026-11-25, #49)

The names-only initializers' `InitHyp` premises became per-package trust-boundary axioms
(`axiom wp_initialize'` in `Dsverify/Proof/<pkg>/Init.lean`, the class's statement exactly; Upamanyu,
#8 2026-11-25T02:20:53Z; `etc/dsv/README.md`, "`HYP_INITS`: per-package `wp_initialize'` axioms"),
each reviewed by the `axiom` skill (`notes/axiom-review/dsv-inits/`) and counted in the kit's
collection. Two reviews refuted theirs in Go, go-redis v8's (`GODEBUG=fips140=bogus` panics in
`crypto/internal/fips140`'s `init`, through `crypto/tls`) and grpc's (a program registering grpc's
`binarylog.proto` first panics in grpc's initializer): those two stay `InitHyp` premises (gen-init's
`DSV_PREMISE_INITS`) until Upamanyu picks a fix. The nine axiomatized packages' test-only
`InitInstancesLinked.lean` (imported by nothing; their local `localInitFuncsOk`, true of no
particular semantics, looked false where an `init` panics) are deleted with their `InitHyp` classes.

Here: `gopkg_in.yaml_v2`, `io.ioutil`, `encoding.gob`, `google_golang_org.grpc.codes` are axioms;
`quepaxa_remote_robust` loses those four `InitHyp` premises and keeps go-redis's and grpc's
(statement diff: removals only); `NonVacuityLinked.lean` instantiates the two kept ones.
