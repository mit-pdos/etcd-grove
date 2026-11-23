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
| trusted code | only `Dsverify/TrustedCode/{raxos/replica/src,raxos/proto/client}.lean` (the lab's no-op `init`s of protoc-gen-go's descriptor tables in QuePaxa's own packages; empty `ManualProof/` beside them). They stay trusted code, not `InitHyp`s: those packages' other initializers (`Consensus_ServiceDesc`) are translated and proved, and a hypothesis would cover the whole package's `initialize'`; untranslated instead, they would be `opaque` initializers and gen-init's `opaqueInitsOk` axiom. (The names-only libraries' no-op models of 0e2763910c are gone: `InitHyp`s, below.) |
| initialization hypotheses | `Dsverify/Proof/{gopkg_in/yaml_v2,github_com/go_redis/redis/v8,io/ioutil,encoding/gob,google_golang_org/grpc,google_golang_org/grpc/codes,math/rand}/Init.lean`, hand-written (dsv-vr's pattern): `class InitHyp GF : Prop` holding the package's `wp_initialize'`; gen-init's `DSV_HYP_INITS` / `dsv_hyp_fix` (vr's code) treat them as external and add `variable [<pkg>.InitHyp GF]` to every generated init file above them |
| package facts and initialization | `Dsverify/Proof/<pkg>/Base.lean` (`True` for every QuePaxa package and names-only library; each imports its imports' fact modules), `Dsverify/Proof/google_golang_org/protobuf/Base.lean` (protobuf's five packages' facts: the main tree's live in `cache/v3/Base`, `raft/v3/Base`, which import the main tree's `net`); `etc/gen-init.py` `dsv_inits` (additive: `DSV_QP*`, `DSV_MAIN` = bufio, math/rand, protobuf's `Init` made in the part as `NET_MAIN`'s in `Net/`, `DSV_OWN` = the part's grpc without the main tree's `SPECIAL`, `SPECIAL['raxos.replica.src']` for `Consensus_ServiceDesc`); generated `Init.lean` and the twelve commands' `PkgTable.lean` all build |
| the protocol's proof | `Dsverify/Proof/raxos/` (the lab's `Quepaxa/Proof/` layout), all building: `Pure/Conf.lean`, `Pure/Consensus.lean` (verbatim), `Pure/Smr.lean` (edited: the kit's `KIn`/`KOut`, linkv's `kvB`, `execCmd_step`; the lab's `Harness.Models` `kvAbs` moved here, recursive, `kvAbs_put` by `rfl`), `Pure/ModelSet.lean` (new: `mSet`, `step_mSet`, `mSet_empty`, `stepE_ok`); `Msg.lean` (the lab's; its `pbCodec` instance dropped: `marshalPre`/`unmarshalPre` are the shapes the protobuf hypotheses will take), `Ghost.lean` (edited, below), `Cons/{Lemmas,Laws}.lean` (the lab's; connections numbered by the net extension), `Smr/{OpId,SumId,Exec}.lean` (Exec edited: `kvAbs_mem`, `cmdPut_cmdOf`/`goodVal_of_put` over `KIn`) |
| the kit's model | `.../raxos/examples/quepaxanet/Model.lean` (the spec `qS`: the Go state as a list `E` of keys and `Ent`s, `qRep`, `qDec`/`qDec_box`, `stepL`/`stepL_pSeq`, bounds; `Model.spec`) and `ModelProof.lean` (`Model.wp_proof`: `Model()` meets `isModel qS`; helpers `push`/`has`/`erase` (paxos's proofs), `cat`, `lookup`, `set`, `stepE`, `step`, `equalS`/`equalE`/`equal`) |
| hypotheses | `Dsverify/Proof/raxos/Hyp.lean` (protobuf `PbHyp`, math/rand `RandHyp`, gRPC `GrpcVocab`/`GrpcHyp` and the instance class `QpVocab`, `sync.Map` `MapVocab`/`MapHyp`; below) |
| trust base | `etc/tcb-collections/dsv-quepaxa.txt` (to come with the statement) |

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
  (respProto W a) ∗ worldOk W`, `replyOk`, `decOk`, `handlerOk`, `descOk`, `encPre`. The specs
  (the lab's statements): `NewServer.spec`, `Server.RegisterService.spec`, `Server.Serve.spec`
  (**changed for the wildcard**: the listener at `la` as `net.Listen`'s success post gives it,
  `isListener li l ∗ netLis l la true ∗ netLisOn l la`, with `lisProto la (reqProto W a)
  (respProto W a) ∗ worldOk W` for the server's address `a`, in place of the lab's listener at
  `a` and `grpcAddr W a`), `WithInsecure.spec` and `Dial.spec` (**as the lab's `dialPost`**: the
  vocabulary's `credsOpt o` (the lab's `DialOption.creds = true`) for `WithInsecure()`'s option;
  `Dial` fails only if no option sets credentials, so QuePaxa's error branch, `fmt.Fprintf` +
  `os.Exit`, is unreachable and needs no spec), `ClientConn.Invoke.spec`, and the law `world_alloc`;
  bundled as `class hyp.grpc.GrpcHyp V` (over `[PbCodec GF]`, to be `qpCodec`). **Audit fixes
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

## State

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

## Which lab run

`quepaxa-bump-1` (dsverify-lab `master` `915f964`, `examples/quepaxa/SOURCE.md`): proof `4ae902e`
(tag `final`), fork `77b5258`, harness `cd3a97b` (lab commit `71cae38`), Perennial `3afd77e35`;
verified there in 671 s (`verify-final.log`).
