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
  `models/protobuf/pbgen.py` and protobuf's model.
- **gRPC, unary**: the vocabulary `hyp.grpc.GrpcVocab GF` (abstract data: `reqProto`/`respProto`
  (`Net/` `Proto`s of a gRPC address), `worldOk`, `isServer`, `srvOwn`, `srvServed`,
  `isClientConn`, `handlerErr`, with their persistence as fields), `UnarySpec`, `GrpcWorld`
  (`MS`, `reg`), and defined over it as the lab's: `grpcAddr V W a := addrProto a (reqProto W a)
  (respProto W a) ∗ worldOk W`, `replyOk`, `decOk`, `handlerOk`, `descOk`, `encPre`. The specs
  (the lab's statements): `NewServer.spec`, `Server.RegisterService.spec`, `Server.Serve.spec` (the
  listener as `net.Listen`'s success post gives it: `isListener li l ∗ netLis l a true ∗ netLisAt
  l a`), `WithInsecure.spec`, `Dial.spec`, `ClientConn.Invoke.spec`, and the law `world_alloc`;
  bundled as `class hyp.grpc.GrpcHyp V` (over `[PbCodec GF]`, to be `qpCodec`). **The deployment's
  vocabulary is an instance `[qv : hyp.QpVocab GF]`** (data only, field `grpc`): the definitions
  (`netProtos`, `peersP`, `replicaRes`, the proxy's state) mention `qv.grpc`; theorems that call
  gRPC take `[GrpcHyp qv.grpc]`. The statement will quantify over the instance and the hypothesis.
- **`sync.Map`**: vocabulary `hyp.sync.MapVocab GF` (`own m M`, string keys), `class
  hyp.sync.MapHyp V` (`own_timeless`, `own_zero` from a zero map, logically atomic
  `Map.Load.spec`, `Map.Store.spec`, `Map.Delete.spec`). The proxy's store packs its vocabulary
  and hypothesis in `isStoreDef` (`∃ MV, ⌜MapHyp MV⌝ ∗ ...`, `Proxy/StoreDefs.lean`): whoever
  allocates a store (`raxos.New`'s proof) needs one from the statement. (`ClientBatchStore.Range`,
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
- `log` (`Println`, `Fatal`), `math/rand` (`Intn`, `Seed`, `NewSource`/`New`/`(*Rand).Intn`), `os`
  (`Create`, `Exit`, `Stderr`), `fmt.Fprintf`, `strconv.Atoi`, `sort.Ints`, `time` extras (the lab's
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
- **PkgState (not done)**: the lab's `srcState` (the `Consensus_ServiceDesc` points-to, for the
  recorder's `RegisterService`) is not the package fact yet: `replica/src`'s fact is `True`
  (`Base.lean`). Making it `srcState` needs `etc/dsv/quepaxa.py`'s `special(g)` entry for
  `raxos.replica.src` to finish the generated `Init.lean` with the descriptor's facts (its
  `before` hook already evaluates the literal), and `Base.lean`'s `define_is_pkg_init` to name
  it. Needed only once the grpc hypotheses (`grpc.Server.RegisterService.spec`) are stated.
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
- **Design points found (to settle in the proofs that meet them)**:
  1. **Wildcard listeners.** The replicas listen on `0.0.0.0:port` (proxy, recorder), the
     protocols are set at `127.0.0.1:port` (what the dialers dial). The proofs of `NetAccept`
     (proxy) and of the recorder's `Serve` hypothesis must relate `net.Listen("0.0.0.0:p")`'s
     `netLis l a` and `Accept`'s `netConnAt cn a` to the dialed address (D21: a wildcard listener
     takes any address with its port). Check what `Net/`'s `listen_au`/`accept_au` give for a
     wildcard address before porting `Proxy/Net*`; the `Serve` hypothesis may need the listen
     address and the protocol address separately.
  2. **`addrTok` is persistent** in `Net/` (exclusive in the lab): `sharedNet`'s invariant
     `netOwn pr rm ∨ addrTok (proxyAddr k)` (the accept routine's state, given once) still
     gives `netOwn` to one caller, but its swap no longer proves a second caller cannot
     exist; `Proxy/NetAccept`'s proof must not need that.
  3. **PkgState**: `Server.RegisterService.spec`'s `descOk` needs the `Consensus_ServiceDesc`
     points-to, the lab's `srcState` (`PkgState.lean`), as `raxos/replica/src`'s package fact
     (now `True`, `Base.lean`): `etc/dsv/quepaxa.py`'s `special(g)` entry for `raxos.replica.src`
     must end the generated `Init.lean` with the descriptor's facts, and `Base.lean`'s
     `define_is_pkg_init` name it. Do this when porting `Replica/Init`/`Inits`/`HarnessInit`.
- Done (third part of this session): `Proposer/*` (all; `Results`' `NewProposer.wp_proof`,
  `Proposer.runProposer.wp_proof` take `[GrpcHyp (cd := hyp.qpCodec) qv.grpc] [hyp.RandHyp GF]`;
  `#print axioms`: Lean's three); math/rand's hypotheses (`hyp.RandHyp`, `Hyp.lean`); `Proxy/Store`
  (`store_add_proof`, `store_get_proof` over `MapHyp`; `isStore_alloc_proof` from `MapVocab.zero`);
  `Replica/{RecDefs,ReqPersist,Helpers,EspImpl,HandleESP,Handlers,Fetch}` (`esp_handlerOk`,
  `fetch_handlerOk`, `inform_handlerOk`: the recorder's three methods meet `handlerOk qv.grpc`).
  `lake build` of `Replica.Fetch`, `Replica.Handlers`, `Proxy.Store`, `Proposer.Results`, `Smr.Laws`,
  `Proxy.Slots`, `ModelProof`: OK. `RecDefs` no longer imports `Proxy.Results`/`Proposer.Results`
  (it used neither).
- **Open: `sync.Map`'s points-to is `sorry` in Perennial** (`Perennial/GeneratedProof/internal/sync.lean`:
  `HashTrieMap_typed_pointsto`/`_into_val_typed` are `sorry -- axiomatized type`, and `sync.Map` has
  a `HashTrieMap` field). `#print axioms`: `store_add_proof`, `esp_handlerOk`, `fetch_handlerOk`
  depend on `sorryAx` (through `ClientBatchStore`'s generated points-to/`IntoValTyped`, which `wp_auto`
  uses on the store's field); `store_get` path and `inform_handlerOk`, `isStore_alloc_proof`, the
  hypotheses (`MapHyp` uses an abstract `MapVocab.zero`, not the points-to) are clean. This is the
  lab's `StoreInst.lean` issue (it gave `ClientBatchStore` a high-priority points-to over its own
  `sync.Map` model). Fix options: (a) high-priority `TypedPointsto`/`IntoValTyped` instances of
  `ClientBatchStore` (and whatever `wp_auto` needs of `sync.Map`) built from data in `MapVocab`
  (a `sync.Map` points-to as part of the hypothesis vocabulary, with `zero` its zero value's), or
  (b) Perennial translating `internal/sync.HashTrieMap` (a Perennial change, `notes/perennial-changes.md`).
  Find first which instance `wp_auto` pulls in (`set_option trace.Meta.synthInstance`, or `#print
  axioms` of the instances in `Dsverify/GeneratedProof/raxos/replica/src/chunk1.lean`).
- **Next, in order** (ported ~13k of 37k lab lines):
  1. `Replica/{Serve,Server,Init,Inits,HarnessInit,Results}`: `Serve` is the recorder's loop
     (`grpc.NewServer`, `RegisterConsensusServer` → `RegisterService` with `descOk` from
     `esp/fetch/inform_handlerOk` and the package fact `srcState` (PkgState, design point 3),
     `net.Listen` on `0.0.0.0:port` (design point 1), `Serve`); `HarnessInit` is the lab's
     harness initialization: drop or replace by the `InitHyp`s.
  2. `Proxy/*` rest (11k: `Net*` onto `Net/Spec/net/*` + `GooseLang/Ext/Net/Proto.lean`'s laws as
     paxos's `NetProof.lean`; the writers through dsv-bufio's specs), `Codec/*` (7.3k: only the pure
     parts port; the generated-codec proofs are replaced by the protobuf hypotheses, so
     `Codec/Switch`, `Enc*`, `Dec*` mostly go; `Wire.lean`'s `ClientBatch.Marshal/Unmarshal` are
     proved from `PbHyp` and dsv-bufio), `Kit/*` (5.8k, onto remote: `Kit.lean` with `qR`,
     `lin_opAU`, `Codec.spec`, `Gen.spec`, `Orch.spec`, `Client.spec`, `Server.spec` as paxos's
     `Kit.lean`; `Orch.wp_proof` takes `Model.wp_proof`).
  3. `quepaxa_remote_robust` (`TopLevelRobustness.lean`): premises every `InitHyp`, `PbHyp`,
     `RandHyp`, `∃ V, GrpcHyp V` (as the `QpVocab` instance), `∃ MV, MapHyp MV`, all visible in
     the `.spec`; check `etc/theorem-loc.py` counts them. `etc/tcb-collections/dsv-quepaxa.txt`
     (the two trusted descriptor-table inits of `TrustedCode/raxos/{replica/src,proto/client}.lean`,
     the etcd #32 justification).
- Porting recipe (now mostly in `etc/dsv/tools/quepaxa-port.py`): run it, then by hand: `#Hcs,
  #Hko` and the two codec conjuncts out of patterns/preconditions; `proposerP`'s destruct
  patterns lose two `-`; library specs: the lab's `*.wp_proof` of its harness become the
  hypotheses' fields (`gh.Invoke`, `hyp.RandHyp.Intn (GF := GF)`, `hMV.Load`), Perennial's
  results where they exist (`Perennial.Proof.sync.Results` for the WaitGroup join idiom).

- Environment: `lake` is `~/.elan/bin/lake` (put `~/.elan/bin` on `PATH` for `etc/lean-check.py`).

## Which lab run

`quepaxa-bump-1` (dsverify-lab `master` `915f964`, `examples/quepaxa/SOURCE.md`): proof `4ae902e`
(tag `final`), fork `77b5258`, harness `cd3a97b` (lab commit `71cae38`), Perennial `3afd77e35`;
verified there in 671 s (`verify-final.log`).
