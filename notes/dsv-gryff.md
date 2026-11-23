# dsv-gryff: dsverify-lab's gryff kit on the net extension (phase 6)

Branch `dsv-gryff` (2026-11-23), off `origin/dsv-paxos` (paxos not landed on `lean` yet; merge
`origin/lean` once it is). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/gryff/` (run
**`gryff-bump-1`**, the final verified run: clients on nodes of their own, Perennial `3afd77e35`;
proof `21ef7d6` tag `final`, fork `ef17c2d`; read only, nothing in the lab changed).

**State (2026-11-23, second resumed session; branch merged with `dsv-infra` `884cb306c9`,
`models-rpc-server` `040ef5e808`, the revised `dsv-bufio` `75ef5881aa` and `lean` `1b2fd95b30`
(Perennial `7b2259a12`; `net-wildcard-listen` landed there)):** Go and translation done (`etc/goose.py --check --project
dsv-gryff` clean). **Ported by editing and building** (`lake build` of every module under
`Dsverify/Proof/gryff/`, 186 files, green): the library-free layers (`Model/`, `Kahn/`, the tag
order, `Pure*`, `Proto/`, `Proto2/`, `Proto2P/`, `B.Pure`, `Wire.Enc`/`Varint`), and the first
`Net/`-facing layer, **the wire protocols** (`N/Wire{Defs,Inj,Laws}`, `Proto2/Wire`,
`Proto/Wire{Defs,,Laws}`, `WS/Ports`: `gryffWireP`/`gryffWireQ` over `Net/`'s `Proto`,
`sentLb`, `connFresh`; see "What changed against the lab (proof)"). **The kit's porcupine model,
pure** (`examples/gryffnet/ModelSet.lean`: `stepG_pSeq`, `cfgSet_init`). Of the lab's 369
`GryffProof` modules, 186 remain (below, "Next"). Not done: the library-facing layers above the
wire (N, B, Rpc, Server, Client, H1-H3, X, Replica2, Start, Shares, Top), the kit's Go-level model
proof, the package initializers, the client on remote, Mains, Linked, `gryff_remote_robust`, the
TCB collection. No `sorry`, no axiom under `Dsverify/`.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/gryff/` (module `gryff`, the fork's path): the fork's packages the kit reaches (`src/{fastrpc,dlog,state,stats,clientproto,genericsmrproto,masterproto,epaxosproto,gryffproto,bitvec,bloomfilter,genericsmr,gryffcommon,gryff,masterlib,serverlib}`, non-test files only, unchanged, the fork's ghost prophecy code included) and the kit `examples/gryffnet` with its eleven commands `cmd/{orch,client0..5,server1..4}` |
| net/rpc codec | `examples/gryffnet/rpc.toml` -> `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` by `models/net/rpc/rpcgen.py` (`--check` clean since lean `660918251a`, the receivers' import fix) |
| translation | `etc/goose.py` project `dsv-gryff` (its entry in `etc/dsv/gryff.py`, dsv-infra's per-kit file) into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/gryff/`), std_models `net/rpc`, `net/http` (as project `models-net`); remote, `net` and the models `Net/`'s, lintest, porcupine, `bufio`, `os` the main tree's, the rest Perennial's. `Dsverify/Code/gryff/src/stats.toml`: `StatsMap.Export` names only (JSON to a file; never called: no statistics file) |
| the protocol's proof | `Dsverify/Proof/gryff/` (modules `Dsverify.Proof.gryff.*`, namespaces the lab's): ported by `port.py`'s mechanical renames then edited; the lab's `Harness` vocabulary the proof keeps, its pure parts only, under `Lab/` (`Model`, `ModelsCas`'s `casRegister`, `ClientSpec`'s `clientN`/`opAwp`/`opAwpMaybe`); `Slots.lean` holds the packages' states (the lab's generated `GryffNetPkgState`) |
| the statement | not written yet (`gryff_remote_robust.spec`, `DistDeploy … → Robust [] …`, as `paxos_remote_robust`) |
| the kit's model | `Dsverify/Proof/gryff/examples/gryffnet/ModelSet.lean` (pure, done): `casB` (linkv's `PendSpec` of the register with CAS: `applyG`, `isWriteG`), `cfgSet` (a list of `Cfg`s stands for the configurations reachable from them), `AReach` (kit.go's `reach`: pending operations applied by index, `without`), `knownCfgs` (what `step`'s second loop collects), `stepG_pSeq`, `cfgSet_init`. The Go proofs (`ModelProof.lean`: `apply`, `isWrite`, `without`, `with`, `sameCfg`, `hasCfg`, `reach`, `step`, `equal`, `Model`) are not written: they need the kit package's `Init` (below) |
| trust base | `etc/tcb-collections/dsv-gryff.txt` not written yet (no roots) |

## What changed against the lab (Go)

- **The deployment is remote's.** The lab ran `remote.RunRemote` (its own driver, recorder, the
  `check.CasRegister` checker under its porcupine axiom) with its client shim. Here the orchestrator
  runs `remote.Check` against the **int64 register with compare-and-swap and pending operations**
  (`kit.go`'s `Model`, a porcupine model): the state is a list of configurations `Cfg{V, Pend}` and
  stands for those reachable by pending operations taking effect (`reach`); an unknown write or CAS
  is appended to every configuration's `Pend`, an unknown read does nothing, an answered operation
  keeps the configurations reachable from the state's whose output is the answer. It is meant to be
  linkv's pending construction (`Proof/.../txnlin/PendModel.lean`, `PendSpec` with `isWrite` = Write
  or CAS) as paxos's `ModelSet.lean` is for the write-once register; its proof is to write. Inputs
  `In{Op, A, B}`, outputs `Out{Unknown, V}` (a Write's and a CAS's output is `Out{}`: Gryff's
  RMWReply does not say whether it swapped, as the lab's `CasRegDone`). The codec: 17 bytes in, 9
  out (injective, as remote's `Check.spec` needs).
- remote's `gen` takes only the client: `gens` numbers each client's calls under a mutex and returns
  the lab's `Gen(c, j)` (write own value, read, CAS expecting it, read).
- The client's start (`Start(c)`, the lab's `StartMs + (c/2)·StaggerMs`) is waited for at the
  client's first operation (`Sys.started`). Client machine `c`'s `Sys` is made once, before
  `remote.ServeClient` (paxos's finding: a second `Sys` would reuse Gryff client ids).
- Machines: orchestrator, six client machines (`127.0.0.1:7511..7516`), the master
  (`127.0.0.1:7501`) and three replicas (`7502..7504`, net/rpc at `+1000`); the lab's
  `10.77.0.x` rig addresses and the per-client checks (`checks`) are gone. Every port is distinct
  (the master's and replicas' wildcard `Listen(":p")`: plan phase 2 item 4 holds).
- `kit_test.go`: the deployment as processes (net/rpc's `DefaultServer` and http's
  `DefaultServeMux` are per process: three replicas in one process would register `Replica` twice),
  the model on small histories (pending writes and CASes taking effect late, once), Gen, Op with no
  server, the codec. Passes with the real net/rpc (`go test ./examples/gryffnet/`) and with the
  models (`GOROOT=$(models/goroot.py farm DIR) GOTOOLCHAIN=local go test -tags netmodel ...`).

## Hypotheses (missing model pieces; the coordinator's rule of 2026-11-23)

No library models of this branch's own; the unlanded shared branches `models-rpc-server` and
`dsv-bufio` (revised) are merged (coordinator's instructions) and used directly. A spec the proof
needs from a piece still missing (rpc over HTTP, net/http's server) is a hypothesis, named after the lab's spec, that the kit's
theorems take as an instance (a `Prop` class), up to `gryff_remote_robust`.

**Stated in Lean so far** (dsv-vr's pattern for names-only package inits,
`Dsverify/Proof/encoding/json/Init.lean` on `dsv-vr`):
- `net.rpc.InitHyp GF`, `net.http.InitHyp GF`, `math.rand.InitHyp GF`
  (`Dsverify/Proof/{net/rpc,net/http,math/rand}/Init.lean`): the packages' `wp_initialize'`. Their
  facts (`Base.lean`) are `True`; net/rpc's and net/http's are names only (dependency part `True`,
  `GetIsPkgInitWf` constraining the package itself), since their import closures (`go/token`,
  `net/url`, `crypto/tls`, `net/textproto`, `httpguts`, ...) have no instances in `Net/` (the main
  tree's `Proof/net/http` is over the main tree's names-only translation, not `Net/`'s model, so it
  cannot be imported here). `math/rand`'s are generated (`define_is_pkg_init`). The lab hand-proved
  gryff's packages' initializations (`GryffProof/Client/Init.lean`), so `gen-init`'s `dsv_hyp_fix`
  is not needed for the package inits; the programs' `PkgTable`s (dsv_inits) will take the classes
  the same way.

**To be stated** (as the port reaches their call sites; each a field of a class named after the
lab's spec):
1. **net/rpc's server side** (plan 5.2, items 4-6; `models-rpc-server` in progress): the master runs
   `rpc.NewServer`, `Server.Register`, `Server.HandleHTTP`, `http.Serve(l, nil)`; a replica
   `rpc.Register`, `rpc.HandleHTTP`, `http.Serve`; both `rpc.DialHTTP` + `Client.Call` (replica ->
   master `Master.Register`; master -> replica `Replica.Ping`, `Replica.BeTheLeader`). The lab's:
   `Harness/Proof/net/rpc/{Server,HandleHTTP,HttpPath,Setup,initialize}.lean`.
2. **net/http's server** (plan 5.2 item 7): `http.Serve`, `Server.Serve`, `conn.serve` up to the
   hijack, `ServeMux.ServeHTTP`/`Handle`, `ReadResponse` on the CONNECT answer. The lab's:
   `Harness/Proof/net/http/{Serve,Mux,Handler,Head}.lean`.
3. **bufio**: no longer a hypothesis: the revised `origin/dsv-bufio` (`75ef5881aa`) is merged
   (see "Next", item 3, for the current names). Older list (pre-revision names): `EtcdGrove.bufio.NewReader.specOk`, `Reader.Read.specOk`, `Reader.ReadByte.spec`,
   `NewWriter.spec`, `Writer.Write.spec`, `Writer.WriteByte.spec`, `Writer.Flush.spec` over
   `ownBufReader`/`ownBufWriter` (contracts `io.readerOk`/`io.writerOk`), `ownBufReader_readerOk`
   for Perennial's `io.wp_ReadFull`/`ReadAtLeast`, `Net/Proof/net/ConnIo.lean`'s
   `conn_readerOk`/`conn_writerOk`. Gryff's translation calls exactly `NewReader`, `NewWriter`,
   `Read`, `ReadByte`, `Write`, `WriteByte`, `Flush` (not `Available`/`Buffered`). The lab's:
   `wp_NewWriter`, `wp_Flush`, `wp_WriteByte`, `wp_Write`, `wp_NewReader`, `wp_ReadByte`, `wp_Read`,
   `wp_ReadAtLeast`, `wp_ReadFull` (`Harness/Proof/bufio/{Writer,Reader,ReadFull,Net}.lean`).
4. **Smaller pieces** the lab had as its own models: `log` (`Printf`/`Println`/`Fatal`,
   `Harness/Proof/log.lean`), `math` extras (`Harness/Proof/math/Extra.lean`), `math/rand`'s
   functions, `time`/`strings` extras (`Harness/Code/{time_extra,strings_extra}`). No third-party
   library the lab replaced with a cut-down copy is reached by gryff (no gods, uuid,
   concurrent-map); `encoding/json`/`io/ioutil` are avoided (`stats.toml`).

How far the missing pieces reach into the lab's proof (its import graph, 369 modules, 112k lines): only
21 modules (5k lines: `Model/` the replica's step model, `Kahn/`, the tag order, a few defs) reach
no library spec. Everything else, the pure protocol layers (`Pure*`, `Proto*`) included, imports
the lab's library vocabulary transitively, through the shared ghost names and invariant modules
(`GryffProof/Names.lean` imports `Harness.Proof.net.rpc.Results` and `net/http`'s `Mux`;
`Proto/` imports the `NetConn` specs and `bufio.Base`). The `NetConn` part is what the port
replaces by `Net/`'s specs anyway; the rpc/http and bufio parts are items 1-3. Done: `Names` is split
(it imports `Net/`'s `RpcWorld` only), so the pure layers port without any hypothesis.

## Findings

- **rpcgen emitted an unused import** (a receiver whose package holds none of the codec's types,
  gryff's `*masterlib.Master`, `*gryff.Replica`, was imported by `rpc_gen.go`, which did not
  compile). Fixed on lean (`660918251a`); this branch merged it and its generated files pass
  `rpcgen.py --check`.
- The fork's `goose.sh` (lab kitgen) lists names-only declarations (`EPaxosRMWHandler.handlePropose`
  ...); the proof's translation (`proof/etc/goose.sh`) translates everything, and so does this one.
- The fork carries its ghost code in the Go (the trace prophecy, `src/gryff/proph.go`, marked
  "verification workaround"), as the lab's forks do; this repository's rule is prophecy patches
  (`etc/proph-patches/`). Kept as the lab's for now (as dsv-paxos kept its fork's), to decide.

## What changed against the lab (proof)

- **Connection ids are `Nat`** (`Net/`'s `cn`), not the lab's `w64`: the ghost maps `conns`
  (`GMap w32 (Option Nat)`), `placers` (`GMap Nat Int`), `connRep` (`GMap Nat Nat`) and every
  `cid`/`conn` binder (`Proto/InvDefs`, `InvSteps`, `Wire`, `WireLaws`, `Proto2/InvDefs`,
  `Proto2P/{Ghost,Facts,Init}`, `StartInit`).
- **The placers' invariant** (`Proto/Wire.lean`'s `placersInv`): the lab made each placed
  connection's fresh acceptor token read-only (its harness's fresh tokens were ghost-map elements,
  `connPlacedG`, `WS/Placed.lean`); `Net/`'s `connFresh` is an exclusive token with no persistent
  form, so the invariant now holds the tokens themselves, plus the authority of a new ghost map
  `ProtoNames.placed` (`Nat ↦ Unit`, same domain as the placers map) whose persistent element
  `connPlaced γ cid` witnesses placement; `placedConn γ cid` = the invariant ∗ that element, and
  `placedConn_fresh` opens the invariant and uses `connFresh_excl`. `WS/Placed.lean` is gone.
- `Proto/WireLaws`' laws take `□ protoInvs γ` (Gryff's invariant and the placers', `Proto/Wire`)
  in place of the hub's `sharedInvs` (`Shares.lean`, which imports the deployment); the hub's
  `sharedInvs` will contain `protoInvs`.
- The replicas' ports are the kit's (`portAddr k` = `127.0.0.1:750(2+k)`), not the lab's
  `10.77.0.x` rig addresses.
- The Net-facing layers are generic in `GF` with paxos's section variables (`[GooseExts]
  [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext] {GF} [G : GooseGlobalGS .hasLC
  GF] [π : NetProtoGS]`, `attribute [local instance] GooseGlobalGS.gooseInvGS`) in place of the
  lab's fixed `netDistGF`.

## net/rpc's server: models-rpc-server merged

`origin/models-rpc-server` (`040ef5e808`, the whole net/rpc server proved on Lean's three axioms;
not landed, waiting for review; the coordinator's instruction of 2026-11-23) is **merged** into this
branch (merge `061b255f51`), so the proof builds against its specs (`Net/Spec/net/rpc/
{NewServer,Server__Register,Server__ServeConn,Server__Accept,Dial,Client__Call}.lean`, ...)
directly. **It does not cover Gryff's HTTP transport of net/rpc**: `Server.HandleHTTP`,
`rpc.HandleHTTP`, `rpc.DialHTTP` (`DialHTTPPath`'s CONNECT handshake) and `http.Serve` (the master
and the replicas serve net/rpc over HTTP, `masterlib/master.go`, `serverlib/server.go`). Those stay
hypotheses (items 1-2 below); the fork's Go is not changed to avoid them (coordinator's decision,
2026-11-23). Such a hypothesis must use a protocol of the HTTP handshake followed by frames: the
model's `DialHTTPPath` writes `"CONNECT /_goRPC_ HTTP/1.0\n\n"` before `NewClient`, and
`ServeHTTP` reads it before any frame, so "DialHTTP returns `Net/`'s `isClient` over `rpcAddr`"
(frames from byte 0) is false of the model (`isClient`'s `sendInv` needs every written byte to be a
prefix of `reqsWire`). Name them after the plan's phase 5.2 specs (`notes/dsverify-net-port-plan.md`,
~580-725); the coordinator asked upamanyus on #24 for that `Net/` piece. **Intended shapes** (upamanyus,
#24; branch `models-rpc-http`, stacked on `models-rpc-server`, after the wildcard listen work; no
date): `rpcAddrP a hs …` (client-to-server bytes `hs ++ reqsWire`, server-to-client
`hsAns ++ ansWire`; `rpcAddr a … := rpcAddrP a [] [] …`; over HTTP `hs := connectReq path`,
`hsAns` = `HTTP/1.0 200 Connected to Go RPC\n\n`), `rpc.DialHTTPPath.spec`/`rpc.DialHTTP.spec`
(`isClient` or an error), `rpc.Server.ServeHTTP.spec`, `rpc.Server.HandleHTTP.spec rpcPath
debugPath`/`rpc.HandleHTTP.spec` (registration on `DefaultServeMux`; the debug path never
requested), `http.ListenAndServe.spec`/`http.Serve.spec`/`ServeMux.ServeHTTP.spec` (the server up
to the hijack, handlers as `handlerOk` per path). Gryff's hypotheses must match these names and
shapes exactly (gryff's clients do not pipeline after `CONNECT`: `DialHTTPPath` waits for the
answer).

## Wildcard listens

The master and the replicas listen on `":p"` (`masterlib.NewMaster`, `serverlib.Serve`, the
replicas' peer port). `lean` now has `net-wildcard-listen` (merged here): `Listen.spec` covers
wildcard addresses (`listenOk`), `Listener.Accept.spec` takes `lisAccepts la a`; laws `lisUnset`,
`lisProto la P Q`, `lis_set_proto`, `lisProto_addr`, `listen_lis_au`, `accept_lis_au`,
`accept_lis_shared_au`, `addrs_lis_start` (`GooseLang/Ext/Net/Proto.lean`); the valid-address
shapes are `Listen.spec_addrOk`/`Listener.Accept.spec_addrOk` (`Net/Proof/net/AtAddr.lean`). Use
them, not a hypothesis. A wildcard on port `p` covers `p` on every machine: the kit's ports are all
distinct (7501..7504, 8502..8504, 7511..7516), as it needs.

## The trace prophecy as a prophecy patch: blocked by prophcheck's grammar

Coordinator's decision (2026-11-23): move the fork's ghost prophecy code into
`etc/proph-patches/dsv-gryff/*.patch` (CLAUDE.md, `etc/proph-patches/README.md`,
`notes/decisions.md` "Prophecies as patches of the Go code"), checked by `etc/prophcheck`, so that
`examples/dsverify/gryff` is the lab's fork minus its ghost code. **It cannot be done as
prophcheck stands.** The ghost code (lines marked `(ghost code`; checked 2026-11-23):
- `src/gryff/proph.go` (294 lines, a whole new file): a package variable `traceProph
  primitive.ProphId` set by `init()` (`primitive.NewProph()`), the event codes, and 28 helper
  methods `(r *Replica) resolve<Event>(m)` that resolve the event's fields through the struct
  field `r.proph` (`resolveCmds`/`resolveDeps` with `for` loops over the command slice and the
  `[5]int32` array);
- `src/gryff/tupaq.go`: the `primitive` import, the `Replica` field `proph primitive.ProphId`,
  `proph := traceProph` in `NewReplica` and the positional composite literal's extra element;
- `src/gryff/epaxosrmwhandler.go` (26 sites) and `epaxos-exec.go` (1): calls
  `e.R.resolve<Event>(msg)` before each handled event, under the replica's lock.

prophcheck accepts only `NAME := primitive.NewProph()` (a local, declared in the same function),
`NAME.Resolve{Bool,U64}(E)` and `if` statements of those, with read-only `E`. It rejects a new
file, a package variable, `init()`, a struct field (and the positional literal's element), helper
methods and calls to them, and `for` loops: run on the three files' pairs (the fork minus the
`(ghost code` lines vs the fork; scratch copy, `go build ./src/...` of the stripped fork is
green), it reports for each "with its prophecy statements erased, it is not orig". The design is
one prophecy per replica (the stage-2 trace prophecy, the lab's D9/D13), created once and resolved
by every goroutine of the replica through the struct; prophcheck's prophecies are per function
invocation. A choice of where it is created (init, main or the node's start) does not help: the
resolutions are in other functions.

Options (decision for the coordinator / the prophcheck owner; nothing changed in the Go yet, the
fork still carries the ghost code):
1. **Extend prophcheck** with what the trace prophecy needs, each effect-free (the soundness
   argument stays "the patched program may fail more, never behave more"): a struct field of type
   `primitive.ProphId` added by the patch (keyed composite literals only, or the positional
   literal's extra element at the end); its initialisation from a patch-declared prophecy;
   resolutions through field selections (`r.proph.ResolveU64(E)`); helper functions/methods whose
   bodies are prophecy statements only, and calls to them as statements with read-only arguments;
   `for` loops with read-only bounds whose bodies are prophecy statements; a new file of only such
   declarations. A struct field changes the type's size and its `reflect` view (the `Replica` is
   registered with net/rpc, which reflects on its methods, not its fields; the generated codec
   names no `Replica` field).
2. **Restructure the proof** onto per-event local prophecies (one `NewProph` per handled event,
   resolved in the same function): a redesign of the lab's stage 2 (`Proto2*`, `Replica2`, D9,
   D13), not a port.
3. Keep the ghost code in the fork (as dsv-paxos kept its fork's), recorded as a deviation.

Until then gen-init's configuration for the `gryff` package (its `init()` and `traceProph`) waits
on this choice; `dlog.DLOG`, `gryff.stack` and the kit's `var _ = fmt.Sprint` are ordinary.

## Which lab run

Ported: run **`gryff-bump-1`** (dsverify-lab `master` `915f964`, `examples/gryff/`; proof
`21ef7d6` tag `final`, fork `ef17c2d`, verified in 1066 s; `dsv_goal_check : SafeDist (orch ::
clients ++ servers) gryffNetCfg`, axioms Lean's three and porcupine's `CheckOperations.wp_proof`).

## Next

Remaining lab modules (as of `858378e8aa`, by directory): B 16, Client 12, H1 32, H2 6, H2a 9,
H2b 3, H2c 7, H2c2 5, H3 6, N 26, Proto2/Replica 1, Replica 2, Replica2 3, Rpc 6, S 1, Server 16,
Shares, Start, Top, Wire 11 (`Wire/Specs`, `Wire/Proof/*`), X 15. The port helper used this
session copies a lab file with the mechanical renames (header line, `GryffProof.` ->
`Dsverify.Proof.gryff.`, `Gryff.{GeneratedProof,Code}.` -> `Dsverify.{GeneratedProof,Code}.`,
`unusedSectionVars`); then by hand: `attribute [local instance] netConnExts ...` ->
`attribute [local instance] GooseGlobalGS.gooseInvGS`, the section variables (paxos's, above),
`netDistGF` -> `GF`, `open ... NetConn Dsv` -> `Net`, `connFreshG netDistGS` -> `connFresh`,
`sentLbG netDistGS` -> `sentLb`, `addrProtoG netDistGS` -> `addrProto`, `addrTokG` ->
`addrTok`, connection ids `w64` -> `Nat`, `[GooseExts]` on defs that used `netConnExts`
implicitly. The order (the frontier of modules whose imports are ported):

1. **Package initializers** (unblocks every Go-level proof, the kit's `ModelProof` first):
   `etc/dsv/gryff.py` has no gen-init configuration yet. Model it on `origin/dsv-epaxos`'s
   `etc/dsv/epaxos.py` (same codebase family: `PKGS`, `PROGRAMS` for the eleven commands, `MAIN =
   ['bufio', ...]`, `MAIN_GEN`, `HYP_INITS = ['net.rpc', 'net.http', 'math.rand'?]`, `HYP_IMPORTS =
   'none'`, `special(g)`). Gryff's package variables: `dlog.DLOG` (bool), `gryff.stack`
   (`make([]*Instance, 0, 100)`) and `gryff.traceProph` with `gryff`'s `init()` (`proph.go`:
   `primitive.NewProph()`, the trace prophecy, ghost code D13), `gryffnet`'s `var _ = fmt.Sprint`.
   The prophecy is the hard part: the lab's hand-written init proof (`GryffProof/Client/Init.lean`,
   `Server/...`) hands the node its prophecy resource (`nodeProph`, `pred_set`), which a
   persistent `Init` fact cannot carry; decide with the coordinator (the repository's rule is
   prophecy patches, `etc/proph-patches/`, not ghost code in the fork). Every `[<pkg>.InitHyp GF]`
   must stay a visible premise of the statement (etc/dsv/README.md); confirm `etc/theorem-loc.py`
   counts them when the statement exists.
2. **The kit's model, Go-level** (`ModelProof.lean`, as paxos's): the representation is a
   read-only slice of `Cfg{V, Pend}` structs, each `Pend` a read-only slice of `In`; `reach`'s
   loop invariant: `out` holds the start, every element `AReach`-reachable from it, and every
   element below `k` has all its successors (`without`) in `out`; at the end it is closed, so its
   members are exactly the `AReach`-reachable ones; `step`'s second loop builds a `cs'` with
   `knownCfgs`' members (`hasCfg` dedups by exact equality). Then the `ModelSpec` (as paxos's
   `woS0`/`woS`) and `Model()`'s spec.
3. **bufio**: the revised `origin/dsv-bufio` (`75ef5881aa`, under re-review, not landed) is
   **merged** into this branch (coordinator, 2026-11-23); use its names directly and never unfold
   the bufio predicates (the table in the last section of `notes/dsv-bufio.md`). The lab's uses
   map to: `bufio.ownReader`/`ownWriter` -> `ownBufReader`/`ownBufWriter` (a size index `sz`
   after `Ew`); `readerOk_conn`/`writerOk_conn` -> `Net/Proof/net/ConnIo.lean`'s
   `conn_readerOk`/`conn_writerOk`; `wp_NewReader`, `wp_ReadByte`, `wp_Read` (takes
   `⌜0 < xs.length → Pre R xs.length⌝`; `preUpTo S Pre n` is an `IProp`), `wp_ReadFull` (Perennial's
   `io.ReadFull` through `ReaderLaws`), `wp_NewWriter`, `wp_Write`/`wp_WriteByte` (take
   `⌜err = nil⌝ -∗ □ Q`; a write that fits gives `e = nil ∧ sent' = sent`: the lab's
   `writerRoom`/`wp_Write_room`/`wp_WriteByte_room`), `wp_Flush`; the lab's `ownWriter_sentLb` ->
   `bufio.ownBufWriter_fact`, its `ownReader_proto` -> `net.connReader_proto` (with
   `bufio.ownBufReader_fact`, `Net.recvTokL_proto`); `ownBufWriter_size`, `Writer.Available`/
   `Buffered`/`Size` specs are new.
   Then `N/NetDefs` and the rest of N (the replica's connections), `Wire/Specs` and
   `Wire/Proof/*` (the messages' Marshal/Unmarshal over bufio).
4. **net/rpc**: `Rpc/Defs` -> `Net/`'s vocabulary: the lab's `RpcCodec` (`enc`, `dec`, `call`,
   `methods`) is `Net/`'s `CodecSpec` (`enc`, `dec`, `rcv`) plus the server's method specs
   (`Net/Spec/net/rpc/Server__Register.lean`, `service__call.lean`; read how the server dispatches
   before porting `gryffCall`); the master's and replicas' addresses become the kit's
   (`127.0.0.1:7501`, replicas' net/rpc at `127.0.0.1:850x`); `Rpc/Codec*` (the generated codec's
   proofs, 2.6k lines) against `Net/`'s `encOk`/`decOk`/`rcvOk`. The HTTP transport
   (`HandleHTTP`, `DialHTTP`, `http.Serve`) as hypotheses named and shaped after
   `models-rpc-http`'s intended specs (above).
5. Server (master, registration), Replica2/B/H*/X (the replica), Client on remote (`Op(sys, in)`
   with remote's `lin` update in place of the lab's `opAU` at `clientN`, as paxos's `opAU`;
   `Proto/ClientLaws`' `opAU` is the lab's shape and must change), Start/Shares (the start's
   resources over remote's), Mains, Linked, `gryff_remote_robust` (`DistDeploy … → Robust [] …`),
   `etc/tcb-collections/dsv-gryff.txt`.
