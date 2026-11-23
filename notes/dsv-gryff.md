# dsv-gryff: dsverify-lab's gryff kit on the net extension (phase 6)

**Coordinator (2026-11-23, ~06:00):** `lean` moved to `e20bbac22f` (Perennial `c95e92207`, no checkout
on the host): do not merge it; stay on `07268ddb57` with `/shared/perennial-7b2259a12`.

Branch `dsv-gryff` (2026-11-23), off `origin/dsv-paxos` (paxos not landed on `lean` yet; merge
`origin/lean` once it is). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/gryff/` (run
**`gryff-bump-1`**, the final verified run: clients on nodes of their own, Perennial `3afd77e35`;
proof `21ef7d6` tag `final`, fork `ef17c2d`; read only, nothing in the lab changed).

**State (2026-11-23, third resumed session; branch merged with `lean` `07268ddb57` (dsv-paxos,
dsv-bufio with the `io.streamWriterOk` rename, dsv-infra, wildcard listen, Perennial `7b2259a12`;
this branch used none of the renamed names) and `models-rpc-server` `36728bd8ed` (not landed:
Client.Call's decode guard and the server's `argDec` guard); `gen-init --check`, `goose --check
--project dsv-gryff` and `etc/dsv/_gryff_boot.py --check` clean after regenerating the PkgTables):** Go and translation done. **Ported by editing and
building**: the library-free layers and the wire protocols (186 lab modules, see below), as before.
**New this session:** the **package initializers** (gen-init, all `Init`/`PkgTable`s build; section
"Package initializers"), the **replica boots** keeping `gryff`'s owned variables and trace
prophecy (`cmd/server{2,3,4}/Boot.lean`, `wp_initialize'_own`, Lean's three axioms), and the
**kit's model, Go-level** (`examples/gryffnet/ModelProof.lean`: `Model.wp_proof : Model.spec`,
`isModel casS`, Lean's three axioms; section "The kit's model"). Not done: the library-facing
layers above the wire (N, B, Rpc, Server, Client, H1-H3, X, Replica2, Start, Shares, Top), the
client on remote, Mains, Linked, `gryff_remote_robust`, the TCB collection. No `sorry`, no axiom
under `Dsverify/`.

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

**Stated in Lean (2026-11-23, fourth session):**
- **`wire.BinaryVarintHyps GF`** (`Dsverify/Proof/gryff/Wire/Proof/VarintWp.lean`): `encoding/binary`'s
  `ReadUvarint`, `ReadVarint`, `PutUvarint`, `PutVarint`, the lab's four statements (`wp_ReadUvarint`,
  ...) over dsv-bufio's reader. Perennial `7b2259a12` translates these four names only
  (`Perennial/Code/encoding/binary.toml`'s `translate` lacks them); the lab proved them over its own
  hand translation (`Harness/Code/binary_extra.lean` + `encoding.binary.ExtraAssumptions`, trusted
  code, not allowed here). Translating `encoding/binary` into the part (as the main tree does `io/fs`)
  would clash with Perennial's `encoding.binary` constants, which the kit also uses (`LittleEndian`).
  **Proposed Perennial change**: add `"ReadUvarint", "ReadVarint", "PutUvarint", "PutVarint"` to
  `binary.toml`; then the lab's proofs (`proof/GryffProof/Wire/Proof/VarintWp.lean` at `21ef7d6`, its
  `wp_ReadUvarint`... bodies) discharge the class, with `ReadByte` from dsv-bufio (no copied
  `wp_ReadByte_wf` needed: `Reader.ReadByte.spec` gives `io.ptrTyped`). To record in
  `notes/perennial-changes.md` when the port is done. A premise of the statement (never an instance).

**Library gaps the lab filled with its own translations** (`proof/Harness/Code/*_extra.lean` + an
`<pkg>.ExtraAssumptions` class of `FuncUnfold`s: trusted code, not allowed here), checked against
Perennial `7b2259a12` (2026-11-23): `encoding.binary` varints (now `BinaryVarintHyps`, above);
`io.ExtraAssumptions` (21 lab uses: `ReadFull`/`ReadAtLeast`): **not needed**, Perennial proves both
(`io.wp_ReadFull`, `io.wp_ReadAtLeast`); `strconv` `Atoi`/`Itoa` and `time.Time.IsZero`: **translated by
Perennial now** (use its specs or prove over its bodies); still names only, to become hypotheses where
reached: `sort.Ints`/`sort.Slice` (1 lab use), `math.Pow` (1), `strings.Index` (1, `N/StrIndex.lean`),
`time.Time.UTC` (with `IsZero`, `Replica/Base.lean`'s `wp_Time_IsZero`).

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

- **gen-init rewrote ~20 main-tree `Proof/go_etcd_io/etcd/server/**` `Init`/`InitLinked` files on this
  branch: a merge mistake of this branch, fixed 2026-11-23.** Not lean (a clean `origin/lean`
  `07268ddb57` worktree: `gen-init --check` clean), not `etc/dsv/gryff.py` (with it disabled the same
  20 files differed), not dsv-infra. This branch's merge `40cff860fc` ("migrate onto dsv-infra")
  resolved `etc/gen-init.py` and `etc/goose.py` to dsv-infra's `a1046d9c4f` versions, dropping
  lean's `prove-ps2-metrics` hunks (`92a9fd7b78`: `gauge_rep`, `MetricLaws`/`gauge__*` in
  `PROM_CTORS`, `ipersist HisLearner`/`HknownPeers`/`HtotalEventsCounter`, goose's
  `prometheus/client_model/go` names-only package) that this branch already had; every later merge
  kept the branch's side. Restored both scripts to `origin/lean`'s (this branch has no line of its
  own in them; its configuration is `etc/dsv/gryff.py`). After: `gen-init --check` clean (main tree
  and both kits), `goose --check --project dsv-gryff` clean. (`gen-init`'s "N files up to date"
  counts the main tree's packages only; the kits' files are checked too.) Other shared files the
  merge touched (`notes/*`) differ from lean only by additions.

- **Link check (VR's finding 7, coordinator 2026-11-23): nothing vacuous here.** For each of the eleven
  programs, `go list -deps ./examples/gryffnet/cmd/<n>`'s `gryff/...` packages equal the `pkg_id.gryff.*`
  packages of its `PkgTable.lean` (all 16 fork packages, `gryffnet`, the command: every command imports
  `gryffnet`, which imports the whole fork). Every package fact of the kit is `True` (the `Base.lean`s; the
  hypothesis packages' too), so no fact relies on a hook another package's init sets. The only `init()` is
  `gryff`'s (`proph.go`, the trace prophecy), linked into every program; the replicas take its resources from
  their own boot (`Boot.lean`), not from a fact.

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

- **bufio is dsv-bufio's** (`Wire/Proof/Lemmas.lean`, sections "The writer", "The reader"). The lab's
  harness predicates become abbreviations over dsv-bufio's, never unfolded: `ownWriter bw wr J Q sent
  pend err := EtcdGrove.bufio.ownBufWriter bw wr.wi J Q wr.Ew wr.sz …`, `writerOk wr J Q :=
  EtcdGrove.io.streamWriterOk wr.wi J Q wr.Ew`, `ownReader br rd I R := EtcdGrove.bufio.ownBufReader br
  rd.ri (fun _ m => 0 < m) I rd.E R` (the read condition a connection gives). The new fixed
  parameters are bundled (`WSt := {wi, Ew, sz}`, `RSt := {ri, E}`), so the lab's `wr J Q` / `rd I`
  argument shapes stay and the port is mechanical (`(wr : GoInterface)` -> `(wr : WSt GF)`).
  `readerOk rd I` is now `isPkgInit io ∗ isPkgInit bufio` (the lab's held the reader's contract, which
  is inside `ownBufReader`). `io.ReadAtLeast`/`io.ReadFull` go through Perennial's specs and
  `bufio.ownBufReader_readerOk` (`wp_wire_ReadAtLeast`, `wp_wire_ReadFull`, `_arr`).
- **Facts of the bytes ahead are `readNext br rd I R P`** (`Lemmas.lean`): `□ ∀ V, ownReader … (R ++ V)
  ={⊤}=∗ ownReader … (R ++ V) ∗ ⌜∃ pend, P (V ++ pend)⌝`, stated of the reader resource. The lab's
  premise `□ (∀ D, I (R ++ D) ={⊤}=∗ I (R ++ D) ∗ ⌜P D⌝)` needed its `ownReader_peek`, which unfolded
  the reader to reach the buffered bytes (forbidden now). `readNext` is that lemma's conclusion as the
  premise; laws `readNext_true`, `readNext_shift`, `readNext_mono`, `ownReader_peek`. For a
  connection it is to be derived from `net.connReader_proto` (a later, stripped under the update since
  the fact is pure) in N.
- **Read errors are `rdErr rd err`** (`Lemmas.lean`): `⌜err ≠ nil⌝ ∗ □ (errE rd.E r err for some r ∨
  ErrUnexpectedEOF's value ∨ ErrShortBuffer's ∨ binary.errOverflow's)`, in place of the lab's
  `net.rpc.errAny err ∗ ⌜errWf err⌝` (which its harness reader gave). N must prove, for the
  connection's `E` (`net.connReadE`: `io.EOF` or a `netErr` `*OpError`), what `replicaListener`/
  `clientListener` need of it: `err != io.EOF` (`io.ptrTyped`: `net.eof_ptrTyped`, `netErr_ptrTyped`) and
  `log.Printf("… %v", err)` (an `Error()` method: `models_lab.errAny`, or Perennial's
  `errors.newVar` for the `io` ones).
- Mechanical rewrites of these (scratch script, reproducible from this list): `open … NetConn Dsv bufio`
  -> `open …`; drop `attribute [local instance] netConnExts …` and add `[GooseExts] [GooseSemantics]
  [GooseInterp]`; `(rd : GoInterface)`/`(wr : GoInterface)` -> `RSt GF`/`WSt GF`; the `nextOk` premise
  -> `readNext br rd I R X.nextOk`; `net.rpc.errAny err ∗ ⌜errWf err⌝` -> `rdErr rd err` (and the
  `%Hwf` patterns and `exact Hwf` splits dropped); the nested `iintro !> %D HI; …; trivial` ->
  `iapply readNext_true; intro; trivial`; `[io.ExtraAssumptions]` dropped,
  `[encoding.binary.ExtraAssumptions]` -> `[BinaryVarintHyps GF]` (only in files importing
  `VarintWp`); `· iexact Hpkg2` after `wp_wire_Read*` dropped (`readerOk` holds the inits);
  `encoding.binary` lemmas from `Perennial.Proof.encoding.binary.Results`; the packages' `IsPkgInit`
  instances from `Dsverify/Proof/gryff/src/<pkg>/Base.lean` (imported by `Wire/Proof/State.lean`).

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

## Package initializers (done 2026-11-23)

`etc/dsv/gryff.py` configures gen-init (`PKGS`: the 16 fork packages, `gryffnet`, the eleven
commands; `PROGRAMS`: their `PkgTable.lean`s; `MAIN`/`MAIN_GEN` as EPaxos's; `HYP_INITS =
['net.rpc', 'net.http', 'math.rand']`, `HYP_IMPORTS = 'none'`; `special`: `dlog`'s `DLOG`, `gryff`'s
seventeen variables, `stack`'s `make3`, `deferMap`'s `make1`, `init()`'s `NewProph`). The packages'
facts are all `True`, hand-written `Dsverify/Proof/gryff/{src/*,examples/gryffnet{,/cmd/*}}/Base.lean`
(written by a scratch script from each package's `PkgInfo` imports; the lab's `GryffNetPkgState`
class instances, `Slots.lean`, are gone). `math/rand`'s `Base` is now names-only like net/rpc's
(`HYP_IMPORTS = 'none'` cuts its `sync` import from the tables). Every `Init.lean`, `PkgTable.lean`
builds (`lake build` of the eleven `PkgTable`s, 2636 jobs).

**The replica's owned init (the prophecy's design).** `gryff`'s initializer makes owned resources:
its mutable variables (`gryffGlobals`: `stack`, `cpMarker`, counters, message buffers, `deferMap`,
`bf_PT`) and the trace prophecy (`traceProph ↦ p ∗ proph p pvs`, `bootProph`). A package fact is a
persistent `isPkgInit`, so the generated `wp_initialize'` drops them (it is what the master's, the
clients' and the orchestrator's boots use). A replica node gets them from **its own boot**:
`Dsverify/Proof/gryff/examples/gryffnet/cmd/server{2,3,4}/Boot.lean`, `wp_initialize'_own`:

    {{ ownGoState ∅ }} cmd.serverK.initialize' #()
    {{ RET #(); ownInitializing getIsPkgInit ∗ isPkgInit cmd.serverK ∗ gryffGlobals ∗ bootProph }}

(the deployment's `wp_boot` starts every machine from `ownGoState ∅`; its replica instances will
take this in place of the generated `wp_initialize'` and hand `gryffGlobals ∗ bootProph` to
`main`). The proof is the lab's (`GryffProof/B/Init.lean`): every package before `gryff` runs with
`gNo g` (`g` but `False` at `gryff`, `gryffnet` and the commands, `Boot/Defs.lean`'s `noPkgs`), so
`gryff`'s, `gryffnet`'s and the command's `package.init` take their first branch
(`wp_package_init_gen`, returning the extra resources). The facts `GetIsPkgInitProp q (gNo g)` and
`(q g)` are the program table's, package by package (`wfNo_<q>`, `wf_<q>`, no tree unfolding).
`Boot.lean` is **generated** by `etc/dsv/_gryff_boot.py` (run after `etc/gen-init.py`; `--check`)
from the `PkgTable.lean` and the generated `wp_initialize'_lb` bodies' import steps; the shared
lemmas and `gryffGlobals`/`bootProph` are hand-written in `Boot/Defs.lean`. Nothing is persistent:
no invariant, no ghost name is needed at init time.

## The kit's model, Go-level (done 2026-11-23)

`Dsverify/Proof/gryff/examples/gryffnet/ModelProof.lean` (one file; builds, `#print axioms
Model.wp_proof`: Lean's three). The spec: `casS : ModelSpec GF (PSet w64 In)`, `M := pM casB casDec`
(`casDec`: a boxed `In` and a boxed `Out`, `.err` when `Out.Unknown`), `casS0` its
representation-free form (for the pending library, as paxos's `woS0`), `casRep k v s`: `v` the boxed
`State{sl}`, `sl ↦*□ cs`, `cfgsOk cs L` (each Go `Cfg` stands for a `GCfg`: its `V` and its `Pend`
slice read-only holding the pending list), `s = cfgSet L`, `L ≠ []`, pending lists at most `k` long.
`Model.spec`: `{{ isPkgInit kpkg }} Model() {{ m, RET #m; isModel casS m }}`. Helper specs:
`wp_apply`, `wp_isWrite`, `wp_without` (needs `0 ≤ i`), `wp_with`, `wp_sameCfg`, `wp_hasCfg`
(`decide (g ∈ L)`), `wp_reach` (the returned list's members are exactly the `AReach`-reachable
ones: loop invariants "every member reachable" and "members below `k` have all their successors";
closure by `areach_closed`), `wp_stepGo` (`stepRes`: `pSeq casB`'s step, via `stepG_pSeq` /
`pseq_unknown`), `wp_equal`. These definitions (`casS0`, `casS`, `casDec`, `inV`, `outV`) are the
kit's Kit-level vocabulary; move them to a `Kit.lean` when the deployment is written (paxos keeps
them in `Kit.lean`).

Proof-mode workarounds found (record for Perennial, `notes/perennial-changes.md` if they persist):
- `wp_alloc`/`wp_auto` do not take `#(zero_val w64)` (at `go.int64`) or `#(zero_val Bool)` as an
  allocation's value (`isIntoVal?` fails on them): local `goose_wp_simp_extra` lemmas
  `zero_val_w64`, `zero_val_bool`, `zero_val_Out` rewrite them to literals.
- A field of a slice element (`s.Cfgs[i].V`) loads only from explicit field points-to: take the
  element's `↦□` from `ownSlice_elem_acc`, then `(Cfg.Cfg_access_load_V _ v _).access_strict` (the
  generated `AccessStrict` instances) for each field; `wp_load` does not find them through the
  element points-to.
- `etc/lean-check.py`'s server reports spurious `(kernel) application type mismatch` errors naming
  an earlier declaration's `_proof_N` (and, after a real error, cascades into unrelated branches):
  `--stop` and recheck, and confirm with `lake env lean`/`lake build` (both clean).

## PENDING for the user: the prophecy ghost code is in the fork

Interim decision (coordinator, 2026-11-23; the user's final choice is pending): the fork's Go is kept
exactly as the lab's, **ghost prophecy code included** (`src/gryff/proph.go`, the `Replica.proph`
field, the 27 `resolve<Event>` calls), **against this repository's rule that prophecies are
patches** (`etc/proph-patches/`, `notes/decisions.md` "Prophecies as patches of the Go code"). The
translation options (1) (extend prophcheck, below) and (3) (a recorded deviation) produce is the
same, so the proofs over it hold under either; option (2) (local prophecies) is not pursued.

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

## Session 5 (2026-11-23, fifth agent): state and decisions

**Tiers: 0 new violations** (`etc/tier-check.py --check` ok at `f3ce081156`). The wire layer sees
dsv-bufio only through its specs: `wire.BufioSpecs GF` (`Wire/Proof/Lemmas.lean`, a `Prop` class:
`Writer.Write.spec`, `Writer.Flush.spec`, `Writer.WriteByte.spec`, `NewWriter.spec`,
`NewReader.specOk`, `Reader.Read.specOk`, `Reader.ReadByte.spec`), a section variable wherever
`[bufio.Assumptions]` or `[gA : examples.gryffnet.Assumptions]` is; discharged at linking by
`⟨Writer.Write.wp_proof Writer.Flush.wp_proof, Writer.Flush.wp_proof, Writer.WriteByte.wp_proof
Writer.Flush.wp_proof, NewWriter.wp_proof NewWriterSize.wp_proof, NewReader.wp_proofOk
(NewReader.wp_proofE NewReaderSize.wp_proofE), Reader.Read.wp_proofOk, Reader.ReadByte.wp_proof⟩`
(no instance anywhere). Lab-style modules naming theorems `wp_<f>` are defs tier, so ported files
importing each other are fine; only `*.wp_proof` modules must not be imported.

**Ported this session** (all `etc/lean-check.py -a` clean): `Proto2/Replica` (`req_mint` over
`protoInvs` and the new `placersInv`), `Replica/ExecDefs`, `Replica2/State`, `N/{NetDefs, Stats,
SpecsDefs, StateLaws, ConnDefs, Handshake, PeerMark, Build, Register, SendMsg, Recv, Reply}`,
`Server/LogErr`, `N/Listener`, `Lib/{NetAddr,Proph}` (`(*TCPAddr).String` over the model;
the lab's Proph helper, `go.NotInterface go.prophId`), `X/{Defs,Pure,Tag,Sort,Laws,Facts,Helpers,
Access,InStack,Slot,SC,Cmds,ExecCmds}`, `B/{Ctor,LockBoot,Names,Step,Resolve,Loop,Run}`. Abbrevs of
method values (`repMB`, `epMB`) go in a section with only `[GooseExts] [GoGlobalContext]
[GoSemanticsFunctions]` (else `go.Semantics` is stuck on `GF`); `replicaProph (GF := GF) γ`.

**log with error arguments: no hypothesis** (`Server/LogErr.lean`): Perennial `7b2259a12` models
`log.Printf`/`log.Println` as trusted no-ops (and specifies `Printf` only with `fmt.ArgsWf`); the
lab's `log.wp_Printf_logArg`/`wp_Println_logArg` (an error argument: `models_lab.errAny`, its
`Error()` runs) are proved from those bodies (coordinator, rabia review point 5: don't assume
functions Perennial gives bodies for).

**Rabia review lessons (coordinator 2026-11-23, `rabia-review-24.txt`), checked here:** the
`InitHyp`s (`net.rpc`, `net.http`, `math.rand`) assert only that the initializer runs (fact
`True`); `BinaryVarintHyps` carries Go's preconditions (`PutUvarint`/`PutVarint`: the buffer
holds the encoding, `PutVarint` only for `0 ≤ x`; the readers: an owned non-nil `*bufio.Reader`,
errors as `rdErr`, `errOverflow` included). To check as they are written: `math/rand.Seed` (gryff's
`NewReplica` calls it; a hypothesis must need what Go needs), any `sort`/`strings`/`time` extras
(`strings.Index`: N/StrIndex), the HTTP server hypotheses.

**Rewrite rules added** (scratch `port/nport.py`, `port/nextok.py`, reproducible from this list):
- section variables: `[GoGlobalContext] [hG : HeapGS .hasLC netDistGF] [sem]` -> `[GooseExts]
  [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext] {GF} [hG : HeapGS .hasLC GF]
  [π : NetProtoGS] [sem]` (use `hG`, not `G : GooseGlobalGS`, where the heap is used);
  `local notation "GF" => netDistGF` dropped;
- instances/lemmas whose statement does not determine `GF` get `(GF := GF)` (e.g.
  `Persistent (aliveAt (GF := GF) k gR)`, `replicaOwnX (GF := GF) ρ …`);
- `[gA : examples.gryffnet.Assumptions]` stays (it is the kit package's class; import
  `Dsverify.GeneratedProof.gryff.examples.gryffnet`), plus `[wire.BufioSpecs GF]`;
  `strconv.ExtraAssumptions` -> `strconv.Assumptions` (Perennial's `strconv.wp_Itoa` takes
  `isPkgInit strconv`, from `isPkgInit_unfold_deps` of the caller's package);
- connection ids `w64` -> `Nat` (`∃ c : Nat, clientConnAt …`, `(c : Nat)` in `dialer_bridge`);
- `sharedInvs γ` (hub, `Shares.lean`) -> `protoInvs γ` where only Gryff's and the placers'
  invariants are used; `placersInv` destructs as `⟨%P, %D, >HPa, >HDa, >%hD, >HPm⟩`;
- the reader peeks: the lab's `□ (∀ D, I (R ++ D) ={⊤}=∗ I (R ++ D) ∗ ⌜P D⌝)` -> `wire.readNext br
  rd I R P` (statements), proof bullets -> `wire.readNext_true` / `wire.readNext_mono … $$ Hnx`;
  `peerReaderB`'s peek is now stated of the reader (`wire.ownReader rd rdi I (hdr ++ Y) ={⊤}=∗
  wire.ownReader … ∗ ∃ W, peerStreamOk … ∗ ⌜Y <+: W⌝`), so `ownReader_peer` is an update; where a
  peer reader is made (N/Connect, N/WaitPeers) it is to be derived from `net.connReader_proto`
  (`▷ protoPrefix`, pure/timeless facts stripped under the update);
- `bufio.wp_ReadByte` -> `wire.wp_ReadByte` (new wrapper, error as `rdErr`); the error branch
  `⟨%Herr, -, -, %v, %R', Hl, Hown⟩` -> `⟨%Herr, -, %v, %R', Hl, Hown⟩`.

**Coordinator's messages this session (to apply at the Rpc layer):**
- net/rpc over HTTP, client side, is on `origin/models-rpc-http` `1a4d9546c9` (stacked on
  models-rpc-server, not landed): `rpcAddrP W a hs hsAns`, `rpcAddr W a := rpcAddrP W a [] []`, the
  handshake per address in the world (`W.hs a`, `W.hsAns a`); `DialHTTPPath`/`DialHTTP` proved over
  `http.ReadResponse.spec` (stated, proof in progress). Merge it at Rpc and use its DialHTTP(Path)
  specs; keep the server side (`ServeHTTP`, `HandleHTTP`, `http.Serve`, mux) as hypotheses.
- Upamanyu's five answers (scratchpad `five-answers-24.txt`): wildcard listeners get `rpcLisP W la
  hs hsAns` (+ `rpcLisP_addr`/`_lis`/`_set`; shape: dsv-swiftpaxos `lib/RpcHttpHyps.lean`);
  `errOk` will cover only the server's own errors (`srvErrMsg`); `Client.Call`'s other errors get
  `∃ msg, errMsg err msg ∗ ⌜msg ≠ []⌝`; net/rpc's `codecFresh`/`srvEnv` will come from a per-machine
  boot resource (never `|==> codecFresh`). Keep these open points (callRet errMsg, codecFresh,
  errOk, wildcard listeners) as visible premises.

## Session 6 (2026-11-23, sixth agent): the two designs, decided

**Base.** `origin/models-rpc-http` `1a4d9546c9` merged (`7a40f81699`): `rpcAddrP`, `connectReq`,
`connectAns`, `defaultRPCPath`, `DialHTTPPath.spec`/`DialHTTP.spec` (proved over
`http.ReadResponse.spec`) are `Net/`'s now. Coordinator (07:2x): models-rpc-server LANDED, `lean` is
`c4e044df92` with Perennial `c95e92207` (`/shared/perennial-c95e92207`); we stay on `07268ddb57` +
`36728bd8ed`; when merging lean (at landing), repoint the overrides and `PERENNIAL_DIR` to
`/shared/perennial-c95e92207` and regenerate the PkgTables.

**Coordinator (later, session 6):** `Net.sentLb_agree`, `Net.sentLb_le`, `Net.recvTokL_sentLb` are
in `GooseLang/Ext/Net/Proto.lean` on `origin/dsv-protolaws` `4a7645929b` (pending Upamanyu's OK);
dsv-rabia landed (`lean` `06fe42e389`, Perennial `48401b6ba`; rabia's tcp layer is a template).
`dsv-protolaws` sits on that new `lean` (Perennial `48401b6ba`), so it is not merged here yet (we
stay on `07268ddb57`/`7b2259a12`). **When merging `lean`/`dsv-protolaws`:** delete
`N/ConnLaws.lean`'s local `sentLb_comparable`, `sentLb_le`, `recvTokL_sentLb` and use
`Net.sentLb_agree`, `Net.sentLb_le`, `Net.recvTokL_sentLb` (callers: `ownReader_sentLb`,
`dial_reader` in N/ConnLaws; grep the N/ and Client/ files).

**Coordinator (later): models-rpc-http `e6b232b2f6`** (merged with lean, not landed) proves
`rpcLisP W la hs hsAns` (`Net/Proof/net/rpc/Proto.lean`, over `lisProtoD`) with
`rpcLisP_addr/_addrOk/_lis/_ok/_set`, `Server.Accept.spec` for wildcards (`specAddr` exact), and
`rpc.Server.ServeHTTP.spec` (taking `hijackOk`). `RpcHttpHyp`'s `rpcLisP_lis` (now `Listen.spec`'s
update), `rpcLisP_ok` (new) and `rpcLisP_set` (premises `listenOk la`, `∀ a, addrOk a ∧ lisAccepts
la a → W.hs a = hs ∧ …`) are aligned to those shapes. **When it lands, merge it**: drop
`rpcLisP*` and `Server_ServeHTTP_spec` from `RpcHttpHyp` for Net's (the class keeps net/http's
server up to the hijack and `HandleHTTP`). dsv-protolaws LANDED (`lean` `bd14566295`): use `Net.sentLb_agree`/`sentLb_le`/`recvTokL_sentLb` at the next lean merge (see above).

**Design (1), the connections on `Net/` (decided, in `Replica2/Specs.lean` and `N/ConnLaws.lean`):**
- A replica listens at the wildcard `lisAddrOf a0` (`a0[strings.Index(a0, ":"):]`, `":7502"` for
  `portAddr 0`) of its node address `a0 ∈ replicaAddrs` (`Proto/Wire.lean`). The start sets, once,
  `lisProto (lisAddrOf a0) (gryffWireP γ a0) (gryffWireQ γ a0)` (`lis_set_proto` from
  `lisUnset`): every address the listener takes has `a0`'s protocols, so the acceptor's facts are
  about `a0` whatever address a dialer used; dialers dial `a0` itself (`lisProto_addr`).
- `connectRes` holds that `lisProto` (in place of the lab's `nodeIp ip ∗ addrTok (ip:port)`) and
  each peer address's `addrProto a (gryffWireP γ a) (gryffWireQ γ a)`; `listenerOwn` holds Net's
  listener (`isListener`, `netLisOn`, owned `netLis … o`, the `lisProto`); `clientConnIn` holds
  `net.connAt t c true a la ra` (any accepted `a`), dsv-bufio's reader over `recvTokL c true
  (gryffWireP γ a0)` with its peek as an update of the reader resource, the writer contract
  `wire.writerOk ⟨connIface t, connWriteE la ra ed, 4096⟩ (sendTok c true (gryffWireQ γ a0))
  (gryffWireQ γ a0 c)` (what `net.conn_streamWriterOk` gives), `sendTok … []`, the reply bridge,
  `clientConnAt`, `connFresh c true`, `□ protoInvs γ`. The lab's `sharedInvs` is `protoInvs`.
- The reader's protocol fact is under a later (`recvTokL`): the laws are stated of `protoPrefix`
  (`acc_dial`, `acc_peer_ids`, `acc_client_conn`), and the reader-level bridges take it from the
  reader and strip the later under the update: Gryff's wire protocols are **timeless**
  (`gryffWireP_timeless`, …, `protoPrefix_timeless`; `ownReader_protoNow`). `ownReader_sentLb`
  (what a reader returned was written) replaces the lab's `recvTok_sentLb`.
- **The wire protocols allow the empty stream** (`gryffWireP γ a cid W := ⌜W = []⌝ ∨ ∃ full, …`):
  `net.conn_streamWriterOk` asks `ProtoPrefixClosed`, which includes `[]`
  (`gryffWireP_closed`, `gryffWireQ_closed`); readers lose nothing (`protoPrefix` has `[]` anyway).
- `serveClient.wp`, `WaitForClientConnections.wp`, `NewReplicaDurable.wp` moved from `Replica2/Specs`
  to `Replica2/SpecsN.lean` (they need N's proofs; Specs is then below N/Boot and the H layers port
  against it now).
- `strings.Index`: the hypothesis `netN.StringsIndexHyp GF` (`N/StrIndex.lean`, one-byte
  separators, Go's exact result `indexOfByte`; Perennial translates it names only).
- Net's specs reach N through a Prop class `netN.NetConnSpecs GF` (`N/NetSpecs.lean`, like
  `wire.BufioSpecs`), discharged at linking by Net's `wp_proof`s.

**Design (2), the Rpc layer (decided):** the kit's generated codec (rpcgen's format: string type
tags, gob-like zero-field skipping; NOT the lab's encodings, so the lab's `Rpc/Codec*` 2.6k lines
are superseded) as a `CodecSpec` whose transformers are the WPs of the generated
`rpcEncode`/`rpcDecode`/`rpcReceiver` (dsv-craq's `Craq/Codec.lean` pattern), with codec lemmas per
type (`Rpc/Codec.lean`, `Rpc/CodecProof.lean`); one hypothesis class `RpcHttpHyp GF`
(`Rpc/RpcHttpHyps.lean`) for the server side only (`rpcLisP`, `handlerOk`, `muxHas`,
`defaultServer`, `ServeHTTP`, `HandleHTTP`, `Register`, `ServeMux.ServeHTTP`, `http.Serve`); the
codec's per-machine boot resource as a named premise (never `|==> codecFresh`); services accept
error answers as swiftpaxos's `withErr` (to become `srvErrMsg`).

**The client's update is remote's linearization point (decided, `b59df34126`):** `opAU γ i Q`
(`Proto/InvDefs.lean`) is now `|={⊤ ∖ gryffN, ∅}=> ∃ σ, regHalf γ σ ∗ (regHalf γ (casApply σ i).1
={∅, ⊤ ∖ gryffN}=∗ Q σ …)` (the lab's Iris atomic update at `clientN` could abort; the proof never
aborted it). `opAU_fire`, `fire_all`/`fire_all2`/`fire_new` take `E = ⊤ ∖ gryffN`, `replica_step`
and stage 1's `store_update` `E = ⊤` (their only caller, `critical_step_proof`, used `⊤`). The
kit's store `casR γ` (`examples/gryffnet/Kit.lean`: `sysState := regHalf γ`, `Eop := gryffN`,
inputs/outputs boxed `In`/`Out`, `Codec()`'s bytes) has `lin_opAU : lin (casR γ) i Φ ⊢ opAU γ
(toRI i) (fun _ _ o => Φ (fromRO o))` (`applyG_casApply`).

**Kit Go changes (`c4ecc02bb6`, kit tests pass):** (a) `Sys` has a mutex and `Op` runs under it
(`op`): remote's `ServeClient.spec` gives the client's state only through `tok sys` from
`{{ True }} newClient c {{ tok sys }}`, so `tok` is persistent (the lock); remote serves one request
at a time, the lock is never contended (paxos's finding, the gryff form); (b) a client answers at
most `K` operations (`sys.ops`), later ones unknown: the replicas' instance budget (lab D14, 4 units
per client) needs a per-client bound and remote's spec gives none; (c) `EncIn` is 24 bytes (`Op` as
8 bytes): with `byte(x.Op)` it was not injective on every `In` and `Check.spec`'s `codecOk` asks
`DecIn (encIn i) = iv i` for every input.

**Work split this session** (forks of the sixth agent, in this worktree; the agent commits): F1 H1
(28 of 32 + H2/Env committed `8fddf553b8`; Send, Icoord, GCoord, GParti rechecking); F2 X/Bridge,
X/Final, B/Handler, B/Tables, B/BootLem, then H2..H3; F4 the Rpc layer + Server/Deploy (DONE,
`bb34bf947c`); F5 N/ConnErr, N/NetSpecs, N/Serve, N/ClientConn, Replica2/SpecsN; F6 N/WaitPeers,
ConnSlots, Connect, Boot; F7 Shares (Net/remote form) + Server/{Master*, RawServer, RegisterProof,
ServeProof, MasterBoot, SpecsDefs, SpecsReq} + B/{Register, Registry, Rcvr, Init}; F8 the kit's
specs (KitSpecs/KitProof: Codec, Gen, Orch, Client, opMaybe) + Client/*. After them: Replica2/Link,
B/NewReplica, Server/Specs, B/Boot, Server/Boot(Iface), the start (StartInit/Start over remote's
start, as paxos's TopLevelRobustness), Mains, Linked, the statement, the TCB collection.

**Status (session 6, latest):** committed and checking: all H layers (H1..H3), X, B/{Handler,
Tables, BootLem, Rcvr, Register, …}, N (all but SpecsCheck), Replica2/{Specs, SpecsN}, Rpc/*,
Shares, Server/{Deploy, RpcEnv, MasterDefs, SpecsDefs, MasterRegister, MasterServe}, the kit
(`Kit`, `KitSpecs`, `KitProof`: Codec, Gen, Orch, Client, Op as `opMaybe` over `op.spec`),
Client/Defs. In progress: F9 `op.spec` (Client/{Conn, Stream, Op}); F10 Replica2/Link, B/Registry,
B/Init, B/NewReplica; F11 Server/{MasterNew, MasterRun, ServeProof, RegisterProof, MasterBoot,
SpecsReq}. Then: Server/Specs, B/Boot, Server/Boot(Iface), the start (StartInit/Start/Top over
remote's start, paxos's TopLevelRobustness), Mains (eleven commands; replicas through their owned
boots `wp_initialize'_own` + `RpcBootHyp.wp_init_own`), Linked, `gryff_remote_robust`, TCB.
Hypotheses added since: `lib.MathPowHyp` (`Lib/MathHyps.lean`), `RpcEnvHyp` (`Server/RpcEnv.lean`:
net/rpc's and net/http's package variables as their inits set them), `lib.io.ReadFull.specLt`
(a premise; proved by `Lib/ReadFullLtProof.lean`'s `wp_proofLt`, rabia's, linked at the top).
Caveat (F2, F6): `etc/lean-check.py` reported "0 errors" on new files that `lake build` then
rejected; confirm new files with a targeted `lake build`.

**The Rpc layer as built (F4):** `Rpc/Defs` (rpcgen's bytes `encRegArgs`, …; addresses
`masterRpcAddr = 127.0.0.1:7501`, listeners `masterRpcLis = ":7501"`, `replicaRpcLis k =
":850(2+k)"`; `masterSvc δ R := withErr (masterSvc0 δ R)`, `replicaSvc := withErr replicaSvc0`;
`rpcServicesDef` per wildcard listener), `Rpc/Codec` (`gryffCodec`, `CodecLaws`, `RcvLaws`),
`Rpc/CodecProof` (`gryffCodecLaws`, `gryffRcvLaws`, proved), `Rpc/RpcHttpHyps` (`class RpcHttpHyp
GF`, data-carrying as swiftpaxos's: `rpcLisP` (+`_addr`, `_lis`, `_set`), `handlerOk`, `muxHas`,
`defaultServer`(+`_init`), `muxFree` (a path is registered once: Go panics on a second
`HandleHTTP`), `Server_ServeHTTP_spec`, `Server_HandleHTTP_spec`, `HandleHTTP_spec` (both at
`defaultRPCPath`, consuming `muxFree`), `Register_spec`, `ServeMux_ServeHTTP_spec`, `Serve_spec`;
`rpcBootRes` and `class RpcBootHyp GF` (`wp_init_own`: net/rpc's initializer, owned, gives
`codecUnset`, the codec mutex, `invalidRequest ↦□`, `muxFree defaultRPCPath`, once per machine:
Upamanyu's C2)).

**Hypotheses so far (each a premise of the statement, no instance):** `wire.BufioSpecs`,
`wire.BinaryVarintHyps` (+ `errOverflowVar`), `netN.StringsIndexHyp`, `SortSliceHyp`
(`Lib/SortHyps.lean`, sort.Slice on `[]int32` with `<`: Go's result is the unique sorted
permutation), `RpcHttpHyp`, `RpcBootHyp`, the `InitHyp`s (`net.rpc`, `net.http`, `math.rand`), and
the Net/remote spec bundles discharged at linking (`netN.NetConnSpecs`, …).

## Which lab run

Ported: run **`gryff-bump-1`** (dsverify-lab `master` `915f964`, `examples/gryff/`; proof
`21ef7d6` tag `final`, fork `ef17c2d`, verified in 1066 s; `dsv_goal_check : SafeDist (orch ::
clients ++ servers) gryffNetCfg`, axioms Lean's three and porcupine's `CheckOperations.wp_proof`).

## Next

**Done 2026-11-23 (fourth session)**: (3) bufio: the wire layer is ported over dsv-bufio, all of it
checking clean with `etc/lean-check.py -a`: `Wire/Proof/{Lemmas,VarintWp,State,Gryff1,Gryff2,Client,
Epaxos,Genericsmr,Slices,SlicesM}`, `Wire/Specs`, `N/{ArrLen,SliceMarshal}`, `Replica/Base`; dlog's fact
is now `DLOG ↦□ false` (`etc/dsv/gryff.py`'s `finish`, `src/dlog/Base.lean`; gen-init and
`_gryff_boot.py` regenerated). `Wire/Proof/Lemmas.lean` also has lab-shaped wrappers over dsv-bufio's
proofs: `wire.wp_Flush`, `wire.wp_WriteByte` (pre `⌜err = nil⌝ -∗ □ Q …`; post with dsv-bufio's two
extra clauses: a failed writer keeps its state, a byte that fits is not sent), `wire.wp_NewWriter`
(`wr.sz = 4096`, the wrapped writer not a `*bufio.Writer`), `wire.wp_NewReader` (over
`io.readerOk rd.ri (fun _ m => 0 < m) I rd.E`, which `net.conn_readerOk` gives),
`wire.writerOk_prefixClosed` (in the unfolded form `EtcdGrove.bufio.Q_of_prefix` takes). Also done:
`N/Generic` (its `wp_WriteByte_sticky` over `wire.wp_WriteByte`), `N/Marshal`. `lake build` of
`N.Marshal`, `N.ArrLen`, `N.SliceMarshal`, `Replica.Base`, `Wire.Specs`, the PkgTables of
orch/client0/server1-4, the three replica `Boot`s and `ModelProof`: green (2658 jobs). In N files the
bundles must be written `wire.WSt`/`wire.RSt`/`wire.BinaryVarintHyps` (in `netN`, `WSt` is sync's
`LockState.WSt`).

**How to port the rest** (the helper is a scratch script, rewritten each session; its rules are the list in
"What changed against the lab (proof)" plus): `port.py` = copy a lab module, header line "Ported from …",
`GryffProof.` -> `Dsverify.Proof.gryff.`, `Gryff.{GeneratedProof,Code}.` -> `Dsverify.{…}.`; then the
`wire_rw` rewrites; for N-level files also `bufio.ownWriter/writerOk/ownReader/readerOk/wp_Flush/
wp_WriteByte/wp_NewWriter/wp_NewReader` -> `wire.…`, `bufio.prefixClosed` -> `EtcdGrove.io.prefixClosed`,
`bufio.Q_of_prefix` -> `EtcdGrove.bufio.Q_of_prefix`, `variable [GryffNetPkgState GF]` dropped, the
`Slots` import -> `Dsverify.Proof.gryff.src.gryff.Base`. Proofs that unfolded the lab's `ownWriter`/
`writerRep` (e.g. `N/Generic.lean`'s `wp_WriteByte_sticky`) are redone over the wrappers.

**Import tiers (land gate, coordinator 2026-11-23):** `etc/tier-check.py --check` at `90a9b5a2fe`: **8 new
violations**, all `defs->proof` from `Dsverify.Proof.gryff.Wire.Proof.Lemmas` to dsv-bufio's proof files
(`Proof.bufio.{NewReaderOk, NewReaderSize, NewWriter, NewWriterSize, Reader__ReadOk, Writer__Flush,
Writer__Write, Writer__WriteByte}`), for the wrappers and `wp_wire_Write`/`wp_wire_Read*`, which name
`EtcdGrove.bufio.*.wp_proof`. To fix before landing: import `Spec.bufio.*` only and take the specs as
hypotheses (section variables `(wp_Write : EtcdGrove.bufio.Writer.Write.spec)` … or one Prop structure
of the bufio specs threaded through the wire specs), discharged by a `Link`/`*Linked` module with the
`wp_proof`s. The rest of the port obeys the rule so far; new files must see callees through their specs
only (lab-style imports of callees' proofs are violations: Rabia's port had 106).

Remaining, in order (updated session 5; lab modules left: see `port/` scratch or diff the lab tree
against `Dsverify/Proof/gryff/`; not to port: `Slots.lean`, `WS/Placed.lean` (gone by design),
`S/SelfOwn.lean` (the lab's evidence copy, its proofs are in `Replica2/State`)):

Everything portable without a design decision is ported. Two designs block the rest:

1. **The client connection on `Net/` (N/Serve, N/ClientConn, N/ConnLaws, N/StrIndex, N/WaitPeers,
   N/ConnSlots, N/Connect, N/Boot, then Replica2/Specs and everything above it: H1-H3, B/Handler,
   B/Tables, B/BootLem, X/Bridge, X/Final, Replica2/Link).** `N/Serve.lean` is not in the tree (recreate
   it: scratch `port/port.py N/Serve.lean`, then `port/nport.py` and `port/nextok.py`); its `clientConnInB` is the lab's connection vocabulary:
   `net.rpc.connIface conn c true` -> `∃ t la ra, ⌜conn = interface.mkOk (ptr TCPConn) #t⌝ ∗
   net.connAt t cn true a la ra`; `sendTok c true (addrQ γ a) []` / `connFreshG netDistGS c true`
   -> `Net/`'s `sendTok`/`connFresh` (`GooseLang/Ext/Net/Proto.lean`); the reader's peek
   `□ (∀ Y, I (u32Le hs ++ Y) -∗ …)` -> the reader-level update form used by `peerReaderB`
   (`N/SpecsDefs.lean`), to be produced where the reader is made (`N/ClientConn`) from
   `wire.ownReader_proto` (`Client/Bufio.lean`, `net.connReader_proto`: `▷ protoPrefix`, strip
   the later under the update; the protocol `gryffWireP`'s facts are persistent/timeless) and the
   reader as `wire.RSt := {connIface t, connReadE eof la ra ed}` (`net.conn_readerOk`, which takes
   `net.Conn.Read.spec` as an argument: thread it as a section hypothesis or a field of a
   `NetSpecs` class like `wire.BufioSpecs`); the writer `wire.WSt := {connIface t, connWriteE la ra
   ed, 4096}` with `net.conn_streamWriterOk` (`J := sendTok cn s P`, `Q := P cn`); `errWf`/`errAny`
   on read errors -> `rdErr` (`io.EOF` test: `net.eof_ptrTyped`, logging: `logArg_err` needs
   `models_lab.errAny` of a `connReadE` error; `OpError.Error` is in `Net/`); `sharedInvs` ->
   `protoInvs` where only those invariants are used; `c.RemoteAddr().String()` -> state it at the
   call shape goose produces (the lab's was a `*TCPConn` method; `Lib/NetAddr.lean` has
   `wp_TCPAddr_String`; `net.Conn.RemoteAddr.spec` returns `ra`, `connAt` holds `netAddr ra`);
   `net.model.Assumptions` -> `net.Assumptions`/`net.FieldAssumptions`. `strings.Index`
   (`N/StrIndex`) is names-only in Perennial: a hypothesis with Go's precondition-free spec.
2. **Rpc against `Net/`'s rpc** (`Rpc/{Defs,CodecLow,CodecEncode,CodecDecode,CodecProof,Slot}`,
   then `Server/*`, `Shares`, `Client/*`, `B/{Register,Registry,Rcvr,Init,Boot,NewReplica}`):
   merge `origin/models-rpc-http` (`1a4d9546c9`; DialHTTP(Path) proved over
   `http.ReadResponse.spec`) and use its client specs; the server side (`ServeHTTP`, `HandleHTTP`,
   `http.Serve`, mux, wildcard `rpcLisP`) as ONE hypothesis class shaped like dsv-swiftpaxos's
   `lib/RpcHttpHyps.lean` (read it on `origin/dsv-swiftpaxos`); `Client.Call` errors with
   `errMsg`, `errOk` only for `srvErrMsg`, `codecFresh`/`srvEnv` from a per-machine boot resource
   (next to the replicas' prophecy boot), all visible premises. The lab's `RpcCodec` (`enc`,
   `dec`, `call`, `methods`) is `Net/`'s `CodecSpec` (`enc`, `dec`, `rcv`) plus the method specs;
   the addresses are the kit's (`127.0.0.1:7501`, replicas' net/rpc at `127.0.0.1:850x`), not the
   lab's `10.77.0.x` (`ipOf`, `portOf`, `masterRpcAddr` in `Rpc/Defs`).
3. Then the client on remote, Codec()/Gen, Start/Shares, Mains, Linked (instances of the hypothesis
   classes are NOT allowed: `wire.BufioSpecs` is discharged in `Linked` by `haveI := ⟨…wp_proof…⟩`
   or by stating the top theorem over it and applying it to the proofs), `gryff_remote_robust` with
   every premise visible (`InitHyp`s, `BinaryVarintHyps`, the rpc-http class, `strings.Index`;
   `etc/theorem-loc.py`), `etc/tcb-collections/dsv-gryff.txt`.

### Older plan (sessions 1-3), still valid where not superseded above


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

1. **Package initializers**: done (above). The replicas' boot (`wp_initialize'_own`) is to be
   used by the deployment's proof for `cmd/server{2,3,4}` in place of the generated
   `wp_initialize'`, handing `gryffGlobals ∗ bootProph` to `main` (the lab's `node_proph_intro`,
   `GryffProof/Server/SpecsDefs.lean`, turns `bootProph` into `nodeProph`).
2. **The kit's model, Go-level**: done (above). Still to write: the codec's spec (`Codec()`,
   `codecOk` of remote's `RBase` for the register: `encIn` 17 bytes, `encOut` 9 bytes, both
   injective) and `Gen`'s, with the remote store `RBase` (`woR`'s analogue: `B := casB`,
   `sysState` the Gryff invariant's register half, `Eop`, `iv := inV`, `ov`, `unk := outV
   ⟨true, 0⟩`).
3. **bufio**: the revised `origin/dsv-bufio` (now `361ca5c7b7`: `io.writerOk` ->
   `io.streamWriterOk`, `io.wp_writer_Write` -> `io.wp_streamWriter_Write`, `net.conn_writerOk` ->
   `net.conn_streamWriterOk`, `Proof/io/StreamWriterOk.lean`; use the new names) is
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
4. **net/rpc** (`models-rpc-server` `2a6b4e5d12` merged: `Client.Call`/`Go`/`send` take
   `□ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep reply (Θ rep))`, decoding owed only for the method's
   answers; success post `⌜err = nil⌝ ∗ Rargs ∗ ∃ rep, Θ rep true`; no type-tag workaround is
   to be used; the server's `methodOk` `NewArg` gives `argDec C argv D Sm Θ := codecSet C ∗ □ (D -∗
   ∀ args Φ, Sm args Φ -∗ Sm args Φ ∗ C.dec args argv (Θ args))` (`36728bd8ed`), and
   `ReadRequestBody` takes a guard; target these): `Rpc/Defs` -> `Net/`'s vocabulary: the lab's `RpcCodec` (`enc`, `dec`, `call`,
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
