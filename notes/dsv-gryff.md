# dsv-gryff: dsverify-lab's gryff kit on the net extension (phase 6)

> **STATE (2026-11-24, session 13, on lean b64d2397f8, Perennial d9c8c1d97): merged `origin/lean`
> (the real-`fmt` pin bump and after). Statement unchanged: `Robust [] (system σ) g (2 ^ 31) (2 ^ 63)`. The
> proved theorem is the plain `gryff_remote_robust : gryff_remote_robust.spec`: Net's `DialHTTP.wp`
> takes no strings hypotheses since lean's 57d66cdcee (Perennial's `strings.Cut`/`TrimLeft` proofs);
> `StringsPending`, `stringsPending.spec` and `gryff_remote_robust_of_strings` are gone. `#print
> axioms`: Lean's three. Non-vacuity open ("Non-vacuity: open"). See "Session 13" below.
> 2026-11-24 (dsv-gryff-strindex, Perennial fce59af75): the premise `netN.StringsIndexHyp` is gone,
> discharged in the proof by `stringsIndexHyp_holds` (`StrIndexHolds.lean`).**

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
| Go | `examples/dsverify/gryff/` (module `gryff`, the fork's path): the fork's packages the kit reaches (`src/{fastrpc,dlog,state,stats,clientproto,genericsmrproto,masterproto,epaxosproto,gryffproto,bitvec,bloomfilter,genericsmr,gryffcommon,gryff,masterlib,serverlib}`, non-test files only, unchanged, the fork's prophecy code included) and the kit `examples/gryffnet` with its eleven commands `cmd/{orch,client0..5,server1..4}` |
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
- The fork carries its prophecy code in the Go (the trace prophecy, `src/gryff/proph.go`, marked
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

## DECIDED (user, 2026-11-23): the prophecy code stays in the fork (option 3)

The fork's Go is kept exactly as the lab's, **prophecy code included** (`src/gryff/proph.go`,
the `Replica.proph` field, the `resolve<Event>` calls), a **recorded deviation** from this
repository's rule that prophecies are patches (`etc/proph-patches/`, `notes/decisions.md`
"Prophecies as patches of the Go code"). The user chose option (3) on 2026-11-23; nothing else
changes. **The reason, for a reviewer:** the code is the lab's verified fork as is; prophcheck
(added 2026-11-03, after the lab's Gryff proof was built) admits only a local `NewProph` resolved
in one function, while Gryff's trace prophecy is package-wide (`traceProph`, created by the
package's `init()`), resolved by 28 helpers through a struct field.

## The trace prophecy as a prophecy patch: blocked by prophcheck's grammar

Coordinator's decision (2026-11-23): move the fork's prophecy code into
`etc/proph-patches/dsv-gryff/*.patch` (CLAUDE.md, `etc/proph-patches/README.md`,
`notes/decisions.md` "Prophecies as patches of the Go code"), checked by `etc/prophcheck`, so that
`examples/dsverify/gryff` is the lab's fork minus its prophecy code. **It cannot be done as
prophcheck stands.** The prophecy code (lines marked `(ghost code`, the lab fork's marker; checked 2026-11-23):
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
fork still carries the prophecy code):
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
3. Keep the prophecy code in the fork (as dsv-paxos kept its fork's), recorded as a deviation.

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

## Session 7 (2026-11-23, seventh agent): review lessons applied, boots, bridge

**Review of dsv-epaxos (#24) applied here:**
- `RpcHttpHyp.defaultServer_init` (`isPkgInit net.rpc ⊢ ∃ γ, defaultServer γ`, a server out of
  `True`) is **gone**; and so is `RpcEnvHyp` (`Server/RpcEnv.lean`: `rpc_env`/`http_env` derived
  net/rpc's and net/http's package variables from `isPkgInit`, also `True`: no true instance).
  They are boot resources now: `RpcBootHyp` (`Rpc/RpcHttpHyps.lean`) has two fields,
  `wp_init_own` (net/rpc's initializer from `ownInitializing (gNoPkg net/rpc g)` leaves
  `rpcInitRes` = `rpcBootRes` ∗ `∃ γs, defaultServer γs` ∗ `cliEnv` ∗ `connected ↦□`) and
  `wp_http_own` (net/http's leaves `httpInitRes` = `muxFree DefaultRPCPath` ∗ `httpEnv`);
  `serverBoot := httpInitRes ∗ rpcInitRes`. (The old single field asked net/http not to be
  initialized before net/rpc's initializer, which the programs violate: `serverlib` imports net/http
  first.) `Server.spec` takes `serverBoot`.
- `RpcHttpAddr GF` (global: `rpcLisP` + `_addr/_lis/_ok/_set`) is split out of `RpcHttpHyp`
  (per heap, `[RA : RpcHttpAddr GF]`), as dsv-epaxos: the start sets the listeners before any
  heap exists, and every machine must see the same `rpcLisP`. Shares' `netShare`/`clientNodeShare`/
  `serverShare` are global-level. The statement's premises: `RA : ∀ G π, RpcHttpAddr`,
  `H : ∀ G L π, RpcHttpHyp`, `∀ G L π, RpcBootHyp`.
- httpW: not needed here: `RpcWorld` has `hs`/`hsAns` fields (models-rpc-http merged), the start
  builds `{ SS, reg, hs := connectReq …, hsAns := connectAns }` and `rpcLisP_set`'s premise is
  discharged from the world itself (`worldOk`).
- DialHTTP(Path): Net's `DialHTTP.spec` (merged), used as is.

**Duplicate declarations (coordinator's lesson, 2026-11-23):** checked. No gryff file declares a
spec of a library function in a library namespace: every `.spec`/`.specLt` is in
`Perennial.gryff.*` or `gryff.examples.gryffnet` (`lib.io.ReadFull.specLt` is
`Perennial.gryff.lib.…`). One file declared in the shared `Perennial` namespace:
`Server/LogErr.lean` (`Perennial.logArg`, `Perennial.log.wp_Printf_logArg`, …; craq has its own
`logArg` in its namespace): moved to `Perennial.gryff`. `Lab/*.lean` declare in
`Perennial.dsverify_lab.harness` (the lab's names: `Linearizable`, `RegInput`, `clientN`, …): no
other branch uses that namespace today; rename before landing if a sibling adopts it.

**Owned boots (item 3, done in the generator):** `etc/dsv/_gryff_boot.py` writes
`cmd/server{1,2,3,4}/Boot.lean`: the program's initialization from `ownGoState ∅` keeping
`gryffGlobals ∗ bootProph ∗ serverBoot`. Tables: `gEx S g` (`g`, `False` on `S`;
`Boot/Defs.lean`), `noPkgs ⊂ noPkgsS2 (+serverlib) ⊂ noPkgsS1 (+net/rpc) ⊂ noPkgsS0
(+net/http)`; the chain: command and gryffnet from `gEx noPkgsS0`, gryffnet's imports before
serverlib at `S0`, `wp_serverlib_own` (net/http owned `S0→S1`, fmt/net/time/log at `S1`, net/rpc
owned `S1→S2`, masterproto at `S2`, ends at `gNo`), then `gNo` until `wp_gryff_own`, then `g`.
The generator asserts the import order it relies on. The master (server1) runs the same boot
(it also initializes gryff; its `gryffGlobals ∗ bootProph` are dropped).

**`wire.BinaryVarintHyps` vs Perennial #689 (`binary-varint`, 99560b12c; coordinator):** kept as
a premise until that lands and reaches the pin. The switch is mechanical: `putUvarint`/`putVarint`
are `encoding.binary.PutUvarint.spec`/`PutVarint.spec` (`buf ↦* xs` ↔ this class's
`typedPointsto p (array.mk n vs)` of a full slice `slice.mk p n n`; `Wire/Enc.lean`'s `varintEnc x := uvarintEnc (zigzag x)`, as Perennial's; the class's extra
`0 ≤ x` premise drops); `readUvarint`/
`readVarint` are `ReadUvarint.spec`/`ReadVarint.spec` at `ri` the `*bufio.Reader`, `S :=
ownReader br rd I` and `io.byteReaderOk` from dsv-bufio's `Reader.ReadByte.spec` (the error cases
`uvarintRes` → this class's `rdErr`, overflow included via `errOverflow_of_init`, which replaces
`errOverflowVar`); `Wire/Enc.lean`'s `uvarintEnc`, `zigzag` and `Wire/Proof/Varint.lean`'s `uvarintDec` are
textually Perennial's (`Varint.lean` was ported from them; checked), so they are replaced by Perennial's names. Not
done now: our Perennial pin has neither the definitions nor `io.byteReaderOk`.

**Link files (coordinator's lesson):** only the kit's top-level `Link.lean` (namespace
`Perennial.EtcdGrove.dsvgryff`) may be named `Link.lean`: `Replica2/Link.lean` and `H2a/Link.lean`
are now `Results.lean` (linking tier); `proof_roots.namespace()` prints `Perennial.EtcdGrove.`.

**Bridge (item 2, done):** `examples/gryffnet/Bridge.lean` = dsv-epaxos's, verbatim
(`robust_of_distProtoLisRB(T)`).

## Session 8 (2026-11-23, landing prep): lean merged, tiers, duplicates

**State: head after this section's commit; `gryff_remote_robust` still closed on Lean's three axioms
(`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`), checked after every change below.**

- **lean merged** (`d1c432a3ca`, Perennial `70706ce5e`; `.lake/package-overrides.json` points at
  `/shared/perennial-70706ce5e`, `PERENNIAL_DIR` likewise). `gen-init` and `_gryff_boot.py` rerun
  (PkgTables gained `internal/bytealg`, `unicode/utf8` under `strings`). The three shared hypothesis
  inits (`Dsverify/Proof/{net/rpc,net/http,math/rand}/Init.lean`) are lean's (dsv-epaxos's,
  dsv-rabia's); gryff's own `Dsverify/Proof/{net/rpc,net/http,math/rand}/Base.lean` are deleted
  (they declared the same instance names: "environment already contains"); `Rpc/RpcHttpHyps.lean`
  imports the `Init`s, `Lib/RandHyps.lean` the main tree's `Proof/math/rand/Base`. math/rand's
  `Init` constrains `sync`: `etc/dsv/gryff.py`'s `HYP_IMPORTS = {'net.rpc': 'none', 'net.http':
  'none', 'math.rand': 'all'}`, over `dsv-hyp-imports` (dependency 2 above).
- **Bridge:** `examples/gryffnet/Bridge.lean` (the verbatim copy) deleted; `TopLevelRobustness` uses
  lean's `github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.robust_of_distProtoLisRBT`.
- **dsv-protolaws:** `N/ConnLaws.lean`'s `recvTokL_sentLb`, `sentLb_le`, `sentLb_comparable` deleted;
  their uses (`ConnLaws`, `Client/Stream`, `N/WaitPeers`) take `Net.recvTokL_sentLb`,
  `Net.sentLb_le`, `Net.sentLb_agree`.
- **Duplicates:** the closure scan (dups.py's logic) found one: `Perennial.ownSlice_elems`, in
  `N/SliceElems.lean` and epaxos's `replica/SliceElems.lean` (different lemmas): gryff's file is now
  in namespace `Perennial.gryff`. A scratch module importing rabia's, epaxos's and gryff's
  `TopLevelRobustness` together compiles (`lake env lean`; no "environment already contains").
  `Lab/*.lean`'s namespace `Perennial.dsverify_lab.harness`: no other kit (dsv-swiftpaxos,
  dsv-quepaxa, dsv-craq, dsv-vr, lean) declares in it (outside `old/`).
- **Tiers: `etc/tier-check.py --check` passes, no baseline or tier-linking entry** (20 new
  violations fixed, as dsv-epaxos's `Interface/LibDeps.lean`):
  * `H1/PartiSpecs.lean` (defs): the participant's six methods' triples as `GryffParticipant.<M>.spec`
    and the class `GryffPartiDeps`; `H1/CoordSpecs.lean` (defs): `GryffCoordinator.ShortCircuit.specInt`
    (`wp_int`'s triple) in `GryffSCDeps`, the seven coordinator methods' `.spec`s in `GryffCoordDeps`.
    The callers take them as instance arguments: `CoordW1`/`CoordW2` (`GryffSCDeps`), `GCoord`
    (`GryffCoordDeps`, `GryffPartiDeps`), `GParti`, and, per theorem (`variable [...] in`),
    `Icoord.Replica_icoordOk_proof`, `Send.wp_Replica_SendRead1`, `H2/Base.wp_Replica_GetStoreMetadata`,
    `H2/PreAccept.handlePreAccept_wp'`, `H2a/Results.handlePreAccept_wp_link`,
    `H2b/Phase1.startPhase1_wp`, `H2b/Propose.{HandleRMW_wp', handlePropose_wp}`,
    `H2c2/ExecOverwrite.executeOverwrite_spec`, `H2c2/PreAcceptReply.{handlePreAcceptReply_wp',
    handlePreAcceptReply_spec}`, `H3/PrepareReply.{handlePrepareReply_wp', _wp_frozen}`.
    `Replica2/Results.lean` closes the three (`gryffPartiDeps_holds`, `gryffSCDeps_holds`,
    `gryffCoordDeps_holds`, local instances of its `specs` section). No `instance` of them exists.
  * The helpers other modules used are apart from the method proofs: `H1/CoordStartDefs`,
    `H1/CoordSCDefs`, `H1/CoordW2Defs` (everything before the proofs, verbatim); `HEnv`, `Iparti`,
    `CoordRead1`, `CoordWrite`, `CoordW1` import those.
  * `examples/gryffnet/ModelDefs.lean`: `ModelProof`'s definitions `Kit`/`KitProof` use (`inV`,
    `outV`, `casDec`, `casS0`, `cfgOk`, `cfgsOk`, `casRep`, `casS`, `Model.spec`, and the helper
    `wp_isWrite`).
  * `B/NewReplica.lean` no longer imports `Replica2/Results`: `NewReplica_core` takes
    `(wp_run : Replica.run.spec)` (`run.wp`'s triple, defined there) and uses
    `X.executeCommands_wp`; `KitServer` threads `wp_run`; `Link.lean` passes
    `replica2.run.wp lib.io.ReadFull.wp_proofLt`.
- **Checks** (this session): `proof_roots.namespace()` = `Perennial.EtcdGrove.`; `gen-init --check`,
  `_gryff_boot.py --check`, `copy-part --check`, `tier-check --check` pass; `errorf-wrap`'s
  `init_errors()` = `[]`; `goose --check` (all projects): up to date (69 translations); `theorem-loc
  --no-go --list-tcb gryff_remote_robust`: TCB 689 lines, all premises (`tcb_axioms 0`), the three
  `InitHyp`s counted. `lake build` of the proof's `TopLevelRobustness`: builds.

## Session 9 (2026-11-23, pre-adaptation to models-rpc-http)

Goal: the branch lands right after `models-rpc-http`, with only a final merge and rebuild.
- **Merged** `origin/lean` `76c00a8d81` (Perennial `160fcf12a`; remote-serveclient, dsv-inithyp-fix,
  dsv-hyp-imports, swiftpaxos, quepaxa) and `origin/models-rpc-http` `fda1e58c0a`, both without
  conflicts. `.lake/package-overrides.json` and `PERENNIAL_DIR` point at `/shared/perennial-160fcf12a`.
  `etc/gen-init.py` equals lean's. `etc/goose.py` differs from lean's by exactly models-rpc-http's
  hunk (`mime/multipart`, `net/http/internal/ascii` in project models-net).
- **Init fix:** `etc/dsv/gryff.py` has no `HYP_IMPORTS` (the default `'all'`; `'none'` for net/rpc and
  net/http was unsound). PkgTables and `cmd/server*/Boot.lean` were regenerated (gen-init twice,
  `_gryff_boot.py`). Because models-rpc-http's net/http imports `mime/multipart`,
  `net/http/internal/ascii`, `slices` and `log`, the shared `Dsverify/Proof/net/http/Init.lean` now
  imports their facts: new `True` facts `Dsverify/Proof/{mime/multipart,net/http/internal/ascii}/Base.lean`
  (the dsv-inithyp-fix pattern), plus Perennial's `slices`/`log` `Base`. epaxos's and swiftpaxos's
  PkgTables were regenerated the same way. **models-rpc-http needs the same files when it merges
  lean** (or it takes them from here). `RpcBootHyp` is unchanged: its tables before (`gNoPkg q g`) and
  after (`g`) agree beyond `q`, and its `GetIsPkgInitProp q g` premise is the shared Init's condition
  over the whole closure (docstring added; the swiftpaxos `RpcFirstInit` property).
- **Remote's landed API** (remote-adapt.md): `mapCtx_alloc ⊤ clientAddrs 12`, where 12 =
  `K · readTries` = 4·3, so `budUnits a 12` per client, threaded through `Orch.spec`/`wp_main`/the
  start/the system's node 0. `wp_Check … 12 (by decide)`. `addrs_set_proto` takes
  `fun a => reqP … a`. `opMaybe`'s third component is dropped. The newClient premise is a plain WP.
- **models-rpc-http's bufio:** `NewWriterSize.wp_proof` now takes `wp_proofRep`, as epaxos/rabia/
  quepaxa use it on lean. Fixed in gryff's `Link.lean` and in swiftpaxos's `lib/LibDepsLinked.lean`
  (a proof, not its statement; swiftpaxos landed after models-rpc-http forked, so models-rpc-http must
  make the same fix when it merges lean).
- **Statement changes** (`gryff_remote_robust.spec`): the premise
  `∀ G L π, net.rpc.DialHTTP.spec` is **dropped**, now discharged by Net's `net.rpc.DialHTTP.wp`
  (models-rpc-http, `Net/Proof/net/rpc/Results.lean`) in `Link.wp_Server`. Nothing else changed in the
  statement's text. `MathPowHyp`'s field is now the main tree's `EtcdGrove.math.Pow.spec` (the old
  field had precondition `True`; it now also needs `isPkgInit math`, so the premise is weaker).
  `RandSeedHyp`'s field is the shared `math.rand.Seed.spec` (the same triple). No landed kit's
  statement changed (Upamanyu's rule #8).
- **One canonical spec per function:** dups.py over all Dsverify roots: no duplicate names (only
  parse noise). math/rand: gryff calls only `Seed`; the shared `Dsverify/Proof/math/rand/Spec.lean`
  now has `math.rand.Seed.spec` (rabia's `math.rand.Hyps` is unchanged; quepaxa's
  `Perennial.raxos.hyp.math.rand.{Seed,Intn}.spec` are textual duplicates of the shared ones, left
  for quepaxa). math.Pow: the main tree's spec (its axiom is not used). os/signal, gods treemap,
  gob: gryff uses none of them. log.Println: gryff proves `Perennial.gryff.log.wp_Println_logArg`
  from Perennial's body (error arguments, which Net's `log.Println.spec`'s `fmt.ArgsWf` excludes); it
  is a lemma, not a premise. bufio: `wire.BufioSpecs` fields are the landed `EtcdGrove.bufio.*` specs.
  sort.Slice: the main tree's `EtcdGrove.sort.Slice.spec` is for `[]int64`, permutation only; gryff's
  `SortSliceHyp` is `[]int32`, sorted, so it stays a separate hypothesis (a generalized main-tree spec
  would retire it). strings.Index, binary varints: no other spec exists (swiftpaxos copies varint
  code into its fork).
- **Statement header:** the step bound (`2^31-1`: net/rpc's int32 WaitGroup, prefixes only) and the
  deployment (no narrowing beyond `DistDeploy`; the kit's `K` = 4 cap and `Sys` lock).

- **Landed kits, proofs only** (needed for the five landed statements to build on this merge; no
  statement text changed): swiftpaxos `examples/swiftnet/Start.lean` builds `RpcWorld` by field
  names (models-rpc-http added `hs`/`hsAns`; `httpW` sets them, as before), its `BootTable.lean` was
  regenerated (`etc/dsv/_swiftpaxos_boot.py`, net/http's larger closure), and `lib/LibDepsLinked.lean`
  links `NewWriterSize` over `wp_proofRep`. models-rpc-http meets all three when it merges lean.
- **Checks (head after this section):** on fk-lean1 (commit `bb8e39f9c3`, plus the scratch
  `Dsverify/Scratch/Axioms.lean`, since deleted): the six `TopLevelRobustness` (gryff, swiftnet,
  rabianet, epaxosnet, quepaxanet, paxosnet) and the scratch module importing all six together
  build (5397 jobs); `#print axioms` of each of the six = `[propext, Classical.choice, Quot.sound]`.
  Here: `tier-check --check` ok (227 known, no new); `gen-init --check` (271 up to date);
  `_gryff_boot.py --check`, `_swiftpaxos_boot.py --check` clean; `goose --check` for dsv-gryff and
  models-net up to date; `proof_roots.namespace()` = `Perennial.EtcdGrove.`; errorf-wrap
  `init_errors()` = `[]` (the full check needs a built tree); `git diff origin/lean -- etc/goose.py
  etc/gen-init.py`: goose.py only, models-rpc-http's hunk. `theorem-loc --no-go --list-tcb
  gryff_remote_robust`: TCB 617 lines, all premises (`tcb_axioms 0`; it was 689 before
  `DialHTTP.spec` dropped); the three `InitHyp`s are counted.
- **After models-rpc-http lands:** merge `origin/lean`. If models-rpc-http adopted the files above
  (net/http Init imports, the two Base files, swiftpaxos's three proof fixes), the merge is
  trivial; otherwise keep this branch's versions. Then gen-init (twice) + `_gryff_boot.py` +
  `_swiftpaxos_boot.py`, an fk-lean1 build of the six with `#print axioms`, `etc/tcb-report.py
  --collection etc/tcb-collections/dsv-gryff.txt --check` (needs a full build) and the land gates.

## Session 10 (2026-11-23): the trace prophecy as a prophecy patch (the widened rule)

Upamanyu approved the widened prophecy-patch rule (#24, option A; branch `proph-patch-rule`,
`notes/proph-patch-rule.md` for the exact checks). This branch merges `proph-patch-rule` (and so
`origin/lean` 29f93a3c2c, Perennial `ccfeb3895`) and moves the fork's prophecy code into
`etc/proph-patches/dsv-gryff/01-trace-prophecy.patch` (the patch directory is named after the
goose project, `dsv-gryff`). This replaces the section "The trace prophecy as a prophecy patch:
blocked by prophcheck's grammar" above and the recorded deviation (option 3 there).
- **The fork** (`examples/dsverify/gryff`) is the lab's minus the prophecy code: `src/gryff/proph.go`
  deleted; `tupaq.go` loses the `primitive` import, the `Replica.proph` field, `proph :=
  traceProph` and the literal's element; `epaxosrmwhandler.go` (23) and `epaxos-exec.go` (1) lose
  the 24 `resolve*` calls. `go build ./src/...` of the stripped fork is green.
- **The patch** (459 lines, 284 added; `src/gryff/epaxosrmwhandler.go` and `epaxos-exec.go`):
  the `primitive` import, `var traceProph primitive.ProphId` with its prophecy-only initializer
  `func init() { p := primitive.NewProph(); traceProph = p }` (Goose refuses `var traceProph =
  primitive.NewProph()`: its copy rule), the 29 helpers of `proph.go` as `*Replica` methods at
  the end of `epaxosrmwhandler.go` (5 for fields, 24 for events), resolving `traceProph` (no
  `Replica.proph` field: it was a copy of `traceProph`, which the rule's "initialized only by
  `NewProph`" does not admit), the 24 `ev*` constants inlined (`ResolveU64(1) // evRead1`; the
  rule admits no constants), and the 24 calls unchanged. `etc/proph_patch.py --project
  dsv-gryff`: checks and applies.
- **Translation**: `Code/gryff/src/gryff.lean` (the helpers read `GlobalVarAddr traceProph`; no
  `ev*` definitions; `Replica` without `proph`; `primitive` imported earlier), its
  GeneratedProof chunk2, the gryff `PkgTable`s, `src/gryff/Init.lean` (gen-init) and the four
  server `Boot.lean`s (`_gryff_boot.py`) regenerated.
- **Proofs**: every `r.[src.gryff.Replica, go!"proph"] ↦□ p` became `globalAddr
  src.gryff.traceProph ↦□ p` (B/Resolve, B/LockBoot, Replica2/{Specs,State,Results}, X/{Laws,
  Final}); `wp_resolveU64` loses its replica argument; `B/NewReplica` no longer persists the
  field (the global's `↦□` comes from `replicaReady`, as before). `gryff_remote_robust`'s
  statement is unchanged (`Dsverify/Spec/gryff/...` identical to `de12d55ab0`).
- **Lean merge fallout** (models-rpc-http's Net proof, not gryff's): `Net/Proof/net/http/
  modelReadMIMEHeader.lean`'s lent `[]byte` is now `fmt.Lent.bytes` (Perennial ccfeb3895's fmt).
- **Built on fk-lean1** (a scratch module importing the seven, dropped after): `#print axioms`
  of `gryff_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`,
  `epaxos_remote_robust`, `quepaxa_remote_robust`, `paxos_remote_robust` and the remote
  `counter_remote_robust`: `[propext, Classical.choice, Quot.sound]` each (5471 jobs, exit 0).
- Checks: tier-check `--check` ok (no new violation); gen-init, `_gryff_boot.py`, goose and
  copy-part `--check` clean (PERENNIAL_DIR=/shared/perennial-ccfeb3895); `proof_roots.namespace()`
  = `Perennial.EtcdGrove.`; dups.py: the same 4 false positives as lean; `git diff origin/lean --
  etc/goose.py etc/gen-init.py`: only models-rpc-http's net/http lines in goose.py (mime/multipart,
  net/http/internal/ascii), as before.

## Session 11/12 (2026-11-24): lean, steps63, frames, varints, strings, non-vacuity

- **Session 11** (the ninth agent, unpushed f6a43c41d0..a5f91c8e46): merged `origin/lean` 5c7f7d2e59
  and `origin/dsv-steps63`; adapted to lean's net/rpc (`Client.Call`'s frame bound, Net's
  `defaultServer`/`Register`), the `*OpError` fields' points-to for `errAny`; `RpcHttpAddr`
  discharged (`netRpcHttpAddr`, Net's `rpcLisP`); a `DialHTTP_spec` field in `RpcHttpHyp`.
- **Session 12** (2026-11-24, from a5f91c8e46): merged `origin/lean` 37bfea9484 (no conflict; the
  generated files check clean: `gen-init --check`, `kitgen --check`, `_gryff_boot.py --check`,
  `goose.py --check --project dsv-gryff`).
  * **`BinaryVarintHyps` discharged**: `Wire/Proof/VarintHolds.lean`'s `binaryVarintHyps_holds`
    (a `*bufio.Reader` is an `io.ByteReader` over dsv-bufio's `ownReader`, `bufReader_byteReaderOk`;
    Perennial's `ReadUvarint`/`ReadVarint`/`PutUvarint`/`PutVarint` proofs, perennial#689;
    `errOverflow_of_init`), `Link.lean`'s `binaryVarintHyps`; the statement loses the premise.
    `#print axioms binaryVarintHyps_holds`: Lean's three.
  * **Strings**: `RpcHttpHyp.DialHTTP_spec` removed (it was a new premise); as craq: `Link.lean`'s
    `StringsPending` (Perennial's `strings.Cut.spec`/`TrimLeft.spec`) feeds `wp_Server`'s
    `net.rpc.DialHTTP.wp sp.cut sp.trimLeft`; the proved theorem is
    `gryff_remote_robust_of_strings (hs : stringsPending.spec) : gryff_remote_robust.spec`. After
    the pin bump: `gryff_remote_robust := gryff_remote_robust_of_strings (fun => ⟨…⟩)` and
    `StringsPending` goes.
  * **Non-vacuity, no new axioms**: the session-11 instances over local axioms (NonVacuityLinked's
    and the twelve `Dsverify/Proof/**/InitInstancesLinked.lean` walks of net/rpc's and net/http's
    closure, which rest on local axioms for the names-only initializers) are removed (in history,
    a5f91c8e46). Kept: `math.rand.InitHyp` (the walk, no axiom) and `lib.MathPowHyp` (the main
    tree's existing `math.Pow` axiom). **Remaining** (no axiom-free instance at b3f2fc485):
    `net.rpc.InitHyp`, `net.http.InitHyp`, `StringsIndexHyp`, `SortSliceHyp`, `RandSeedHyp`
    (`strings.Index`, `sort.Slice`, `math/rand.Seed` names only), `RpcHttpHyp` (net/http's server,
    `HandleHTTP`), `RpcBootHyp`.
  * `notes/perennial-changes.md`: the merge's duplicated models-rpc-http sections dropped (lean's).

## Session 13 (2026-11-24): onto the real-`fmt` pin

- Merged `origin/lean` af4fd74b00 (Perennial 52d62e83c), then b64d2397f8 (Perennial d9c8c1d97; no
  conflict either time); the eleven generated
  `cmd/*/PkgTable.lean` regenerated (`etc/gen-init.py`: the pin's new packages in the closures);
  `kitgen --check`, the Links and `goose.py --check` clean.
- Strings: at 52d62e83c a bridge `Proof/strings/FromPerennial.lean` turned Perennial's
  `strings.Cut`/`TrimLeft` proofs into the specs Net's `DialHTTP.wp` took as hypotheses; lean's
  57d66cdcee then discharged them in Net itself (deleting `Spec/strings/{Cut,TrimLeft}.lean`), so
  the bridge went and `Link.lean`'s `wp_Server` passes `net.rpc.DialHTTP.wp` as is. `StringsPending`
  and `stringsPending.spec` deleted; `gryff_remote_robust_of_strings` became `gryff_remote_robust`.
  The statement is unchanged (only its docstring's mention of the old theorem).
- **`fmt.Sprintf` onto the real `fmt`**: lean's pin bump removed `fmt.wp_Sprintf_argsWf` (the
  trusted model's spec); gryff's six call sites (`Server/MasterRegister` `%s:%d`, `MasterRun`
  `%s:%d`, `MasterNew` x2 and `ServeProof` x2 `:%d`, `N/Listener`/`N/Serve` the stats keys
  `server_rpc_%d_chan_length`/`client_rpc_%d_chan_length`) now use `EtcdGrove.fmt.wp_Sprintf_pure`
  over Perennial's `fmt.wp_Sprintf` (`Proof/fmt/SprintfPure.lean`, as lean's own callers), their
  output lemmas restated over `fmt.render` (`render_addr`, `sprintf_rpcAddr`,
  `sprintf_colon_port`); the `SprintfOut`/`ArgsWf` helpers (`sprintf_addr`, `regArgs_argsWf`,
  `rpcAddrArgs_argsWf`, `intArg_int_uniq`) deleted. `log.Printf`'s `fmt.ArgsWf` premise
  (`LogErr.lean`) is unchanged.
- The four server `cmd/*/Boot.lean` regenerated (`etc/dsv/_gryff_boot.py`, after gen-init: the
  PkgTables' new packages).
- Not done: `StringsIndexHyp` stays a premise (Perennial 52d62e83c has no `strings.Index` proof;
  dropped since, "Non-vacuity: open").

## Non-vacuity: open (decision 2026-11-24)

**Decision** (kaashoek, 2026-11-24): dsv-gryff lands **without** non-vacuity instances for most of
its premise classes; the gap is recorded here and real instances are a follow-up. Why: the
instances session 11 wrote were built from local axioms that restate the premise they instantiate
(an axiom `RpcBootHyp`-shaped, or names-only initializers assumed to run), so they showed nothing
about the premises' consistency and only grew the trust base.

**Premise classes of `gryff_remote_robust.spec`** (`Dsverify/Spec/gryff/examples/gryffnet/
TopLevelRobustness.lean`, checked against the statement at fff2eff310):

- **With an instance** (`Dsverify/Proof/gryff/examples/gryffnet/NonVacuityLinked.lean`,
  `nonvacuous_premises`, imported by nothing): `math.rand.InitHyp` (the main tree's walk over
  Perennial's `sync`/`sync/atomic` initializers, no axiom) and `lib.MathPowHyp` (the main tree's
  existing axiom `EtcdGrove.math.Pow.wp_proof`, not a new one).
- **No axiom-free instance** (at Perennial b3f2fc485): `net.rpc.InitHyp`, `net.http.InitHyp`
  (their closure reaches names-only initializers),
  `replica2.SortSliceHyp` (`sort.Slice`), `lib.RandSeedHyp` (`math/rand.Seed`), `RpcHttpHyp`
  (net/http's server, `rpc.HandleHTTP`: not in Net), `RpcBootHyp` (net/rpc's and net/http's owned
  initializations).
- **No longer a premise** (dsv-gryff-strindex, 2026-11-24): `netN.StringsIndexHyp`. Perennial
  `fce59af75` translates `strings.Index` with its body; `stringsIndexHyp_holds` (axiom-free, over
  `stringslite.IndexByte`'s proof; `Dsverify/Proof/gryff/examples/gryffnet/StrIndexHolds.lean`, a
  defs module, moved there from `NonVacuityLinked.lean` with its name) discharges the class in the
  top-level proof.
- Until session 13 the proved theorem also took `stringsPending.spec`
  (`gryff_remote_robust_of_strings`; Perennial's `strings.Cut`/`TrimLeft`); since the pin 52d62e83c
  those are Perennial's proofs and the theorem is `gryff_remote_robust`.

**The removed axiom-based files** are in history at a5f91c8e46 (deleted by 37ed77ef0f):
`NonVacuityLinked.lean`'s local axioms and the twelve `InitInstancesLinked.lean` walks
(`Dsverify/Proof/{net/rpc,net/http,net/http/internal/ascii,net/url,net/textproto,mime/multipart,
crypto/tls,go/token,runtime,internal/runtime/atomic,internal/runtime/sys,
vendor/golang_org/x/net/http/httpguts}/InitInstancesLinked.lean`).

**Follow-up order:** first the cheap ones, gryff's leaf library classes (`StringsIndexHyp` done,
above): `SortSliceHyp`, `RandSeedHyp` (a spec of `sort.Slice`, `math/rand.Seed` in
Perennial or the main tree, or `math/rand` becoming Perennial's with math-rand-isinit, which also
retires `math.rand.InitHyp`); then `net.rpc.InitHyp`, `net.http.InitHyp`, `RpcHttpHyp` and
`RpcBootHyp`, which depend on Upamanyu's model initialization of net/rpc and net/http (their
initializers translated with bodies, net/http's server in Net).

## Which lab run

Ported: run **`gryff-bump-1`** (dsverify-lab `master` `915f964`, `examples/gryff/`; proof
`21ef7d6` tag `final`, fork `ef17c2d`, verified in 1066 s; `dsv_goal_check : SafeDist (orch ::
clients ++ servers) gryffNetCfg`, axioms Lean's three and porcupine's `CheckOperations.wp_proof`).

## Next

**Session 8 (landing prep) end state:** all landing work done except the dependencies at the top of
this file (models-rpc-http, dsv-hyp-imports) and `etc/tcb-report.py --collection
etc/tcb-collections/dsv-gryff.txt --check` (needs the whole repository built: run at landing, after
merging lean again). `wire.BinaryVarintHyps` stays a premise until Perennial #689 reaches the pin.

**Session 7 end state (`4ec8ec43b1` and later): `gryff_remote_robust` is CLOSED.**
`lake build Dsverify.Proof.gryff.examples.gryffnet.TopLevelRobustness`: `#print axioms
gryff_remote_robust` = `[propext, Classical.choice, Quot.sound]`. Statement:
`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean` (`DistDeploy gryffKitAddrs (system
σ) g → Robust [] (system σ) g threads (2 ^ 31 - 1)`); proof:
`Dsverify/Proof/gryff/examples/gryffnet/TopLevelRobustness.lean` (dsv-epaxos's pattern:
`robust_of_distProtoLisRBT` over `gryffLas`, `gryff_start`, remote's map/addresses/pending library,
each machine's boot). Pieces: `Client/{Conn,Stream,Op}.lean` + `KitOp.lean` (`op.wp_proof`, fork A
of session 7; `connOk` keeps `repliesOk` over `replyShape`), `Start.lean` (fork B), `Link.lean`,
`Mains.lean`, `ServerSpec.lean`, `Bridge.lean`, `cmd/server*/Boot.lean`.
- **`AllG`:** `KitOp`/`Link` have no `[AllG GF]` section variable: the heap's `gooseAllG` is the
  one `sysSt`/Gryff's ghost state use; a section `[AllG GF]` wins instance resolution and splits
  the two (KitSpecs/KitProof/Mains still carry `[AllG GF]`, instantiated with `gooseAllG` at the
  links; dropping it there is a cleanup).
- **`etc/theorem-loc.py --no-go --list-tcb gryff_remote_robust`:** TCB 689 lines, all premises
  (`tcb_premises 689`, `tcb_axioms 0`); the three `InitHyp`s are counted.
- **`etc/tcb-report.py --collection etc/tcb-collections/dsv-gryff.txt --check`** refuses to run
  until the whole repository is built (409 modules of other parts not built here; a full `lake
  build` is not allowed on the shared host): run it at landing.
- `proof_roots.namespace()` = `Perennial.EtcdGrove.`; `etc/tier-check.py --check`: 20 new
  violations (H1's lab-style `…wp_proof` imports, `Kit -> ModelProof`); `gen-init --check`
  (PERENNIAL_DIR=/shared/perennial-7b2259a12) and `_gryff_boot.py --check` clean.
- Remaining (landing work, item 6 below): merge `lean`/models-rpc-http (then `DialHTTP.spec` stops
  being a premise: `DialHTTP.wp_of_ReadResponse` once Net's `DialHTTPPath` proof compiles and
  ReadResponse is proved, and `RpcHttpAddr`'s fields become Net's), tiers to 0, Perennial #689 for
  `BinaryVarintHyps`, tcb-report.

**Session 6 end state (`a06cfc3e72` + F9's pending files).** Ported and building: everything below
the top level — Wire, Proto*, Pure*, Model, Kahn, X, all H layers, N (all; `N/SpecsCheck` skipped,
a check file), Replica2/{State, Specs, SpecsN, Link}, B (all but `B/Init`, superseded by
`Boot/Defs` + the generated owned boots), Rpc/*, Shares, Server/{Deploy, RpcEnv, MasterDefs,
SpecsDefs, MasterRegister, MasterServe, MasterRun, MasterNew, ServeProof, RegisterProof,
MasterBoot, SpecsReq} (the lab's Server/{Specs, Boot, BootIface}, B/Boot are composed at the kit
level instead: `examples/gryffnet/KitServer.lean`, `Server.wp_proof`), the kit (`Kit`, `KitSpecs`,
`KitProof`, `KitServer`, `ModelSet`, `ModelProof`), Client/Defs, the statement
(`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`, `gryff_remote_robust.spec`) and
`TopLevelDefs`. No sorry, no axiom under `Dsverify/`.

**Remaining, in order:**
1. **`op.spec`** (KitSpecs; the kit client's `op`): fork F9 was proving it in `Client/{Conn, Stream,
   Op}.lean` (uncommitted `Client/Conn.lean`, `N/NetSpecs.lean`'s `dialTimeout` field at the end of
   session 6; check them with a targeted `lake build`). Plan: F8's (in this file's history, commit
   `5151c01965`'s message and KitSpecs' docstrings): ops ≥ K → unknown, else a budget unit;
   `started` + `time.wp_Sleep`; connect (`DialTimeout.spec` + `dial_au` at `addrProto (replicaOf
   c)` from `replicaLis` by `lisProto_addr`, `idTok`→`clientConnAt`, `conn_readerOk`,
   `conn_streamWriterOk` + `gryffWireP_closed`, the 4-byte handshake in `writerRoom`); the request
   (Marshal, `op_begin` with `opAU` from `lin_opAU`, a read's `□ lin` used once, Flush); the reply
   loop (`ownReader_protoNow` on `gryffWireQ`, `acceptStream`'s client branch, `sentLb_comparable`,
   `opDone` → `Φ` by Proto/ClientLaws' claim law, errors by `rdErr_conn'`).
2. **The start bridge for wildcard listeners**: `Net.robust_of_distProtoRB` gives `addrUnset` for
   the listed addresses only; the seven wildcards (":7501", ":7502..7504", ":8502..8504") need
   `lisUnset`. Write a kit-local copy of `robust_of_distBootRB` with `addrs_lis_start` in place of
   `addrs_start` (public lemmas: `goose_dist_adequacy`, `net_globalStart`, `addrs_lis_start`,
   `nodeWp_of_distBootG`; the listeners take pairwise disjoint address sets, none a client address).
   A design finding for Net: a `robust_of_distProtoRB` variant with wildcard listeners.
3. **Owned net/rpc init on the server machines**: `etc/dsv/_gryff_boot.py` must treat net/rpc (and
   net/http: `gNoRpc`) as owned too (`RpcBootHyp.wp_init_own`, giving `rpcBootRes ∗ muxFree`), and
   generate an owned boot for `server1` (the master) as for the replicas.
4. **`Start.lean`**: the rpc world `γ.rpc` (`SS := rpcServicesDef`, handshakes per `worldOk`, `inv
   regN' (regInv W)`), Gryff's ghost state (port the lab's `StartInit.lean`: `budget0`, `claims0`,
   …), `deploy_alloc`, `lis_set_proto` for the replica ports (`gryffWireP/Q γ (portAddr k)`),
   `H.rpcLisP_set` for the four rpc listeners, remote's pending library over `casR γ.proto` with
   `casS0` + `mapCtx` + the six `remoteAddr`s, the shares (`clientNodeShare`, `serverShare`).
5. **`Mains.lean`, `Linked.lean`, the proof `TopLevelRobustness.lean`** (paxos's pattern): Linked
   discharges `KitProof`'s, `Server.wp_proof`, `Model.wp_proof`, `gryffCodecLaws`/`gryffRcvLaws`,
   `lib.io.ReadFull.wp_proofLt`, Net's net/rpc (`Client.Call`, `DialHTTP`, `SetCodec`) and remote's
   (`Check`, `ServeClient`) `wp_proof`s, `netN.NetSpecs` and `wire.BufioSpecs` from the
   `wp_proof`s (no instance). **`DialHTTP.spec` is proved over `http.ReadResponse.spec`**, not yet
   proved on models-rpc-http: unless it lands first, `http.ReadResponse.spec` becomes a premise of
   the statement (name it so). Then `#print axioms gryff_remote_robust`, `etc/theorem-loc.py`
   (InitHyp premises counted), the link check (VR finding 7), `etc/tcb-collections/dsv-gryff.txt`.
6. **Landing work**: merge `lean` (Perennial `48401b6ba`/later, `/shared/perennial-*`; repoint
   overrides/`PERENNIAL_DIR`, regenerate PkgTables) and models-rpc-http when it lands (drop
   `RpcHttpHyp`'s `rpcLisP*`, `Server_ServeHTTP_spec` for Net's); use `Net.sentLb_agree/_le`,
   `recvTokL_sentLb` (delete N/ConnLaws' copies); `etc/tier-check.py --check` (lab-style proof
   imports: KitServer, Replica2/Link, H2c2/ExecOverwrite's `…wp_proof` call; restructure as
   needed); `etc/goose.py --check --project dsv-gryff`, `gen-init --check`, `_gryff_boot.py --check`.

**Tiers at `f6213e1528`: 20 new violations** (`etc/tier-check.py --check`), mostly `defs->proof` from H1/H2 modules importing H1 modules that hold lab-style `…wp_proof` theorems (Parti, CoordW2, …) and `Kit -> ModelProof`: rename those theorems or split statements from proofs before landing.

**Design findings this session (for the report):** remote's `ServeClient` needs the client state
behind a persistent token (kit `Sys.mu`); remote gives no per-client bound on operations (kit
`ops ≥ K`); `Check`'s `codecOk` needs an injective `EncIn` (24 bytes); Net's `NewServer.spec` does
not expose the fresh server's empty service map (`RpcHttpHyp.srvFresh`, …); wildcard listeners in
`robust_of_distProtoRB` (item 2); `io.ReadFull.spec`'s read condition at every length (rabia's
`specLt`, `Lib/ReadFullLt`); lean-check false "0 errors" on new files (confirm with `lake build`);
concurrent `lake` builds in one worktree race on `.olean`s.

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

## math-rand-isinit (2026-11-24)

`math.rand.InitHyp` is no longer a premise of `gryff_remote_robust`: `math/rand`'s `isPkgInit` is
Perennial's (`isInit`), its `wp_initialize'` Perennial's proof, so `etc/dsv/gryff.py`'s `HYP_INITS`
drops `math.rand` and the generated initializers call it (`ExternalInit.math_rand`). `RandSeedHyp`
stays (`Seed` is names only at fce59af75); its precondition `isPkgInit math.rand` is now Perennial's
fact, a stronger precondition and so a weaker premise. `NonVacuityLinked.lean` drops its
`mrand_initHyp_holds` walk. See `notes/math-rand-isinit.md`.
