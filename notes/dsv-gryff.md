# dsv-gryff: dsverify-lab's gryff kit on the net extension (phase 6)

Branch `dsv-gryff` (2026-11-23), off `origin/dsv-paxos` (paxos not landed on `lean` yet; merge
`origin/lean` once it is). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/gryff/` (run
**`gryff-bump-1`**, the final verified run: clients on nodes of their own, Perennial `3afd77e35`;
proof `21ef7d6` tag `final`, fork `ef17c2d`; read only, nothing in the lab changed).

**State (2026-11-23, resumed under the coordinator's rule "missing library specs become
hypotheses"):** Go and translation done (`lake build` of the gryffnet modules green; `etc/goose.py
--check --project dsv-gryff` clean); **the protocol proof is being ported by editing**, bottom-up:
the library-free layers (`Model/`, `Kahn/`, the tag order, `Pure*`, `Proto/` pure parts, `B.Pure`,
`Wire.Enc`/`Varint`) build, over `Names.lean` split from the lab's rpc/http vocabulary (it imports
`Net/`'s `Net.Proof.net.rpc.Proto`, `RpcWorld`, only). The library-facing layers (NetConn -> `Net/`,
bufio/rpc/http as hypotheses), the client on remote, the model's proof, Mains, Linked and
`gryff_remote_robust` are not done. No `sorry`, no axiom under `Dsverify/` (the missing pieces are
hypothesis classes, below).

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/gryff/` (module `gryff`, the fork's path): the fork's packages the kit reaches (`src/{fastrpc,dlog,state,stats,clientproto,genericsmrproto,masterproto,epaxosproto,gryffproto,bitvec,bloomfilter,genericsmr,gryffcommon,gryff,masterlib,serverlib}`, non-test files only, unchanged, the fork's ghost prophecy code included) and the kit `examples/gryffnet` with its eleven commands `cmd/{orch,client0..5,server1..4}` |
| net/rpc codec | `examples/gryffnet/rpc.toml` -> `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` by `models/net/rpc/rpcgen.py` (`--check` clean since lean `660918251a`, the receivers' import fix) |
| translation | `etc/goose.py` project `dsv-gryff` (its entry in `etc/dsv/gryff.py`, dsv-infra's per-kit file) into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/gryff/`), std_models `net/rpc`, `net/http` (as project `models-net`); remote, `net` and the models `Net/`'s, lintest, porcupine, `bufio`, `os` the main tree's, the rest Perennial's. `Dsverify/Code/gryff/src/stats.toml`: `StatsMap.Export` names only (JSON to a file; never called: no statistics file) |
| the protocol's proof | `Dsverify/Proof/gryff/` (modules `Dsverify.Proof.gryff.*`, namespaces the lab's): ported by `port.py`'s mechanical renames then edited; the lab's `Harness` vocabulary the proof keeps, its pure parts only, under `Lab/` (`Model`, `ModelsCas`'s `casRegister`, `ClientSpec`'s `clientN`/`opAwp`/`opAwpMaybe`); `Slots.lean` holds the packages' states (the lab's generated `GryffNetPkgState`) |
| the statement | not written yet (`gryff_remote_robust.spec`, `DistDeploy … → Robust [] …`, as `paxos_remote_robust`) |
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

No widening of bufio's goose config, no rpc-server or library models in this branch: a spec the
proof needs from a missing piece is a hypothesis, named after the lab's spec, that the kit's
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
3. **bufio**: the shared change is `origin/dsv-bufio` (`bb18c0f3ef`, in review); this branch uses its
   names when it reaches the call sites (merging it, or as hypotheses of the same names and shapes
   until it lands): `EtcdGrove.bufio.NewReader.specOk`, `Reader.Read.specOk`, `Reader.ReadByte.spec`,
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

## Which lab run

Ported: run **`gryff-bump-1`** (dsverify-lab `master` `915f964`, `examples/gryff/`; proof
`21ef7d6` tag `final`, fork `ef17c2d`, verified in 1066 s; `dsv_goal_check : SafeDist (orch ::
clients ++ servers) gryffNetCfg`, axioms Lean's three and porcupine's `CheckOperations.wp_proof`).

## Next

1. The library-facing layers of the protocol proof: the lab's NetConn vocabulary at its fixed
   `netDistGF` becomes `Net/`'s `Proto.lean` at a generic `GF` (as dsv-paxos and dsv-vr;
   `addrProtoG` -> `addrProto`, `sentLbG` -> `sentLb`, `connFreshG` -> `connFresh`, ...; the
   connection ids are `w64` there, `Nat` here), bufio/rpc/http/log as the hypotheses above.
2. The client on remote (`Op(sys, in)` with remote's `lin` update, as paxos's `opAU`), the model's
   proof (kit.go's `Model` against linkv's `PendSpec`), `Mains`, `Linked`, `gryff_remote_robust`,
   `dsv_inits` entries, `etc/tcb-collections/dsv-gryff.txt`.
