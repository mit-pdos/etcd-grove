# dsv-gryff: dsverify-lab's gryff kit on the net extension (phase 6)

Branch `dsv-gryff` (2026-11-23), off `origin/dsv-paxos` (paxos not landed on `lean` yet; merge
`origin/lean` once it is). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern:
`notes/dsv-paxos.md`. Source: dsverify-lab `master` `915f964`, `examples/gryff/` (run
**`gryff-bump-1`**, the final verified run: clients on nodes of their own, Perennial `3afd77e35`;
proof `21ef7d6` tag `final`, fork `ef17c2d`; read only, nothing in the lab changed).

**State: Go and translation done (`lake build` of `Dsverify.GeneratedProof.gryff.examples.gryffnet`
and the eleven `cmd` modules green, 2026-11-23; `etc/goose.py --check --project dsv-gryff` clean);
the proof port is blocked** on model pieces not proved yet
(below, "Blocked"). No Lean proof is written yet; nothing under `Dsverify/` for gryff has an axiom
or `sorry` (there is no proof).

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/gryff/` (module `gryff`, the fork's path): the fork's packages the kit reaches (`src/{fastrpc,dlog,state,stats,clientproto,genericsmrproto,masterproto,epaxosproto,gryffproto,bitvec,bloomfilter,genericsmr,gryffcommon,gryff,masterlib,serverlib}`, non-test files only, unchanged, the fork's ghost prophecy code included) and the kit `examples/gryffnet` with its eleven commands `cmd/{orch,client0..5,server1..4}` |
| net/rpc codec | `examples/gryffnet/rpc.toml` -> `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` by `models/net/rpc/rpcgen.py` **with a one-line fix** (below, "Findings") |
| translation | `etc/goose.py` project `dsv-gryff` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/gryff/`), std_models `net/rpc`, `net/http` (as project `models-net`); remote, `net` and the models `Net/`'s, lintest, porcupine, `bufio`, `os` the main tree's, the rest Perennial's. `Dsverify/Code/gryff/src/stats.toml`: `StatsMap.Export` names only (JSON to a file; never called: no statistics file) |
| the protocol's proof | not ported yet |
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

## Blocked: model pieces the kit needs that are not proved (as of 2026-11-23)

The coordinator's instruction (2026-11-23): no bufio widening, no rpc-server or library models in
this branch; where a spec is needed, take it as a hypothesis named after the lab's spec.

1. **net/rpc's server side** (plan 5.2, items 4-6; `models-rpc-server` has the codec and
   `Register` part, not landed). The kit runs, on the master, `rpc.NewServer`, `Server.Register`,
   `Server.HandleHTTP(DefaultRPCPath, DefaultDebugPath)` and `http.Serve(l, nil)`; on a replica,
   `rpc.Register` (`DefaultServer`), `rpc.HandleHTTP`, `http.Serve`; and `rpc.DialHTTP` +
   `Client.Call` (replica -> master `Master.Register`; master -> replica `Replica.Ping`,
   `Replica.BeTheLeader`). Missing specs: `Net/Spec/net/rpc/{Register,Server__HandleHTTP,HandleHTTP,
   Server__ServeHTTP,Server__ServeConn,Server__ServeCodec,DialHTTP,DialHTTPPath}.lean` (none
   exists; `NewServer`, `Server__Register` exist on `origin/models-rpc-server` only), and net/rpc's
   package initialization (`isPkgInit` of `net/rpc`: plan 5.2 item 5). The lab's are
   `Harness/Proof/net/rpc/{Server,HandleHTTP,HttpPath,Setup,initialize}.lean`.
2. **net/http's server** (plan 5.2 item 7): `http.Serve`, `Server.Serve`, `conn.serve` up to the
   hijack, `ServeMux.ServeHTTP`/`Handle`, `ReadResponse` on the CONNECT answer. No spec in `Net/`;
   the lab's: `Harness/Proof/net/http/{Serve,Mux,Handler,Head}.lean`.
3. **bufio** (the shared change the coordinator is arranging on #24): the main tree's
   `Code/bufio.toml` translates `NewReader`, `NewReaderSize`, `Reader.Read` (and helpers) only.
   Gryff needs `NewWriter`, `Writer.{Write,WriteByte,Flush,Available,Buffered}`,
   `Reader.ReadByte`, `io.ReadFull`/`ReadAtLeast` over a `*bufio.Reader` (every message's
   Marshal/Unmarshal; genericsmr's peer and client readers and writers; the kit's client). The lab's
   specs: `Harness/Proof/bufio/{Writer,Reader,ReadFull,Net}.lean` (`wp_NewWriter`, `wp_Flush`,
   `wp_WriteByte`, `wp_Write`, `wp_NewReader`, `wp_ReadByte`, `wp_Read`, `wp_ReadAtLeast`,
   `wp_ReadFull`).
4. **Smaller library pieces the lab had as its own models** (to check against Perennial's specs when
   the port starts): `log` (`Harness/Proof/log.lean`: `Printf`/`Println`/`Fatal`; Perennial
   translates `log`), `math/rand` and `math` extras (`Harness/Proof/math/{rand,Extra}.lean`),
   `time`/`strings` extras (`Harness/Code/{time_extra,strings_extra}`), `os` (the `*os.File` type
   only: the stable store's `Write`/`Sync` are behind `Durable`, false here, fix T4),
   `encoding/json`/`io/ioutil` (avoided: `stats.toml` above).

How far the blockers reach into the lab's proof (its import graph, 369 modules, 112k lines): only
21 modules (5k lines: `Model/` the replica's step model, `Kahn/`, the tag order, a few defs) reach
no library spec. Everything else, the pure protocol layers (`Pure*`, `Proto*`) included, imports
the lab's library vocabulary transitively, through the shared ghost names and invariant modules
(`GryffProof/Names.lean` imports `Harness.Proof.net.rpc.Results` and `net/http`'s `Mux`;
`Proto/` imports the `NetConn` specs and `bufio.Base`). The `NetConn` part is what the port
replaces by `Net/`'s specs anyway; the rpc/http and bufio parts are items 1-3. A port before they
land would first split `Names`/`Proto` so that the pure layers name no rpc/http vocabulary, then
take the bufio specs as hypotheses (the coordinator's instruction).

## Findings

- **rpcgen emits an unused import** (`models/net/rpc/rpcgen_core.py`, `Spec.imports()`): a
  receiver whose package holds none of the codec's types (gryff: `*masterlib.Master`,
  `*gryff.Replica`; the arguments are `masterproto`'s and `genericsmrproto`'s) is imported by
  `rpc_gen.go`, which does not use it, so the package does not compile. The difftest never saw it
  (its receivers and types share a package). Fix (used here from a scratch copy of the generator;
  `models/` unchanged on this branch): `imports(receivers=True)`, and `rpc_gen.go`'s caller passes
  `receivers=False` (the model file computes its own imports; the generated test needs the
  receivers'):
  ```
  -    def imports(self):
  +    def imports(self, receivers=True):
  -                      or any(self.uses(r["type"], p) for r, _ in self.receivers))
  +                      or (receivers and any(self.uses(r["type"], p) for r, _ in self.receivers)))
  -    imps = S.imports()      # in the rpc_gen.go writer
  +    imps = S.imports(receivers=False)
  ```
  Until it lands, `rpcgen.py --check` on this kit fails.
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

1. When bufio (item 3) is decided: port the protocol proof by editing (pure parts first, they are
   independent of it), onto `Net/`'s `net` specs and `Proto.lean`'s laws, as dsv-paxos did.
2. When net/rpc's server and net/http's server (items 1-2) have specs: the master and the
   registration, the kit's proofs (`Mains`, `Linked`, the model's proof as paxos's `ModelSet`/
   `ModelProof`), `gryff_remote_robust`, the TCB collection, `etc/gen-init.py` `dsv_inits` entries.
