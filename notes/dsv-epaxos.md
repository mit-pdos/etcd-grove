# dsv-epaxos: dsverify-lab's EPaxos kit on the net extension (phase 6)

Branch `dsv-epaxos` (2026-11-23), off `origin/dsv-paxos` (`e3eaf5cd0d`; paxos has not landed on
`lean` yet). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/epaxos/` (run **`epaxos-e1nogs-1`**, the final
verified run of EPaxos: clients on nodes of their own, Perennial `3afd77e35`, the E1-opt1/opt2 perf
fixes; proof `c276a91` tag `final`; fork `71d99d4`). Read only: nothing in the lab changed.

**State: BLOCKED after the Go and the translation** (below, "What blocks"). No Lean proof is
ported yet: the protocol proof (88k lines in the lab) rests at every layer on library pieces that
are not proved here (bufio's writer and reader methods, net/rpc's server, net/http's server and
`DialHTTP`, gods' treemap), which the coordinator said to take as hypotheses rather than add; that
work has not started.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/epaxos/` (module `github.com/imdea-software/swiftpaxos-epaxos`: the fork's path with `-epaxos`, see below): the fork's packages the kit runs (`rpc` = fastrpc, `dlog`, `config`, `state`, `replica/defs`, `replica`, `epaxos`, `master`, with the fork's `fix_*_test.go` regression tests) and the kit `examples/epaxosnet` with its 17 commands `cmd/{orch,client0..9,server1..6}` |
| the kit | `examples/epaxosnet/kit.go` (configuration, addresses, `Gen`, `Op`, `Orch`, `Client`, `Server`, the replicas' registration), `model.go` (the porcupine model and remote's `Codec`), `rpc.toml` + `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` (rpcgen's codec of the master's and the replica's net/rpc receivers), `kit_test.go` |
| translation | `etc/goose.py` project `dsv-epaxos` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/github_com/imdea_software/swiftpaxos_epaxos/**`, and gods v1.18.1 at `Dsverify/{Code,GeneratedProof}/github_com/emirpasic/gods/**`); remote, `net`, net/rpc and net/http the part `Net/`'s (std_models `net/rpc`, `net/http`); lintest, porcupine, `bufio`, `encoding/json`, `os` the main tree's; the rest Perennial's |
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

## What blocks

The proof needs specs of library code that is not proved in this repository (the coordinator's
instruction, 2026-11-23: state each as a hypothesis named after the lab's spec, list it here, do
not widen shared translations or add models):

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
   nothing proves the rest. The lab used a cut-down copy with its own proof. A model of gods for
   `models/` is the coordinator's to decide.
5. Also used, with specs to check before the port: `log` (`Logger.Printf`/`Println`/`Fatal`,
   through dlog), `encoding/json` (the replica's latency config, never read: `LatencyConf` ""),
   `sort`, `math`, `strconv`, `fmt.Sprintf` (the master), `time`, `os`.

## Next (for a successor)

1. Initializers: extend `etc/gen-init.py`'s `DSV_PKGS`/`DSV_PROGRAMS` (additively) with this kit's
   packages and 17 programs; write the packages' `Base.lean` facts (the lab's `Epaxos/Proof/init/`).
2. The pure model (`Epaxos/Model/`, 31k lines, plus `Interface/{Names,Wire}`, `Proof/epaxos/{Tarjan,
   ExecModel}`): mostly namespace edits (`github_com.imdea_software.swiftpaxos` →
   `..._epaxos`, `Epaxos.` → `Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.`).
3. The code proofs over `Net/`'s specs with the hypotheses above; the kit's model proof (as paxos's
   `ModelSet`/`ModelProof`); the statement `epaxos_remote_robust`.
