# dsv-epaxos: dsverify-lab's EPaxos kit on the net extension (phase 6)

Branch `dsv-epaxos` (2026-11-23), off `origin/dsv-paxos` (`e3eaf5cd0d`; paxos has not landed on
`lean` yet). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/epaxos/` (run **`epaxos-e1nogs-1`**, the final
verified run of EPaxos: clients on nodes of their own, Perennial `3afd77e35`, the E1-opt1/opt2 perf
fixes; proof `c276a91` tag `final`; fork `71d99d4`). Read only: nothing in the lab changed.

**Merges (2026-11-23, later):** `origin/lean` (`07268ddb57`: dsv-paxos, dsv-bufio (with the
rename `io.writerOk` → `io.streamWriterOk`, `net.conn_writerOk` → `net.conn_streamWriterOk`; this
kit used them only in comments), dsv-infra, the wildcard listen, **Perennial `7b2259a12`**:
`.lake/package-overrides.json` and `PERENNIAL_DIR` now `/shared/perennial-7b2259a12`; the build
was seeded from `/shared/etcd-grove-dsvbufio/.lake/build` (everything but `Dsverify/`); the 17
`PkgTable.lean`s (and paxos's) regenerated; `gen-init.py --check` and `goose.py --check --project
dsv-epaxos` pass) and `origin/models-rpc-server` (`36728bd8ed`, not landed: Client.Call's decode
obligation only for the method's answers, methodOk's `argDec` guard on the server; nothing here
used the old shapes yet).

**Earlier merges (2026-11-23):** `origin/dsv-infra` (`a1046d9c4f`, then `884cb306c9`): the kit's goose
project and gen-init configuration are now `etc/dsv/epaxos.py` only (no shared lines of
`etc/goose.py`/`etc/gen-init.py` are this kit's; `gen-init.py --check`, `goose.py --check --project
dsv-epaxos` up to date). `origin/models-rpc-server` (`040ef5e808`, not landed: waits for the human
reviewer; the coordinator's instruction): the whole net/rpc server proved on Lean's three axioms;
the kit builds against its server specs directly (no mirrored hypotheses for net/rpc's server).
`origin/dsv-bufio` (`75ef5881aa`, the revision after Upamanyu's review; under re-review, not
landed): bufio's generic specs (table in the last section of `notes/dsv-bufio.md`); bufio now
imports `bytes`/`strings`, so `Dsverify/Proof/bufio/Init.lean` and the 17 `PkgTable.lean`s were
regenerated (`lake build` of `cmd.{server2,orch,client0}.PkgTable` passes). It also brought
`origin/lean` (`92eb404dbc`: dsv-tpmodels' gods/uuid/concurrent-map/slog models).

**State (2026-11-23):** the Go, the translation, the package initializers (all 32 packages and the
17 programs' `PkgTable`s build, no axiom: the names-only inits are `InitHyp` hypotheses) and the
mechanical port of the pure model (below, "Proof port: progress") are done. The code proofs, the
kit's model proof and `epaxos_remote_robust` are not started; every layer of them rests on library
specs that are hypotheses here ("Hypotheses").

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/epaxos/` (module `github.com/imdea-software/swiftpaxos-epaxos`: the fork's path with `-epaxos`, see below): the fork's packages the kit runs (`rpc` = fastrpc, `dlog`, `config`, `state`, `replica/defs`, `replica`, `epaxos`, `master`, with the fork's `fix_*_test.go` regression tests) and the kit `examples/epaxosnet` with its 17 commands `cmd/{orch,client0..9,server1..6}` |
| the kit | `examples/epaxosnet/kit.go` (configuration, addresses, `Gen`, `Op`, `Orch`, `Client`, `Server`, the replicas' registration), `model.go` (the porcupine model and remote's `Codec`), `rpc.toml` + `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` (rpcgen's codec of the master's and the replica's net/rpc receivers), `kit_test.go` |
| translation | `etc/goose.py` project `dsv-epaxos` into the part `Dsverify/` (`Dsverify/{Code,GeneratedProof}/github_com/imdea_software/swiftpaxos_epaxos/**`, and gods v1.18.1 at `Dsverify/{Code,GeneratedProof}/github_com/emirpasic/gods/**`); remote, `net`, net/rpc and net/http the part `Net/`'s (std_models `net/rpc`, `net/http`); `encoding/json` the part's names-only translation of the model (dsv-vr's, std_models `encoding/json`; files identical to dsv-vr's); lintest, porcupine, `bufio`, `os` the main tree's; the rest Perennial's |
| initializers | `etc/gen-init.py` (additive: `DSV_EPAXOS`, `DSV_MAIN`, `DSV_MAIN_COPY`, the epaxos `SPECIAL`s, `DSV_PKGS`/`DSV_PROGRAMS`; dsv-vr's `dsv_hyp_fix`/`DSV_HYP_NEED` taken over verbatim, `DSV_HYP_INITS` the union `encoding.json`, `net.rpc`, `net.http`): `Init.lean` of every package, `PkgTable.lean` of the 17 programs; `Base.lean` facts all `True` (hand-written, `Dsverify/Proof/**/Base.lean`); `Dsverify/Proof/bufio/Init.lean` a generated copy of the main tree's; hypotheses `Dsverify/Proof/{net/rpc,net/http,encoding/json}/Init.lean` (the first two from `scratchpad`'s template, the same shape as dsv-vr's) |
| pure model | `Dsverify/Proof/github_com/imdea_software/swiftpaxos_epaxos/{Model/**,Interface/Wire.lean,epaxos/{Tarjan,ExecModel}.lean}` (the lab's, renamed), `Model/KvScan.lean` (the lab harness's `kvScan`, pure) |
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

## Proof port: progress

1. **Initializers: done** (`01ac72f60b`, `c7617216ca`). Notes: `gen-init`'s closure stops at a
   hypothesis package (its `imports=[]` and `pkginfo_imports` → `[]`: its `GetIsPkgInitWf` is
   hand-written, `g p = isPkgInit p ∧ True`), so a program's table does not need facts of net/http's
   untranslated closure. `epaxos`' initializer: `deferMap` is `make(map[uint64]uint64)`
   (`wp_map_make1`), `errVarintOverflow` an `errors.New`. The facts the lab proves
   (`Epaxos/Top/PkgState.lean`: `errVarintOverflow`, `deferMap` ↦□, `LatencyConf` ↦□ "") are not
   yet in `Base.lean`: add them (gen-init `finish` steps) when a code proof reads them.
2. **Pure model: ported mechanically** (`etc/dsv-epaxos/port.py`: module
   `Epaxos.{Model,Interface}.X` → `Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.
   {Model,Interface}.X`, `Epaxos.Proof.X` → `…swiftpaxos_epaxos.X`; identifier `swiftpaxos` →
   `swiftpaxos_epaxos`; `dsverify_lab.harness` → `…swiftpaxos_epaxos.kvs`; `KvsInput/KvsOutput/
   Option GoString` → `(List w8)`, as this Perennial's `GoString` is not `List w8`). By hand:
   `Interface/Wire.lean` imports `Model/KvScan.lean` in place of `Interface/Names.lean` (the lab's
   net harness) and drops the harness's local instances. **Builds** (2026-11-23, `lake build
   …Model.Proof.{ExecWfInv,G1Replay,NoneRec}`, the leaves; 63 files, 32k lines, no `sorry`;
   `#print axioms model.inv_step_deliver`: Lean's three). Also `Interface/PeerWire.lean` (the peer
   messages' pure encoders and `Countable` instances; by hand: imports `Perennial.Std.Countable`,
   which the lab's `Names` brought, and keeps `open Iris`).
3. **Interface layer, by hand (in progress).** `Interface/Names.lean` (`EpNames`, without the
   lab's `rpc : RpcWorld netDistGF` field: Net/'s net/rpc world is passed on its own when needed),
   `Interface/Net.lean` (the peer streams' ghost vocabulary; GF generic under `GooseGlobalGS`,
   statements annotated `(GF := GF)`; connection ids are the extension's `Nat`, so `peerConn`'s
   variable is `Option Nat` and `cwriters` maps a writer to a `Nat`), **`Interface/Client.lean`
   redesigned**: the op's update is `opU γ i Φ`, exactly remote's `lin` of the store (`sysState =
   own_state γ`, `Eop = epEop = ↑epN`, `B.step = kvStep`, the function form of `kvScan`,
   `kvStep_spec`), in place of the lab's `AU … @ ↑clientN`; the escrow keeps `Φ o` (not the lab's
   `Q σ σ' o`); `escrow_fire` needs `⊤ ∖ epEop ⊆ E` (was `↑clientN ⊆ E`) and still gives the
   lab's `(kvScan w8).step σ i σ' o`; `escrow_claim` gives `Φ o`; `inPre` is the lab's `kit.pre`;
   `serverAddrs`/`replicaAddrs` the kit's `ServerAddrs()` (7501..7506; replicas 7502..7506); the
   lab's `is_sys`, `orchShareEp`, `clientShareEp` are gone (remote's start and `Op(addrs, c, in)`
   replace them). `solve_ndisj` (the lab harness's) → `nclose_subseteq`.
3b. **`Interface/Treemap.lean`**: gods' treemap as the hypothesis class `TreemapHyp GF` (abstract
   `isTreeMap`/`iterVal`/`ownIter`; `NewWith_spec`, `Put_spec`, `Get_spec`, `Select_spec`,
   `Iterator_spec`, `iter_alloc`, `Next_spec`, `Value_spec`); `Interface/State.lean` over it.
   Every theorem that uses the store takes `[TreemapHyp GF]`. (dsv-tpmodels' Go model
   `models/gods` has landed but no spec of it is proved; once one is, translate gods through
   `module_models` and discharge the class.)
3c. **The `state` package's proofs: done** (`wire/State/*.lean`, the lab's files via
   `etc/dsv-epaxos/port.py`, which now also rewrites the proof-file headers to the generic `GF`):
   `InitState`, `NIL`, `NOOP`, `Conflict`, `ConflictBatch`, `concat`, `formatUint10`,
   `Key/Value/Command.String`, `KeyComparator`, `Command.Execute`. Changed: the lab's
   `Treemap*.lean` (its cut-down treemap's proofs) are not ported; `Execute`'s `SCAN` case is
   re-proved over `TreemapHyp` (`Select_spec` with the closure's triple, `Iterator_spec`, a loop
   over `ownIter`; pure: `ScanPure.scan_flatten_sorted`, `Execute.vals_es`); `ScanPure` defines
   `keysSorted` (was `TreemapLemmas`'). `#print axioms`: Lean's three (2026-11-23).
3e. **`Interface/Varint.lean`** (`epaxos.putVarint.spec`, `pkgInit_{state,defs,epaxos}` and
   `sint_Z_W64_length`, split out of the lab's `Interface/Marshal`) and
   `wire/Varint/{PutUvarint,PutVarint,Decode}`: ported, 0 errors.
3g. **The marshal layer: DONE (2026-11-23)** over dsv-bufio (`75ef5881aa`):
   `Interface/Marshal.lean`, `wire/{WProg,RProg,Bytes,Binary16,Codec,Varint,Link}`,
   `wire/Varint/{ReadUvarint,ReadVarint}`, `wire/Marshal/*` (18 files). `lake build
   …wire.Link` passes; `#print axioms` of `Serializable.{Marshal,Unmarshal}.wp_proof`,
   `replica.defs.Propose.Unmarshal.wp_proof`, `epaxos.readVarint.wp_proof`: Lean's three. Design
   (changed against the lab):
   - The writer's and reader's parameters are bundled: `BufWr GF` (`wi`, `J`, `Q`, `Ew`, `sz`,
     and `Q_pre : ∀ x y, Q (x ++ y) ⊢ Q x`: the marshalers' partial writes need `Q` prefix-closed,
     which the lab read off its `writerOk`; dsv-bufio's `io.streamWriterOk` holds it inside the sealed
     `ownBufWriter`, so it is a Lean field; a connection's `Q = P cn` with `ProtoPrefixClosed P`
     gives it) and `BufRd GF` (`ri`, `Pre`, `S`, `E`; a stream fact `F` with `F_pers`,
     `F_of : S r ⊢ S r ∗ F r`, `F_pre` prefix-closed: exactly `bufio.ownBufReader_fact`'s
     premises; `Pre_pos : 0 < m → Pre r m`, a connection's `Pre`). `wrOwn bw wr …` /
     `rdOwn br rd R` abbreviate `EtcdGrove.bufio.ownBufWriter`/`ownBufReader` (never unfolded).
   - `nextIs rd R enc wf := □ ∀ r, rd.F r -∗ ▷ ⌜R <+: r → …⌝`: over the stream fact, **a step
     later** (for a connection `F = ▷ protoPrefix P cn` from `net.connReader_proto`; the lab's
     `nextIs` was over its harness's stream state `I S`, with no later). `nextIs_read` returns
     `▷ ⌜…⌝`; the decoders strip it with `imod H with %H` (a WP goal, a timeless pure fact).
     For a connection the caller (the replica's listener, the lab's `listener_nextIs`) proves
     `nextIs` from `▷ protoPrefix` and its role element, under the later.
   - `marshalTriple`/`unmarshalTriple`: as the lab's with the bundles; `isPkgInit bufio` stays a
     conjunct (for `io`'s error values); the lab's `bufio.streamWriterOk`/`readerOk` conjuncts are gone
     (inside the reader/writer); an unmarshal error is only `⌜err ≠ nil⌝` (the lab's
     `net.rpc.errAny` was its harness's). `wire/RProg`'s `wp_ReadFull_br`/`wp_ReadAtLeast_br` are
     Perennial's `io.wp_ReadFull`/`io.wp_ReadAtLeast` over `bufio.ownBufReader_readerOk`, their
     error results `ptrTyped` no more; the lab's `Varint/ReadByte.lean` (`wp_ReadByte_wf`) is
     dsv-bufio's `Reader.ReadByte.spec` (its error is `ptrTyped`); the lab's `BufioSticky.lean`
     and `Interface/BufioLocal.lean` are dsv-bufio's sticky-error clauses (`wire/WProg`).
   - `etc/dsv-epaxos/port.py --bufio` does the call-site rewrites (argument bundles, dropped
     conjuncts and error facts, `imod` after `nextIs_read`, `(GF := GF)` on statements whose
     only `GF` is inside a spec): the 18 `wire/Marshal/*` files needed no hand edit.
3f. **The ghost chain: DONE (2026-11-23)**: `epaxos/{GhostLib,GhostDefs,GhostLaws,GhostStep,
   ExecFacts,NoReply,GhostDeliver,GhostBasic,GhostRep,GhostSimple,GhostSend,GhostExec}` and the
   model-side facts `epaxos/{ModelFacts,PAModel,PARModel,PRModel,PRDecide,RecModel}` (`lake build`
   of the leaves passes; no `sorry`). Changed against the lab:
   - **Connection ids are `Nat`** (`Net/`'s connection numbers), not the lab net model's `w64`:
     `Model/State.lean` `Proposal.cid : Nat`, `Model/Sys.lean` `Sys.fired : Nat → …` (the model
     proofs needed no other change: the cid is only compared); the escrow/fired maps are
     `GMap Nat KvO` (`Interface/Client.lean`).
   - **The escrow fires under remote's mask**: `ep_execCmdB` (`GhostExec`) takes
     `(hEc : ⊤ ∖ epEop ⊆ E)` and `(hNc : ↑N ⊆ epEop)` (the replicas' invariant `N` inside `epN`)
     in place of the lab's `↑clientN ⊆ E`, `N ## clientN`; callers (the executor's proofs) pass
     these.
   - `iinv`'s side-condition solver (`simp [*]`) loops on `ep_execCmdB`'s hypotheses with a
     generic `GF`; they are hidden across it (`hideP`, a FIXUP).
   - `port.py` now: `(GF := GF)` on the first ghost predicate of a statement with no other `GF`
     (`gf_preds`/`gf_annotate`, scanning every ported file's `def … : IProp GF`); the lab's section
     headers to the generic world with `[π : NetProtoGS]`; `kit.pre` → `inPre`; per-file hand
     edits in `FIXUPS` (re-running the port reproduces them; `GhostSend`, `GhostExec` have some).
3h. **The interface layer above the ghost chain (in progress, 2026-11-23).** Done (each checks,
   `lake build` of the leaves passes, `#print axioms`: Lean's three): `Interface/EpaxosGhost`
   (`protoN` inside `epEop`: `protoN_epEop` replaces the lab's `protoN_clientN_disj`),
   `Interface/RpcTable`, `Interface/Registry` (**the kit's addresses**: server `k` at
   `127.0.0.1:(7500+k)`, its rpc at `127.0.0.1:(8500+k)` (`serve`'s `port + 1000`), the master
   `127.0.0.1:7501`; the lab's `nodeAddrs_*` facts of its 10.77.0.x harness are gone; a span
   FIXUP), **`Interface/ConnBuf.lean` (new)**: a connection's ends as the marshal layer's bundles,
   `connWr t cn s la ra ed P hP sz` (`net.conn_streamWriterOk`'s contract) and
   `connRd t cn s eof la ra ed P` (`net.conn_readerOk`'s, stream fact `▷ protoPrefix P cn`), and
   `repDialP_ppc`/`repAccP_ppc` (`ProtoPrefixClosed`, the lab's `*_prefixClosed`);
   `replica/{Ghost,RpcTable,SliceElems,ClientWire}`: the slots restated over `Net/`
   (`connIn c cid side t la ra ed eof`: `c = connIface t`, `connAt`, `ErrDeadlineExceeded`'s and
   `io.EOF`'s values; peer and client writers `wrOwn w (connWr … 4096)` (all the replica's writers
   are `bufio.NewWriter`), the peer reader `rdOwn rd (connRd …)`; FIXUPS).
   `BufWr.Q_pre` is now `□ Q (x ++ y) ⊢ □ Q x` (`ProtoPrefixClosed.pre`'s form).
   **`Interface/{Replica,ReplicaSpec}` (2026-11-23, hand-maintained after the port; 0 errors):**
   cids `Nat`; `opTok_excl`/`peerRole_register` by `Net/`'s `connFresh_excl`; the lab's
   `repDialP_prefixClosed`/`repAccP_prefixClosed` and the documentation copies `peerP`,
   `peerSlot`, `clientSlot` dropped (ConnBuf's `repDialP_ppc`/`repAccP_ppc`, replica/Ghost's
   `peerSlotX`/`clientSlotX`); **the lab's `addrTok` is gone** (in `Net/` the right to listen at a
   replica address is its `addrProto`'s, in `clientInvs`, through `listen_au`; `fwStart` and
   `replica.New.spec` no longer carry a token); `fwListening` is `net.isListener li l ∗ netLis l a
   true ∗ netLisAt l a` at `a = L[id]`; `fld`/`fwMethod` are stated over `[GoLocalContext]` only
   (with `HeapGS`'s `GF` in them nothing determined `GF` at a use: "stuck go.Semantics");
   `fwFresh`/`replica.New.spec` take `[state.Assumptions] [treemap.Assumptions] [TreemapHyp GF]`
   as binders (a section instance whose dependencies are included is included in every
   declaration mentioning `GF`, and is then stuck at uses).
   **`replica/{Core,Specs,Quorum,Defs,Log,DelayChan,Stream}`: ported, 0 errors.** `connIf c cn s`
   (`Interface/ConnBuf`: `∃ a, net.isConn c cn s a`) replaces the lab's `net.rpc.connIface`;
   `accEnd` is `connIf ∗ sendTok … [] ∗ recvTok … [] ∗ connFresh`, exactly `accept_au`'s
   `connEnd cn true Q P [] [] ∗ connFresh cn true`; `Stream`'s `ownReader_proto` is dropped
   (bufio's `ownBufReader_fact`), `listener_nextIs` is over `connRd t cid side eof la ra ed (peerPin …)`
   (its stream fact `▷ protoPrefix`, stripped with `inext`).
   **`replica/{PrefixReader,SendMsg,ReplyPropose}` (hand-maintained after the port; build,
   no `sorry`):** `PrefixReader`: `prI` over `recvTokL`, `prefixReader_readerOk` (Perennial's
   `io.readerOk (prIface pr) (0 < ·) (prI …) (connReadE …)` from `net.conn_readerOk`; the copy
   branch by `wp_slice_copy_int`), `prRd` (the `BufRd`, stream fact `▷ protoPrefix`).
   `SendMsg`/`ReplyPropose`: dsv-bufio's `Writer.WriteByte.wp_proof`, `Writer.Flush.wp_proof` and
   the kit's `marshalTriple` on `connWr` writers (no `writerOk` premise: the contract is inside
   `ownBufWriter`), the stream's prefix closure by `peerPX_ppc`/`repAccP_ppc`; frame a `wrOwn …
   (connWr …)` goal only after `simp only [wrOwn, connWr]` (the bundle's projections).
   **New hypothesis `BufWriterNotNull`** (`Interface/ConnBuf.lean`): `ownBufWriter bw … ⊢ ⌜bw ≠
   null⌝`, the lab's `ownWriter_not_null` (SendMsg's `PeerWriters[t] != nil`); dsv-bufio has no
   such law and its predicates may not be unfolded here: a premise of `SendMsg.spec_holds`, to be
   discharged by a one-line bufio law (from `writerRep`'s `bw ↦ Writer.mk …`). **Ask for it.**
   **`replica/Beacon`: done** by `port.py`'s new **`writer_conv`** (applied to every file that
   mentions the lab's `bufio.writerOk_conn`): the peer writer's message write (`icases Hconn`
   with the connection's `tc la ra ed eof`, `hNN` for the not-null test, `hppc := peerPX_ppc`,
   `WriteByte.wp_proof`/`Flush.wp_proof`, the marshal call on `connWr … hppc 4096`, the
   obligations by `hppc.pre cid _ _ (prefix_of_eq hfull)`, WriteByte's outcome adapted for
   `send_stream_eq`, the slot repacked after `simp only [wrOwn, connWr]`) and `(hNN :
   BufWriterNotNull)` added to the theorems that use it. `lake build` of
   `replica.{Beacon,ReplyPropose,PrefixReader,Quorum,DelayChan,Stream,Defs}` and
   `Interface.ReplicaSpec` passes (2026-11-23; `etc/lean-check.py` may return after the first
   clean declaration, so build a file before calling it done).
   **2026-11-23 (later, resumed agent): `BufWriterNotNull` discharged** (merged `origin/dsv-bufio-laws`
   `f5de3d32b8`: `bufio.ownBufWriter_not_null`; `bufWriterNotNull` is now a theorem in
   `Interface/ConnBuf.lean`, the premise is gone from SendMsg/Beacon and from `port.py`'s `writer_conv`).
   **Done since (each `lake build` passes, no `sorry`; hand-maintained, listed in `port.py`'s docstring):**
   - `replica/ReplicaListener`: `Reader.ReadByte.wp_proof`; `connRd_fact`/`connRd_fact'` (bufio's
     `ownBufReader_fact` at `connRd`, for the reader's unfolded form, as `ReadByte`'s post returns it, and
     for `rdOwn`); `listener_shape`, `listener_msgSent_later` (`pin_stream`/`listener_msgSent` under the
     stream fact's later, stripped by `imod`: pure, resp. `msgSent` timeless); unmarshal calls framed by
     `simp only [rdOwn, connRd]; iframe`. The ewma update is float64: this Perennial's float ops are
     relational (`wp_float64_mul`/`add`/`div`, `Golang/Theory/Float.lean`), which `wp_auto` does not do.
   - `replica/ClientListener`: `bufio.NewReader.wp_proofOk` over `prefixReader_readerOk` (with
     `net.Conn.Read.wp_proof`), `NewWriter.wp_proof` over `net.conn_streamWriterOk`; `proto_client`,
     `prRd_fact`, `rd_client`/`rd_clientU` (the two forms again), `client_nextIs` over `prRd`;
     `wp_connClose` (`net.Conn.Close.wp_proof` with `close_au`, outcome dropped; `connIs` from
     `sendTok_connIs`); `ownBufWriter_excl` (dsv-bufio-laws) for the writer registration.
     **`clientListener.spec` now takes `connIn conn cid true t la ra ed eof`** (binders `t la ra ed eof`):
     `clientSlotX` needs the connection's globals. **New hypothesis `TCPAddrStringHyp`** (in the file): no
     spec of `net`'s `(*TCPAddr).String` (the lab's `net.TCPConn.RemoteAddr.wp_String`; used for
     `strings.Split(conn.RemoteAddr().String(), ":")[0]`); a premise of `clientListener.spec_holds`.
   - `replica/Pkg` (`replica_net_errs`: `io.EOF`'s, `ErrDeadlineExceeded`'s values from `pkgInit_replica`).
   - `replica/WaitClients`: `Listener.Accept.spec_addrOk Listener.Accept.wp_proof` with `accept_au`
     (paxos's pattern). **`accEnd` now carries `∃ t la ra ed eof, connIn …`** (`replica/Specs.lean`).
   - `replica/ClosestPeers`: one float division step added.
   - `replica/ServeConn`: `io.ReadFull(conn, …)` by **`replica/IoReadFull.lean`, a local copy of Perennial
     branch `readatleast-prefix`'s fixed ReadAtLeast/ReadFull specs and proofs** (Perennial gap, review C1,
     recorded in `notes/perennial-changes.md`); each read's `recvTokL` turned into `recvTok` by a later
     credit (`wp_apply (lc := 1)`, `lc_fupd_elim_later`); NewReader/NewWriter on the conn as above.
   These sections need `[field_sem : net.FieldAssumptions]` (as paxos's): a section variable, so a
   premise of the statement, like paxos's.
   - `replica/New` (the store's assumptions as section binders; the lab's `addrTok` premise dropped);
     **`replica.defs`' package fact is now `LatencyConf ↦□ ""`** (`Base.lean`; gen-init `finish` step in
     `etc/dsv/epaxos.py`; `gen-init.py --check` passes), read by `New`.
   - `replica/Dial` (`serveConnDial`, as ServeConn), `replica/WaitPeers` (`Listen.spec_addrOk
     Listen.wp_proof` with `listen_au` from the address's `addrProto`, `addrTok_ok`/`addrProto_tok` for
     the valid address; **`waitForPeerConnections.specX` no longer takes `addrTok`**; the loop keeps
     `netLis`; Accept as WaitClients), `replica/ConnectGhost` (port output, checks).
   - **`replica/Connect` (done, 2026-11-23 resumed agent 2)**: dial by `net.Dial.wp_proof` + `dial_au`,
     handshake by `net.Conn.Write.wp_proof` + `write_acc`/`writeP_init`, `PutUint32` by Perennial's
     `encoding.binary.wp_LittleEndian_PutUint32` (`Results`); `Interface/Registry`'s `repFwStart` map
     is now `GMap Loc Nat` (cids `Nat`, as `fwCoreDef`). **`replica/Link` (done)**: the replica package
     closed (`#print axioms` of `ConnectToPeers`/`WaitForClientConnections`/`New.wp_proof`: Lean's three).
     **`TCPAddrStringHyp` is proved** (`tcpAddrString` in `replica/ClientListener.lean`, from
     `wp_net_AnyString`, as dsv-swiftpaxos's `net.wp_TCPAddr_String`): no longer a premise.
     **lean-check caveat:** after many incremental edits of `Connect` the server reported a bogus
     `(kernel) application type mismatch` (`spec_holds._proof_1_N` applied to the wrong fvars); `lake
     build` of the module was clean. When a kernel error looks like that, `lake build` the module.
   Then (2) `Interface/{RpcPure,Rpc,MasterSpec,Servers}` over models-rpc-server
   (decode guards: `callfix.txt`/`srvfix.txt` in the coordinator's scratchpad) and `RpcHttpHyp`; (3) the
   epaxos code proofs (`Epaxos/Proof/epaxos`, 71 files, 24k lines) and the codec; (4) the model proof,
   mains, `epaxos_remote_robust`, TCB baseline.
   Recipes that recur (for the rest of the port): a bufio reader/writer built by a spec with `_`
   arguments comes back in unfolded form (`ownBufReader … (prIface pr) … (prI …)`), one taken from a
   loop invariant in `rdOwn`/`wrOwn` form; lemmas need both forms (`connRd_fact`/`connRd_fact'`,
   `rd_clientU`/`rd_client`), framing between them by `simp only [rdOwn, wrOwn, connRd, connWr, prRd]`
   first. `wp_auto` stops at float64 ops (`wp_float64_*`) and leaves `if decide True = true then …`
   after a method resolution on an interface (`try simp only [decide_true, ↓reduceIte]`). The type
   inequalities NewReader/NewWriter ask: `unfold X.ty Y.ty; simp` after `go.GoType.PointerType.injEq`.
   - **port.py** has three layers: `conv` (renames), `generic_conv` (every port: section headers,
     `(GF := GF)` on spec statements, spec hypotheses `(hP : X.spec)` and `have h := thm γ …`,
     `Dsv.` names, unseal equations, `clientN` → `epEop` masks, `[net.model.Assumptions]` →
     `[HasExt netExt] [π : NetProtoGS]` (plus the store's assumptions where `isState` occurs),
     `Epaxos.GeneratedProof` → `Dsverify.GeneratedProof`), after FIXUPS `net.rpc.connIface` → `connIf`,
     `bufio_conv` (`--bufio`: the marshal layer's call sites only; it drops `iframe He…` lines,
     so never use it outside `wire/`), then `gf_annotate` and `FIXUPS`. Re-running it on every
     file ported this session reproduces the tree (checked 2026-11-23), except the hand-maintained
     files named in its docstring.
3i. **The epaxos package's code proofs (2026-11-23, resumed agent 2): ported, all check.**
   `Interface/EpaxosRep` and the lab's 48 remaining `Proof/epaxos/*` files (order:
   `scratchpad/eporder.txt`, i.e. the import topological order) are `port.py`'s output, no hand
   edits. **The lab's `Proof/epaxos/Base.lean` is `epaxos/EpBase.lean`** (`epaxos/Base.lean` is the
   package fact). New `port.py` rules: `[examples.epaxosnet.Assumptions]` → `[epaxos.Assumptions]`
   (and `EpaxosRep` no longer imports the kit's `Server`), the store's assumptions + `TreemapHyp`
   wherever the lab had `examples.epaxosnet.Assumptions`, `connFreshG_excl _ cn s` →
   `connFresh_excl (Gg := G) cn s`, `(GF := GF)` on: spec conclusions `theorem X : Y.specZ :=`,
   `{{ pkgInit_X`, `{{ <ghost pred>`, `have h : …` statements (incl. `· have`), the kit's own spec
   `Prop`s after `:` (`HandlerSpec`, `ProposeSpec`, `ExecuteCommandsSpecX`, …, collected from
   `def/structure XSpec…`), pattern-matching defs counted as ghost predicates; a file-level
   `variable [GooseExts]` when pure declarations over the code's types precede the first section;
   `omit … [net.model.Assumptions]` → the Net variables; FIXUPS for `EpaxosRep` (`efld` over the
   local context, as `fld`), `HCtx`, `Slot`, `New` (no `addrTok`). `epaxos.New`'s theorem is
   `wp_New_of` (premises: the replica specs, `HandlerSpecs`, `ExecuteCommandsSpec`, `CmdStringSpec`).
   Not yet: the lab's `Interface/Epaxos.lean` (it closes these premises: imports `replica.Link`,
   `wire.Link`, `ExecuteCommandsProof`, `HandlePropose`, the kit's `Server` and `rpcmaster.ReplicaRcvr`).
3d. **`Interface/Misc.lean`** (dlog's non-verbose `Println`/`Printf`/`Fatal`, config's
   `IsProxy` on an empty `ProxyInfo`) and its proofs `wire/Misc/{Dlog,IsProxy}.lean`: ported, check
   with 0 errors (2026-11-23). The lab's import of `Top/PkgState` is dropped (not needed).
4. **Not started:** the rest of the model layer's bridge to remote and the kit's model (the lab's
   `Interface/*` beyond `Wire`: they are stated over the lab's harness `EpaxosNetSpec`, the
   `netConnExts` world and its `kvScan` escrow; here they must be restated over `Net/`'s specs and
   `Proto.lean`'s laws and the kit's set-of-configurations model), the code proofs
   (`Epaxos/Proof/**`, ~40k lines), the model proof (Go `step` vs the set semantics, as paxos's
   `ModelSet`/`ModelProof`), `epaxos_remote_robust`.

## Hypotheses

**Linking check (VR's finding 7, 2026-11-23):** the kit's Go has no `init()` function (`grep`), and
every program (`go list -deps ./cmd/server2`, and the 17 `PkgTable`s) links all eight fork packages
(`config dlog state replica/defs rpc replica epaxos master`): the package facts the proofs use
(`epaxos`' `errVarintOverflow`, `deferMap`, `LatencyConf`: package variables, no hooks) are of
linked packages. No vacuous premise of this kind.

- `BufWriterNotNull`: discharged (3h).
- `TCPAddrStringHyp`: discharged (`tcpAddrString`, 3h).

Stated in Lean (no axiom, no `sorry`; each a `Prop` class taken as an instance by every theorem
that needs it):

- `net.rpc.InitHyp GF` (`Dsverify/Proof/net/rpc/Init.lean`): net/rpc's initializer.
- `net.http.InitHyp GF` (`Dsverify/Proof/net/http/Init.lean`): net/http's initializer.
- `encoding.json.InitHyp GF` (`Dsverify/Proof/encoding/json/Init.lean`, dsv-vr's): encoding/json's.

- `RpcHttpHyp GF` (`Interface/RpcHttpHyps.lean`, 2026-11-23): net/rpc over HTTP with Upamanyu's
  names and shapes (#24): abstract `rpcAddrP W a hs hsAns` (`rpcAddrP_raw`: `[] []` is `Net/`'s
  `rpcAddr`), `handlerOk`, `muxHas`, `defaultServer`; concrete `connectReq path`, `connectAns`,
  `defaultRPCPath`; specs `DialHTTPPath_spec`, `DialHTTP_spec`, `Server_ServeHTTP_spec`,
  `Server_HandleHTTP_spec`, `HandleHTTP_spec`, `Register_spec` (package-level, `DefaultServer`),
  `ServeMux_ServeHTTP_spec`, `Serve_spec` (handler nil). The handshake is in the protocol, so the
  class is true of the model. `ListenAndServe` not stated (the kit does not call it). To be
  discharged by `models-rpc-http`; a visible premise of `epaxos_remote_robust`, never an instance.
  Field names use `_spec` (`DialHTTP_spec` for Upamanyu's `rpc.DialHTTP.spec`): rename to his
  `def …spec` names when his branch lands.
- `TreemapHyp GF` (`Interface/Treemap.lean`): gods' treemap (above). **Audit against real gods
  (rabia review lessons, 2026-11-23):** `isTreeMap m M` is exclusive and only `NewWith_spec` creates
  it (so `m` is non-nil and the comparator is `state.KeyComparator`, a total order on `int64` keys);
  `Put`/`Get` take `keyIface`/`valIface` (a `state.Key`, a `state.Value`: no comparator panic on a
  foreign key type); `Select` needs `f`'s triple; `Iterator` consumes the map's ownership (no
  modification while iterating); `Next`/`Value` need `ownIter`. No spec holds where Go panics or
  races. The `InitHyp`s assert only that the initializer runs (package fact `True`).

To be stated when the code proofs reach them (the library specs below, named after the lab's):

(The coordinator's instruction, 2026-11-23: state each as a hypothesis named after the lab's spec,
list it here, do not widen shared translations or add models.)

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
   nothing proves the rest. The lab used a cut-down copy with its own proof. dsv-tpmodels is
   building a gods treemap model; until then treemap's specs are hypotheses (the coordinator).
5. Also used, with specs to check before the port: `log` (`Logger.Printf`/`Println`/`Fatal`,
   through dlog), `encoding/json` (names only; the replica's latency config, never read: `LatencyConf` ""),
   `sort`, `math`, `strconv`, `fmt.Sprintf` (the master), `time`, `os`.

**bufio (coordinator, 2026-11-23):** the shared change is `origin/dsv-bufio` (`bb18c0f3ef`, in
review; `/shared/etcd-grove-dsvbufio/notes/dsv-bufio.md`). Use its names (or merge it): namespace
`Perennial.EtcdGrove`: `bufio.NewReaderSize.spec`, `NewReader.specOk`, `Reader.Read.specOk`,
`Reader.ReadByte.spec`, `NewWriterSize.spec`, `NewWriter.spec`, `Writer.Flush.spec`,
`Writer.Write.spec`, `Writer.WriteByte.spec` over `ownBufReader`/`ownBufWriter` with contracts
`io.readerOk`/`io.streamWriterOk`; law `ownBufReader_readerOk` (Perennial's `io.wp_ReadFull`/`ReadAtLeast`
through bufio); `Net/Proof/net/ConnIo.lean`: `conn_readerOk`, `conn_writerOk` (needs
`ProtoPrefixClosed P`). The lab's `Interface/BufioLocal.lean`, `Proof/wire/BufioSticky` and
`Harness/Proof/bufio/*` are replaced by these, not ported.

## RPC layer: shapes to use (coordinator, 2026-11-23, for step (2))

- **models-rpc-http** (`1a4d9546c9`, stacked on models-rpc-server, not landed): `rpcAddrP W a hs hsAns`,
  `rpcAddr W a := rpcAddrP W a [] []`, handshake per address (`W.hs a`, `W.hsAns a`);
  `rpc.DialHTTPPath.spec`/`rpc.DialHTTP.spec` proved over `http.ReadResponse.spec` (stated, proof in
  progress). Merge it and use its DialHTTP(Path) specs in place of `RpcHttpHyp`'s client fields; keep
  the server fields (`ServeHTTP`, `HandleHTTP`, `http.Serve`, `ServeMux`) until that part lands.
  Not merged yet (it regenerates `Net/GeneratedProof/net/http`: merge right before the RPC work).
- Upamanyu's five answers (#24; text `scratchpad/five-answers-24.txt`): wildcard listeners (the
  master's `":%d"`) get `rpcLisP W la hs hsAns` (`rpcAddrP` its instance at an exact address; names
  `rpcLisP_addr`/`_lis`/`_set`; dsv-swiftpaxos's `lib/RpcHttpHyps.lean` has the hypothesis shape);
  `errOk` will cover only the server's own errors (`srvErrMsg m`); `Client.Call`'s other errors give
  `∃ msg, errMsg err msg ∗ ⌜msg ≠ []⌝`; net/rpc's `codecFresh`/`srvEnv` come from a per-machine boot
  resource returned by `wp_initialize'` (never `|==> codecFresh`). Keep the open points (callRet
  errMsg, codecFresh, errOk, wildcard listeners) as visible premises.
- Templates: dsv-craq (`Craq/{Codec,CodecSrv,HttpRpc,Netrpc/*}`: rpcgen codec, net/rpc over HTTP),
  dsv-rabia (top level: `TopLevelDefs`/`TopLevelRobustness`, remote's `ServeClient` with a Mutex in
  the kit's `Sys`).

## Import tiers (etc/tier-check.py, a land gate)

2026-11-23: `etc/tier-check.py --check` reports **34 new violations, all `defs->proof`**: the kit's
proof files are named `<F>.spec_holds` (so tier "defs") and import library proof modules to call
their `wp_proof`s directly (`Proof.bufio.{Writer__Flush,Writer__WriteByte,NewReaderOk,...}`,
`Net.Proof.net.{Conn__Read,Conn__Write,Conn__Close,Dial,...}`, in `replica/*` and `wire/{WProg,RProg,
Varint/ReadUvarint}`). To fix at landing: import the libraries' `Spec` modules, take their specs as
hypotheses of `spec_holds`, and close them in the `Link` modules (which may import proofs). New files
follow the rule (a proof file sees callees through their specs only).

## Next (for a successor)

**State (2026-11-23, resumed agent 3):** **Merged `origin/lean` `c4e044df92`** (models-rpc-server
landed; Perennial **`c95e92207`**: `.lake/package-overrides.json` points at
`/shared/perennial-c95e92207`, `PERENNIAL_DIR` likewise; the build seeded by `rsync` from
`/shared/etcd-grove-dsvrabia/.lake/build` without `Dsverify/`; `gen-init.py --check` (268 up to
date) and `goose.py --check --project dsv-epaxos` pass; `lake build` of `replica.Link`,
`epaxos.Link` green, 2716 jobs). `etc/goose.py`/`etc/gen-init.py` equal lean's. models-rpc-http
NOT merged (its `DialHTTPPath` proof fails on lean's bufio, #24): `RpcHttpHyp` keeps the client
fields. `epaxos.New`'s spec now asks `c.Port' = 7500 + k` (the kit's port; was the lab's 7000 + k,
unused by the proof).

**The RPC layer's interfaces (committed `767e410a99`, all check):** `NetRpc/Wire.lean` (rpcgen's
bytes as pure encoders `encRegisterArgs`, `encRegisterReply`, `encBtlReply`, …, namespace
`netrpcw`), `NetRpc/Codec.lean` (`epCodec : CodecSpec` from the generated functions' WPs,
`rpcReady`, `getU64`/`getTag`/`tagOk`, the clients' `CodecLaws`), `NetRpc/CodecSrv.lean`
(`SrvCodecLaws`, `ArgFacts`, `decLen.spec`), `NetRpc/Methods.lean` (the services over rpcgen's
bytes: `registerSpec` (`regReplyOk γ k id nl ready`), `masterSvc`, `btlSpec`, `pingSpec`,
`replicaSvc`, `rpcSS`; each method spec also takes any error answer (`∧ errAns Φ`), so
`masterSvc_errOk`/`replicaSvc_errOk` prove Net's current `errOk`: no F3-like premise here;
`portOf k = 7500 + k`, `regArgsOf`, `replicaRpcAddrs_lit`), `NetRpc/Specs.lean` (the parts'
interfaces: `btlCall.spec`, `pingCall.spec`, `registerCall.spec` (args `↦□`, reused across
calls); the bodies `masterRegister/GetLeader/GetReplicaList.spec`, `replicaBtl/Ping.spec` over an
abstract handle; the receivers `masterRcv.spec`, `replicaRcv.spec`). **`RpcHttpHyp` revised**
(`Interface/RpcHttpHyps.lean`, premise truthfulness): `rpcLisP` (+`_addr`, `_lis`, `_set`; the
master's wildcard `":7501"`), `muxOwner R` in `HandleHTTP_spec` (a second `http.Handle` of a
path panics), `Serve_spec` over a listener at `la` (`netLisOn`, `lisInv`); dropped the unused
`handlerOk`, `Server_ServeHTTP_spec`, `Server_HandleHTTP_spec`, `ServeMux_ServeHTTP_spec`.

**Design finding (Net/remote): the master's wildcard listener at the top level.** `Run` listens
on `":7501"`; its `lisProto`/`rpcLisP` come from `lisUnset ":7501"`, which only
`addrs_lis_start` (`GooseLang/Ext/Net/Proto.lean`) gives; `robust_of_distProtoRB`
(`Net/Statement/DistBridge.lean`) uses `addrs_start` (addresses only). Plan: a local copy of the
bridge over `addrs_lis_start` (`robust_of_distProtoLisRB addrs las`, `las = [":7501"]`, the kit's
address list without `127.0.0.1:7501`, which the wildcard takes), proved from Net's lemmas, in the
kit's `TopLevelRobustness`; Net could offer it.

**Work in flight (2026-11-23, four subagents of agent 3, disjoint files; their reports go to the
next notes update):** (A1) `NetRpc/CodecProof.lean` (`epCodecLaws`), `NetRpc/CodecSrvProof.lean`
(`epSrvCodecLaws`, `epArgFacts`, `epDecLen`), after craq's; (A2) `NetRpc/Calls.lean`
(`btlCall`/`pingCall`/`registerCall` from Net's `Client.Call.spec` + `CodecLaws`),
`NetRpc/Bindings.lean` (`masterRcv`/`replicaRcv` from the bodies + `SrvCodecLaws`),
`epaxos/Rpc.lean` (`replicaBtl`/`replicaPing` for `isReplica`, the lab's `wp_BeTheLeader`/`wp_Ping`);
(B) `master/{Defs,New,Register,GetLeader,GetReplicaList,run,Run,Link}.lean` (the lab's
`Interface/MasterSpec.lean` ported, over `NetRpc/Specs` and `RpcHttpHyp`); (C)
`examples/epaxosnet/{Kit,ModelSet,ModelDefs,ModelProof,KitProof}.lean` (remote's `RBase` `epR γ`
over `own_state`/`epEop`/`kvStep`, `lin_opU`, the set semantics of model.go, `Model`/`Codec`/`Gen`
specs and proofs; outputs collide on the wire (`Out{V:""}`): craq's F4 fix).
**Kit Go change (2026-11-23, `6fe689ecc4`): `model.go`'s `Equal` is always false** (the `equal`
function removed; retranslated; `go test ./examples/epaxosnet/` passes). Subagent C's finding: two
histories (put a unknown, put b ok) vs (put b ok, put a unknown) on one key reach the same Go
`State` whose exact sets of configurations differ (only the first allows "a fired before b"), so
no `rep` meets porcupine's `equalSpec` with the old `equal`; porcupine's verdicts were right. The
proof relates a Go state to its set up to pending puts that never fire (dsv-craq's `Sim`, P2).
**Done by agent 3 itself:** `examples/epaxosnet/KitVals.lean` (`inOf`, `outBytes`, `outOk`,
`outUnk`: the kit's `In`/`Out` values, shared by the model and `Op`), `ServerDefs.lean`
(`codecFresh`, `wp_Register` over Net's `SetCodec.spec`, `register.spec`), `Register.lean`
(`register.wp_proof`, from `DialHTTP_spec`, `registerCall.spec`, `Client.Close.spec`,
`regX_claim`; checks). (E) a fifth subagent: `examples/epaxosnet/{OpDefs,OpProof}.lean` (`Op.spec`:
`{{ isPkgInit kit ∗ sl ↦*□ serverAddrs ∗ clientInvs γ ∗ opU γ i Φ }} Op sl c (inOf i) {{ o; o =
outUnk ∨ ∃ r, o = outOk r ∗ Φ r }}`, the lab's `OpCore` ported).
**Still to do after the subagents:** `serve`'s replica branch (`nodeConfig`, `host`, `itoa` (a
generic loop spec, `itoa (8500+k)` = `fmt.decimal`), `epaxos.New` (`EpaxosNewSpecEp`),
`rpc.Register`+`replicaRcv`, `HandleHTTP`, `net.Listen` at `rpcAddrOf k` (`rpcLisP_lis`,
`listen_lis_au`, `lisInv_alloc`), `http.Serve`), the master branch (`master.New`, `Run` from B),
`Server`, `Client` (`remote.ServeClient` with `newClient` returning the address slice: `tok sys`
persistent; `first` in an invariant), `Orch` (`remote.Check`), the `Mains`, the start (the lab's
`Top/Start.lean`: `registry_alloc`, `regXInv_alloc`, the protocol invariant, `clientInvs`, the rpc
world `W` with `W.SS = rpcSS γ` and `rpcLisP_set` at `":7501"` and each `rpcAddrOf k`), the local
bridge `robust_of_distProtoLisRB`, `TopLevelDefs`, `TopLevelRobustness`, the statement, TCB.
**Done and built (2026-11-23, agent 3 and its subagents; `lake build` green on each, Lean's
three axioms where printed):** `NetRpc/CodecProof` (`epCodecLaws`), `NetRpc/CodecSrvProof`
(`epSrvCodecLaws`, `epArgFacts`, `epDecLen`), `NetRpc/Calls` (`btlCall_holds`, `pingCall_holds`,
`registerCall_holds` from Net's `Client.Call.spec` + `CodecLaws`), `NetRpc/Bindings`
(`masterRcv_holds`, `replicaRcv_holds`), `epaxos/Rpc` (`replicaBtl_holds` (dlog Println premise),
`replicaPing_holds`), `master/{Defs,New,Register,GetLeader,GetReplicaList,BtlReply,RunLoop,Run,Link}`
(`master.wp_Run hBtl hPing γ W hRcv : Master.Run.specM γ W`; pre: `isPkgInit master ∗ isPkgInit
net.http ∗ masterFresh ∗ listUnset γ ∗ ⌜W.SS = rpcSS γ⌝ ∗ rpcLisP W ":7501" … ∗ replicaRpcs W ∗
muxOwner [] ∗ rpcReady ∗ srvEnv ∗ bounds`), `examples/epaxosnet/{OpDefs,OpProof}` (`Op.wp_proof`;
11 callee-spec premises: NIL, Marshal, Unmarshal, DialTimeout, Conn.Read/Write/Close, bufio
NewWriter/NewReader/WriteByte/Flush), `ServerDefs`/`Register` (`register.wp_proof`),
`ServeDefs`/`ServeHelpers`/`ServeReplica` (`serveReplica.wp_proof`; `epaxosNew.spec` is a copy of
`EpaxosNewSpecEp`, which lives in the linking module `epaxos/Link`: move it to `epaxos/New` to
drop the copy), `Bridge` (`robust_of_distProtoLisRB`), `Start` (`ep_ghost_start`, `ep_start` over
`GooseGlobalGS` + `RpcHttpAddr`: `∃ γ W, ⌜W.SS = rpcSS γ⌝ ∗ own_state γ init ∗ masterRes γ W ∗
[∗list] k, replicaRes γ W k ∗ □ clientInvs γ`, addresses `epStartAddrs` (replica peer + rpc),
`epLas = [":7501"]`, `addrUnset_lisUnset`). Statement changes on the way: `masterRcv`/`replicaRcv`
take `codecSet epCodec`; `GetLeader`/`GetReplicaList`'s specs pin their argument bytes;
`btlCall`'s error branch keeps the reply (`dec_BtlReply` fails only on non-encodings);
`epaxos.New` returns `r ≠ null`. **`RpcHttpHyp` split** (`6cc1565d9a`): `RpcHttpAddr GF` over
`GooseGlobalGS` (`rpcAddrP`, `rpcLisP` + laws: the same at every machine) and `RpcHttpHyp GF`
(per heap, `[RpcHttpAddr GF]`). (C) `examples/epaxosnet/Kit.lean` (`epR γ : RBase GF KvS EIn
BStr`, `EIn = {i // inPre i}`, `BStr` bounded strings, `lin_opU : lin (epR γ) i Φ ⊢ opU γ i.1
(fun o => Φ (bnd (outBytes o)))`), `ModelSet`: in progress (uncommitted while C runs).
**Remaining:** C's ModelDefs/ModelProof/KitProof; `Server` (master branch: `wp_Register`,
`nodeConfig`, `master.New`, `Run`; replica branch: `serveReplica`), `Client`
(`remote.ServeClient`; `newClient` returns the address slice; `Op`'s outputs need
`(outBytes r).length < 2^63 - 1` for `epR_ov`), `Orch` (`remote.Check`), `Mains`, `TopLevelDefs`,
`TopLevelRobustness` (bridge `robust_of_distProtoLisRB epAddrs epLas`, `ep_start`, remote's
client-address protocols and `pend_alloc`/`mapCtx_alloc` as paxos; per-machine boot `RpcBoot`
giving `codecFresh ∗ invalidRequest ↦□ () ∗ muxOwner []` as craq's), the statement with every
premise visible, `etc/theorem-loc.py`, TCB, tier-check.
If a subagent's files are present but uncommitted, check them (`etc/lean-check.py -a -q`) and
commit what checks.

**Next, in order:**
1. **Merge** `origin/lean` (now `c4e044df92`: models-rpc-server LANDED, Perennial `c95e92207`:
   repoint `.lake/package-overrides.json` and `PERENNIAL_DIR` to `/shared/perennial-c95e92207`, reseed
   the build, regenerate the `PkgTable`s with `etc/gen-init.py`, rebuild `replica.Link`/`epaxos.Link`)
   and `origin/models-rpc-http` (client side of net/rpc over HTTP; see "RPC layer: shapes to use").
2. **The RPC layer** (the lab's `Interface/{RpcPure,Rpc,MasterSpec,Servers}`, `Proof/rpcmaster/*`,
   `Proof/codec/*`): restate over rpcgen's codec (`examples/epaxosnet/rpc_gen.go`, net/rpc's
   `CodecSpec` in `Net/Proof/net/rpc/Codec.lean`) following dsv-craq (`Craq/{Codec,CodecProof,
   CodecSrv,CodecSrvProof,HttpRpc,Methods}`): the lab's kitgen codec proofs (`Proof/codec`, `Rpc.lean`'s
   `wp_rpcEncode_*`/`wp_rpcDecode_*`) are replaced, not ported. The methods: master `Register`,
   `GetLeader`, `GetReplicaList`; replica `BeTheLeader`, `Ping` (the rest of the lab's
   `Interface/Epaxos.lean`: `wp_BeTheLeader`, `wp_Ping`, `rcvr_ok`). The decode guards (`argDec`
   on the server, `Client.Call`'s guard) are models-rpc-server's. The master listens on `":7501"`:
   `rpcLisP` (wildcard). `RpcHttpHyp`'s client fields → models-rpc-http's `DialHTTP(Path)` specs; keep
   the server fields as visible premises.
3. **The kit** (`examples/epaxosnet`: `Gen`, `Op`, `serve`/`Server`, `Orch`, `Client`; the lab's
   `Proof/examples/epaxosnet/*`, `Top/*`) onto remote, as dsv-rabia (`TopLevelDefs`,
   `TopLevelRobustness`, the kit's `Sys` with a Mutex for `ServeClient`) and dsv-paxos; the model proof
   (Go `step` vs the set-of-configurations semantics, `ModelSet`/`ModelProof` of paxos); the mains;
   `epaxos_remote_robust` with every `[<pkg>.InitHyp GF]`, `[TreemapHyp GF]`, `RpcHttpHyp`, the
   net/rpc open points (codecFresh as a per-machine boot resource, errOk/srvErrMsg, errMsg) as
   visible premises (`etc/theorem-loc.py`); the TCB baseline.
4. The tier restructuring (34 violations) before landing.

Library pieces (older notes, still accurate where not superseded above):

0. **Wildcard listen (coordinator, 2026-11-23): `net-wildcard-listen` LANDED on `lean`
   (`1b2fd95b30`, with the Perennial pin bump to `7b2259a12`, `/shared/perennial-7b2259a12`).**
   The master listens on `":%d"` (`master/master.go:72`), a wildcard: its code proof needs
   `Listen.spec` with `listenOk` and `Listener.Accept.spec` with `lisAccepts`
   (`Net/Proof/net/AtAddr.lean`; laws `lisProto`, `listen_lis_au`, `accept_lis_au`, … in
   `Proto.lean`). Not merged yet (deliberately: the pin bump invalidates the build seeded from
   9c3b81f30, so merge `origin/lean` right before the master's code proof, then point
   `.lake/package-overrides.json` and `PERENNIAL_DIR` at `/shared/perennial-7b2259a12`). The
   replicas listen on their full peer address (`replica.go:393`) and the kit's server on
   `ip:port` (`kit.go:267`): the old shapes (`Listen.spec_addrOk`) serve them.

1. **bufio (the marshal layer): DONE** (3g above).
2. **net/rpc over HTTP** (the master and the replicas: `rpc.Register` on `DefaultServer`,
   `rpc.HandleHTTP`, `http.Serve(l, nil)`, `rpc.DialHTTP`). `origin/models-rpc-server` (merged
   here) proves `NewServer`, `Server.Register(Name)`, `ServeConn`/`ServeCodec`, `Accept`, `Dial`,
   the client, the codecs; not `DialHTTP`/`DialHTTPPath`, `HandleHTTP`, `ServeHTTP`, the
   package-level `Register` (DefaultServer), nor net/http's `Serve`. The coordinator (2026-11-23):
   do **not** change the fork's Go to avoid HTTP (an attempt to serve with `rpc.NewServer` +
   `Accept` and dial with `rpc.Dial` was reverted, never committed); a hypothesis for `DialHTTP`
   must use a protocol of the handshake (`"CONNECT /_goRPC_ HTTP/1.0\n\n"`, then
   ServeHTTP's response) followed by frames: the model's `isClient` over `rpcAddr` (frames from
   byte 0) is false of it. Name such hypotheses after the plan's phase 5.2 specs
   (`notes/dsverify-net-port-plan.md` on origin/lean, ~580-725); the coordinator asked Upamanyu on
   #24 for that `Net/` piece. **Upamanyu's intended shapes (#24, 2026-11-23; branch
   `models-rpc-http`, stacked on models-rpc-server, next after the wildcard listen, no date):**
   `rpcAddrP a hs …` (client-to-server bytes `hs ++ reqsWire`, server-to-client `hsAns ++
   ansWire`; raw net/rpc is `rpcAddrP a [] []`; over HTTP `hs := connectReq path`, `hsAns` =
   `HTTP/1.0 200 Connected to Go RPC\n\n`; `isClient` unchanged, over the frame part);
   `rpc.DialHTTPPath.spec network addr path`, `rpc.DialHTTP.spec` (at `DefaultRPCPath`);
   `rpc.Server.ServeHTTP.spec` (a net/http handler: on CONNECT hijack, write `hsAns`, `ServeConn`
   on the frames; else 405); `rpc.Server.HandleHTTP.spec rpcPath debugPath`, `rpc.HandleHTTP.spec`
   (the debug path never requested); `http.ListenAndServe.spec`, `http.Serve.spec`,
   `ServeMux.ServeHTTP.spec` (handlers as `handlerOk` per path). Any hypothesis here must match
   these names and shapes exactly. The kit's clients (the master's `DialHTTP` to the replicas,
   `register`'s to the master) send nothing after CONNECT before the answer, as required.
3. **gods' treemap**: `TreemapHyp` (above) until a spec of `models/gods` is proved.

Then: the lab's `Interface/{Rpc,RpcPure,RpcTable,Registry,MasterSpec,Replica,ReplicaSpec,
Epaxos,EpaxosGhost,EpaxosRep,ClientSpec,Servers}` restated over `Net/`'s specs (`Net/Spec/net/*`,
`Net/Spec/net/rpc/*`) and `Proto.lean`'s laws; the code proofs (`Proof/{epaxos,replica,codec,
rpcmaster,examples/epaxosnet,init}`, ~38k lines; `codec` is replaced by rpcgen's codec, whose
proof is models-rpc-server's `Codec`); the kit's model proof (Go `step` vs the set semantics, as
paxos's `ModelSet`/`ModelProof`); the mains/links; `epaxos_remote_robust` in
`Dsverify/Spec/.../epaxosnet/TopLevelRobustness.lean` with every `[<pkg>.InitHyp GF]`
(`encoding.json`, `net.rpc`, `net.http`) and `[TreemapHyp GF]` as visible premises of its
`.spec` (etc/dsv/README.md; never an `instance`); confirm `etc/theorem-loc.py` counts them; the
TCB baseline `etc/tcb-collections/dsv-epaxos.txt` (still the roots and an empty baseline).

Edit loop: `export PATH=$HOME/.elan/bin:$PATH` (lake is not on the default PATH here), then
`etc/lean-check.py -a -q FILE`; `etc/gen-init.py --check` needs
`PERENNIAL_DIR=/shared/perennial-7b2259a12` (the worktree has no `.lake/packages`).
