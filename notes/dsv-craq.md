# dsv-craq: dsverify-lab's craq kit on the net extension (phase 6)

Branch `dsv-craq` (2026-11-23), off `dsv-paxos` (`e3eaf5cd0d`) with `origin/lean` merged (the net/rpc
client's proofs). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/craq/` (run **`craq-bump-1`**: proof `d9f172f` tag
`final`, fork `a0238ac`, Perennial `3afd77e35`; read only, nothing in the lab changed).

**State in one line (2026-11-23, third agent: see P4 for the current state; the line below is the first agent's):** the Go and its translation are done and tested;
the lab's protocol proof is ported and built (`Store`, `Kv/`, `Protocol/`, `Wire`, `Methods`,
`Iface`, `Codec`, `Specs`, `Netrpc/`, `Node/`, `Coord/`: `lake build` of the leaves `Coord.All`,
`Node.Svc`, `Netrpc.New`, `Kv.New`, `Protocol.All` green); what remains is the kit (the lab's `Kit/`,
rewritten onto remote as paxos's `Kit`/`KitProof`/`ModelSet`/`ModelProof`/`Mains`), the statement
`craq_remote_robust`, and the hypotheses below. **Design finding (blocks a non-vacuous statement):
H4 as stated (`DialHTTP` giving Net's `isClient` over `rpcAddr`) is false of the model's
`DialHTTPPath`** (see H4 below): rpc over HTTP needs a shared Net piece, or the kit moves to plain
net/rpc (`rpc.Dial`, `Server.Accept`).

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/craq/` (module `github.com/despreston/go-craq`, the fork's path): the fork's `transport`, `transport/netrpc`, `store`, `store/kv`, `store/storetest`, `node`, `coordinator` (unchanged but below), and the kit `examples/craqnet` (rewritten onto `examples/lib/remote`) with its 12 commands `cmd/{orch,client0..4,server1..6}` |
| the kit's net/rpc codec | `examples/craqnet/rpc.toml` → `rpc_gen.go`, `rpc_model_gen.go`, `rpc_real_gen.go`, `rpc_gen_test.go` by `models/net/rpc/rpcgen.py` (18 types, 2 receivers, 13 methods); `rpc_stub.go` (tag `rpcgen`, never built) keeps `models.lab/rpcdesc` in `go.mod` for the generator |
| translation | `etc/goose.py` project `dsv-craq` into the part `Dsverify/` (`std_models` net/rpc, net/http: the models' sources), `Dsverify/{Code,GeneratedProof}/github_com/despreston/go_craq/**`; `Dsverify/Code/.../store.toml` leaves out `store.Encode`/`DecodeMany` (gob; only the bolt store, not ported, calls them) |
| package facts | `Dsverify/Proof/github_com/despreston/go_craq/**/Base.lean` (hand-written: `store`, `node`, `coordinator` are their `errors.newVar`s, as the lab's `PkgState.lean`; the rest `True`) |
| initializers | `etc/gen-init.py` (the block after `DSV_PROGRAMS`, before `dsv_inits`): `transport`, `store`, `store/kv`, `node`, `coordinator` (`Init.lean`, built). Not `transport/netrpc`, `examples/craqnet`, the commands (their closure reaches net/rpc's and net/http's initializers: hypothesis H1) |
| the proof | `Dsverify/Proof/github_com/despreston/go_craq/Craq/`: the lab's `Craq/Proof/` tree, ported by editing. Ported and built: `Store`, `Kv/`, `Protocol.lean` + `Protocol/` (P1 done), `Wire`, `Methods`, `Iface`, `Codec` (H5), `Hyps` (H4), `LogHyp` (H6), `Specs`, `Netrpc/`, `Node/`, `Coord/`. Not yet: the lab's `Kit/`, `Link`, `Top` (rewritten onto remote) |
| the kit (in progress) | `Dsverify/Proof/github_com/despreston/go_craq/examples/craqnet/`: `ModelSet.lean` (pure: the store `kvB`, the bracket `Sim`, `sim_init`, `sim_step`; done), `Kit.lean` (the store `kvR γ` over the protocol's `ownState`, `lin_opAU`, the model spec `kvS0`/`kvS`, the addresses; done). Not yet: `ModelProof`, `KitProof`, `Mains`, the statement |
| porting aid | `Dsverify/Proof/github_com/despreston/go_craq/Craq/wip/port.py SRC DST PKGS` (the mechanical edits of a lab file: imports, opens, section variables; used for `Kv/`) |

Build: `lake build Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.Write` (and the `Init`
modules) green on Perennial `9c3b81f3`. A worktree needs `.lake/package-overrides.json` pointing at a
built Perennial of the pin (this one: `/shared/perennial-9c3b81f30`, path entries for perennial, iris,
batteries, Qq); `etc/gen-init.py` needs `PERENNIAL_DIR=/shared/perennial-9c3b81f30`; `etc/goose.py
--perennial /shared/perennial-9c3b81f30`.

Tests (`GOWORK=off`): `go test ./...` (real net/rpc and net/http: the packages' own tests and the
kit's `TestDeployment`, 12 processes on loopback, ~2 s, `TestModel`, `TestConfCodec`); over the
models: `python3 models/goroot.py farm DIR`, then `GOROOT=DIR GOTOOLCHAIN=local PATH=DIR/bin:$PATH go
test -tags netmodel ./...` (passes; `transport/netrpc`'s own tests are real-build only, tag
`!netmodel`: in a model build net/rpc needs a program's codec, which only the kit registers).

## What changed against the lab

Go:
- **The deployment is remote's** (as paxos): the lab's own `remote.RunRemote`/`ServeClient`,
  recorder, driver and `check.KV` are replaced by `examples/lib/remote` (`remote.Check` on the
  orchestrator, `remote.ServeClient` per client machine) and porcupine against the kit's own model.
  12 machines as in the lab: orchestrator, 5 clients, coordinator, 5 chain machines; addresses
  `127.0.0.1:75xx` (`ServerAddrs` the net/rpc servers, `ClientAddrs` remote's, `ConfAddrs` the
  configuration ports).
- **The model** (`kit.go`'s `Model`): a key-value map of strings with **pending puts** (`State{M,
  Pend}`): an unknown put becomes pending, an unknown get changes nothing, a get answers the map's
  value of its key or the value of a put pending at it (which then takes effect and leaves `Pend`).
  For remote it must be the pending-writes store `linkv.PendSpec` of the map; the Go model fires a
  pending put only when a get reads it, so its state stands for a set of configurations *up to*
  pending puts that may never fire (see "Proof design", P2).
- **Inputs**: remote's generator sees the client only (`gen(c)`), so `Gen` draws a put or get of a
  random key at random (`primitive.RandomUint64`), where the lab's `Gen(c, j)` put then got round
  `j`'s key. The configuration and the removals are drawn the same way (the lab used `math/rand`).
- `Orch` sleeps `StartMs` after configuring (the lab's driver's `Start` delay; tests only).
- **`Client` makes its `Sys` before `ServeClient`** (waits for its configuration, registers the
  codec, starts its removals), and `newClient` returns it: remote's `ServeClient.spec` takes
  `newClient` as a persistent triple from `True` (paxos's finding, `notes/dsv-paxos.md`), which cannot
  own the machine's configuration listener or its one-shot ghost resources.
- The net/rpc codec is the models' `rpcgen` (gob-shaped, `Codec.Receiver` with `NewArg`/`NewReply`/
  `Call` per method), not the lab's kitgen codec (its own encoding, `Codec{Encode, Decode, Methods,
  Call, Name}`): the lab's `Codec/` and `Dispatch/` proofs (6k lines) are for the old codec.
- Dropped: `store/boltdb`, `store/mongodb` (unused; their dependencies), `node/node_stress_test.go`
  (the lab harness's models). `transport/netrpc`'s two tests got tag `!netmodel`.

Lean so far:
- `errNotFound` (the store's error) is stated over Perennial's `errors.newVar` shape (the `*errorString`
  pointer, its field, its `Error()` spec), not the lab's rpc `errMsg`: the store needs no rpc.
- The lab's `storeOwnK`/`isStoreK` (pending its hub request H-kv-1) are `Store.lean`'s `storeOwn`/
  `isStore`.
- Tactic drift (lab Perennial `3afd77e35` → `9c3b81f3`): `and_self` is ambiguous with `BI.and_self`
  (`_root_.and_self`); a range loop's `Hif` from `wp_if_destruct` can stay `#(decide P) = #true` (use
  `of_decide_eq_true (go.intoVal_inj Hif)`); range loops over slices are `slice.forRange` (the body a
  function of key and value: the lab's index-load steps no longer apply as written: see
  `Kv/ReadVersion`, not yet ported); `log.Printf.spec` (Perennial's, `fmt.ArgsWf`) replaces the lab's
  `log.wp_Printf`.

## Hypotheses (model pieces the port needs that are not proved)

Each to be a hypothesis (section variable or premise named after the lab's spec) of the statement until
the shared piece lands; none is an axiom.

- **H1. net/rpc's and net/http's package initialization**: `IsPkgInit`/`GetIsPkgInitWf` instances for
  `pkg_id.net.rpc`, `pkg_id.net.http`, and their `wp_initialize'` (plan 5.2, item 5). Now instance
  variables in `transport/netrpc/Base.lean`, `examples/craqnet/Base.lean`, the commands' `Base.lean`;
  blocks `gen-init` for those packages.
- **H2. net/rpc's server**: `origin/models-rpc-server` (040ef5e808, the whole net/rpc server on Lean's
  three axioms; not landed, waits for the human reviewer) is **merged** here (2026-11-23, the
  coordinator's decision; its statements are not expected to change). It proves the `*Server`
  methods (`Server.RegisterName.spec`, `Server.ServeConn.spec`, `Server.Accept.spec` over
  `isServer s γ`, `svcReg`, `srvServes`, `rpcAddr`, `codecSet`); its `CodecSpec` gained `rcv`
  (`Codec.lean`'s `craqCodec.rcv`, `craqCodec_rcvOk`). Still missing for craq: the **package-level**
  `rpc.RegisterName` (`DefaultServer`, a package variable: its fact needs net/rpc's `Init`, H1) and
  **`rpc.HandleHTTP`** + `(*Server).ServeHTTP` (the CONNECT hijack, then `ServeConn`).
- **H3. net/http's server**: `http.ListenAndServe(addr, nil)` with `DefaultServeMux` routing net/rpc's
  path to the `DefaultServer` (plan 5.2, item 7: `Serve`, `conn.serve` up to the hijack). Nothing in
  `Net/` yet (the lab had `Harness/Proof/net/http/{Base,Mux,Serve}.lean`).
- **H4. net/rpc over HTTP, client side: restated, true of the model (`Craq/HttpRpc.lean`), awaiting
  Net's piece.** The first statement (`DialHTTP` giving Net's `isClient` over `rpcAddr`) was false
  of the model: `DialHTTPPath` writes the CONNECT handshake before the frames, and `rpcAddr`'s
  protocols speak of frames from byte 0. Decision (coordinator, 2026-11-23): go-craq stays the
  lab's fork; Net gets rpc over HTTP (upamanyus's shapes, #24: branch `models-rpc-http`, stacked on
  `models-rpc-server`, no date; text in the coordinator's scratchpad `rpc-http-shapes.md`):
  `rpcAddrP a hs …` (client-to-server bytes `hs ++ reqsWire`, server-to-client `hsAns ++
  ansWire`; `rpcAddr = rpcAddrP a [] []`), `connectReq path`, `isClient` unchanged (over the frame
  part), `rpc.DialHTTPPath.spec`, `rpc.DialHTTP.spec`. Here, matching: class `RpcHttpAddr GF`
  (`rpcAddrP W a hs hsAns`, abstract, persistent), `connectReq`, `connectedAns`, `defaultRPCPath`,
  `httpRpcAddr W a` (at `DefaultRPCPath`), class `RpcHttpDial GF` with `rpc.DialHTTPPath.spec`
  and `rpc.DialHTTP.spec` (giving Net's `isClient`, so the client proofs `Netrpc/` keep using Net's
  proved `Client.Call`/`Close`). `craqCtx` now says every address is an `httpRpcAddr`. Every file
  with `[π : NetProtoGS]` takes `[ra : RpcHttpAddr GF]` (`Netrpc/Connect`, `New` also `[rd :
  RpcHttpDial GF]`). No instance of either class exists; they become premises of the statement.
  **The server side** (H2, H3) is stated too, in the same file: class `RpcHttpServe GF` with
  abstract `muxOwner R`, `muxRoute p h`, `handlerOk h p W a`, and the fields `RegisterName`
  (package-level, `DefaultServer`), `HandleHTTP` (Net's `rpc.HandleHTTP.spec`), `ServeHTTP`
  (Net's `rpc.Server.ServeHTTP.spec` as a handler: `isServer`, `srvServes`, `srvEnv`, `codecSet`
  give `handlerOk (serverHandler s) defaultRPCPath W a`), `ListenAndServe` (Net's
  `http.ListenAndServe.spec`, over `httpRpcAddr`). Not used yet (the kit's `Server`/`runNode`
  proofs). **Open**: a machine's `muxOwner []` (from net/http's initialization: H1, Net's piece
  decides), and the allocation of `rpcAddrP` at the deployment's addresses (the statement must
  take it with these classes, or the abstract predicates could be `False`). When Net's piece lands:
  replace `RpcHttpAddr.rpcAddrP` by Net's `rpcAddrP`, the class fields by Net's specs, and drop the
  classes.
- **H5. The generated codec and Net's `Call` spec.** `Craq/CodecProof.lean` proves the seven
  `enc_*` of `CodecLaws` (from `rpc_gen.go`'s translation). Decoding: Net's
  `net.rpc.Client.Call.spec` (`Net/Spec/net/rpc/Client__Call.lean`) asks for `□ (D -∗ ∀ rep, C.dec
  rep reply (Θ rep))`, but rpcgen's `rpcDecode` **panics** (`rpcNotModelled`, by design) when the
  reply's type tag parses but names another type, so no rpcgen codec of two or more types meets
  it. Raised on #24 (coordinator, comment 7091832079); **Upamanyu confirmed the defect and will fix
  it on `models-rpc-server`** (2026-11-23): Call's decode obligation will cover only replies the
  method's reply type can produce (what the server's codec encodes from a value of that type, as
  the protocol fixes); `decErr`'s docstring will mention the panic; a failed decode will promise
  only "some field values". He will post the new statement on #24. Here, until then:
  (1) `Codec.lean`'s `dec_*` are **restated** with the premise `tagOk t rep` (pure `getU64`,
  `getTag`, `tagOk`, `getTag_encStr`, `tagOk_tagged` in `Codec.lean`) and failure branches giving
  some field values (`∃ k v, p ↦ …`; Item `∃ k sl`; PropagateResponse `∃ mp', p ↦ mp'`; NodeMeta
  `∃ m` as before); their proofs go in `CodecProof.lean` (`craqCodecLaws : CodecLaws`; status in
  P4 (a)). (2) **`RpcCallReply GF`** (`Craq/HttpRpc.lean`, a `Prop` class, no instance): field
  `Call : rpc.Client.CallR.spec`, Net's Call spec with the obligation `□ (D -∗ ∀ rep, Φ rep [] -∗
  C.dec rep reply (Θ rep))` (decode only an answer the method gave; success post `∃ rep, Θ rep
  true`). (3) `Netrpc/Defs.lean`'s **`wp_Call_tag`** derives from it, for `craqCodec`, the shape
  the clients use: given `HT : ∀ rep, Φ rep [] ⊢ ⌜T rep⌝`, the obligation is `□ (D -∗ ∀ rep, ⌜T
  rep⌝ -∗ dec …)` and the post is Net's (with `Φ rep []`); `craqCodec_dec_frame`; `tagOk_*` per
  reply (`tagOk_nil`: an empty reply has no tag). Every client in `Netrpc/` (NodeClient,
  CoordClient, New) now uses `wp_Call_tag` with `T := tagOk <reply type>`; the `Φ`s that did not
  pin the reply (`Ping`, `Commit`, `Write`, `Update`, coordinator `AddNode`/`Write`/`RemoveNode`)
  gained `⌜msg = [] → …⌝`. When Net's fix lands: replace `RpcCallReply.Call` by Net's spec (its
  premise is likely the `T`/protocol shape), drop the class.
- **H6. Perennial's `log`**: `*log.Logger`'s `Printf`/`Println`, `log.Default`, `log.Fatalf`, and
  `log.Printf` with error arguments (`notes/perennial-changes.md`, 2026-11-23). The node and the
  coordinator call them.

## Proof design notes (for the next steps)

- **P1. The linearization point.** The lab's `opAU γ i Q` is an Iris AU at `↑clientN`; remote gives a
  one-shot `remote.lin R i Φ` (paxos made `opAU` a one-shot fancy update, `lin_opAU`, `Inv.lean`).
  craq fires each operation's update once (a put's at the tail's commit, a get's at the tail's
  read), so the same change works; `Protocol/Commit.lean`, `Laws.lean` (AU elimination) change with it.
- **P2. The model (done: `examples/craqnet/ModelSet.lean`).** The Go state `(M, Pend)` does not
  determine the set of configurations the history reached (put a unknown; put b ok gives `({k:b},
  [a])` and allows "a fired before b, dropped"; put b ok; put a unknown gives the same Go state
  without it), so **kit.go's `Equal` is now always false** (porcupine only merges fewer states) and
  `kvRep` lets the Go state **bracket** the set: `Sim a P S` = every configuration reachable from
  `⟨a, P⟩` is in `S` (`Funl`) and every one in `S` is reachable from `a` with a sub-multiset of `P`
  pending (`Fall`). `sim_init`, `sim_step`: the model's step is defined exactly when `goStep` (kit.go's
  `step` on the decoded answer, `Kit.lean`'s `decAns`) is, and the next set is bracketed by `goStep`'s
  next state. Values are bounded (`Str8`, < 256 bytes: `encStr`'s length byte), so the store `kvB` is
  over `St = GoString → Option Str8`; `Kit.lean`'s `lift` maps it to the protocol's `KvM.State`.
- **P4. Next steps** (2026-11-23, second agent; the coordinator's order: (a) H5, (b) ModelProof,
  (c) KitProof, (d) Mains/TopLevelDefs/TopLevelRobustness/`craq_remote_robust` + `etc/theorem-loc.py`,
  (e) `etc/tcb-collections/dsv-craq.txt`). State:
  (a) **Decoders**: `dec_*` restated (H5); `Netrpc/` moved onto `RpcCallReply` (built: `lake build
  ...Craq.Netrpc.New` green, 2026-11-23). The decoder proofs in `CodecProof.lean` were delegated to
  a sub-agent (third agent's session); see the git log / the file for which `dec_*` and
  `craqCodecLaws` are proved. Plan if unfinished: pure decoders with round-trip lemmas against
  `Wire.lean`; `wp_rpcGetTag`, `wp_rpcDec_t{5,6,12,11,29,16,20,24,28,10,9,8}` in `wp_rpcGetU64`'s
  style; each `dec_*` through `rpcDecode`'s type switch (`tagOk` rules out the panic).
  (b) **Done** (`examples/craqnet/ModelProof.lean`, `lake build` green): `kvDec_box` (from
  `out_intoVal_inj`, `in_intoVal_inj`, `outV_inj`, `ivK_inj`), `ivK_inOf`, `Model.wp_proof`
  (Init: `sim_init`; Step: `wp_step`, `linkv.pM_step … (kvDec_box …)`, `sim_step`; Equal: always
  false; Hash nil).
  (c)-(e) not started: `KitProof.lean` (`Codec`, `Gen`, `op`, `Client`/`ServeClient`, `Orch`/
  `remote.Check`, `Server`/`runNode` over `HttpRpc.lean`'s classes), `Mains`, `TopLevelDefs`,
  `TopLevelRobustness` as paxos's; the statement's premises: every `InitHyp` (net.rpc, net.http),
  `RpcHttpAddr`, `RpcHttpDial`, `RpcHttpServe`, `LogHyp`, and the two open points of H4 (the
  allocation of `rpcAddrP` at the deployment's addresses; a machine's starting `muxOwner []`) as
  explicit premises in the shape Net's piece will likely give (an allocation lemma `|==> ∃ W,
  [∗list] a ∈ addrs, rpcAddrP W a hs hsAns` and `muxOwner []` from net/http's initialization).
- **P3. Order of the port** (done up to the kit) (each file through `Craq/wip/port.py`, then `etc/lean-check.py`): `Kv/` (the
  rest: `Commit`, `ReadVersion`, `AllItems`, `AllNewerDirty`, `AllNewerCommitted`, `New`; first errors
  are the drift above), `Protocol/` (with P1), `Iface`/`Specs` (over `Net/Proof/net/rpc`'s `RpcWorld`,
  `errMsg`, `serverErr`, `models_lab.errAny`), `Node/`, `Coord/`, `Netrpc/` (over the proved client),
  then the kit (`Kit/` rewritten onto remote, as paxos's `Kit.lean`/`KitProof.lean`/`Mains.lean`),
  then the statement (`craq_remote_robust`, as `paxos_remote_robust`).

## Which lab run

`craq-bump-1` (the end of craq-net-2 → craq-net-clients-1 → craq-bump-1): clients on nodes of their
own, a chain of 3-5 with late joins and either read mode chosen at random, removals asked by client
nodes. Its axioms: Lean's three and porcupine's `CheckOperations.wp_proof` (here the verified
porcupine replaces it).
