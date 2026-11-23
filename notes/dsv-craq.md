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
  only "some field values". **Landed on `origin/models-rpc-server` 2a6b4e5d12, merged here**
  (2026-11-23; it moved the Perennial pin to `7b2259a12`: `.lake/package-overrides.json` points
  at `/shared/perennial-7b2259a12`): Call's premise is `□ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep
  reply (Θ rep))`, success post `∃ rep, Θ rep true`. Here:
  (1) `Codec.lean`'s `dec_*` take the premise `tagOk t rep` (pure `getU64`, `getTag`, `tagOk`,
  `getTag_encStr`, `tagOk_tagged`) and failure branches giving some field values (`∃ k v, p ↦ …`;
  Item `∃ k sl`; PropagateResponse `∃ mp', p ↦ mp'`; NodeMeta `∃ m`); proofs in
  `CodecProof.lean` (`craqCodecLaws`; status P4 (a)). `tagOk` is not a workaround of Net's old
  spec but what the guard gives: the method's answer `Φ rep []` says the reply is an encoding of
  the reply type, hence its tag. (2) `Netrpc/Defs.lean`'s **`wp_Call_tag`** is Net's
  `Client.Call.wp` for `craqCodec` in the shape the clients use: given `HT : ∀ rep, Φ rep [] ⊢
  ⌜T rep⌝`, the obligation is `□ (D -∗ ∀ rep, ⌜T rep⌝ -∗ dec …)` and the post keeps `Φ rep []`
  (`craqCodec_dec_frame`); `tagOk_*` per reply type, `tagOk_nil`. Every client in `Netrpc/` uses
  it with `T := tagOk <reply type>`; the `Φ`s that did not pin the reply (`Ping`, `Commit`,
  `Write`, `Update`, coordinator `AddNode`/`Write`/`RemoveNode`) gained `⌜msg = [] → …⌝`. (The
  interim hypothesis class `RpcCallReply` is gone.) Still open on Net's side (Upamanyu: same
  shape coming): the server's `methodOk` `NewArg` owes decoding of every request body — matters
  for the bindings (P4 (c)).
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
  (c) **KitProof** (in progress). `Kit.lean` now states `Codec.spec` (over `kvR γ`, remote's
  `codecOk`) and `Gen.spec` (`genSpec`, inputs `∃ x : KIn, i = ivK x`); `KitProof.lean` (new)
  proves them (**done**, `lake build` green; `Codec.wp_proof` takes `[go.BasicIntoValInj]`) and
  the helpers `wp_ServerAddrs`, `wp_ClientAddrs`, `wp_ConfAddrs`, `wp_attempt`, `wp_digit` (pre
  `True`), `wp_flag`, `wp_encStr`, `wp_decStr`, `encOutV_outV`, `outOk_outV`. Kernel pitfall
  seen: an inline `have … := by simp only [slice.slice, sliceIndexRef, …]` made the kernel hit
  "deep recursion" on the whole theorem; a separate lemma (`sliceIndexRef_slice0`) fixed it.
  Still to state and prove, porting the lab's `Kit/` (3060 lines; `Craq/Proof/Kit/*.lean` in the
  lab) by editing onto remote and Net, in paxos's shape (`Kit.lean`'s `Orch.spec`/`Client.spec`/
  `Server.spec`, `KitProof.lean`):
  * the configuration messages: `Conf.encode`/`decode`/`mine`/`plan`/`choose` (lab
    `OrchConf.lean`, `Decode.lean`), `sendConf` (net.Dial/Write/ReadFull/Close) and `awaitConf`
    (Listen/Accept/ReadFull, a bag channel of `msgOk`; lab `Await.lean`, `OrchSend.lean`) over a
    trivial protocol (`confProto`: the messages carry nothing; set at the conf addresses with
    `addrs_set_proto`);
  * the client machine: `newSys` (awaitConf goroutine, `<-ch`, `Register()` = the codec's
    `codecSet craqCodec`, `go s.remove(rs)`), `Sys.end`/`readAt`/`remove` (CoordinatorClient
    `RemoveNode`, `Netrpc/CoordClient.wp_CRemoveNode`), `op` (put: coordinator `Write`; get: node
    `Read`, `Netrpc/`; the linearization through `lin_opAU`), `Client` via
    `remote.ServeClient.spec` (paxos's finding: `newClient` returns the `Sys` made before);
    lab `Op.lean`, `New.lean`, `Client.lean`;
  * the server machine: `Server(1)` = `coordinator.New`, `CoordinatorBinding`,
    `rpc.RegisterName` (`RpcHttpServe.RegisterName`), `rpc.HandleHTTP`, `go c.Start()`,
    `http.ListenAndServe` (`RpcHttpServe.ListenAndServe` with `ServeHTTP`'s `handlerOk`);
    `Server(k ≥ 2)` = awaitConf, then `runNode` (`node.New` over `kv.New`, `NodeBinding`, the same
    rpc/http calls, a goroutine `Sleep; n.Start()`), then the idle loop; lab `Boot.lean`,
    `BootNode.lean`. **Missing piece**: the bindings' server side (`CoordinatorBinding`/
    `NodeBinding` methods meeting `coordSpec`/`nodeSpec` as `rcvrIs craqCodec …` for
    `Server.RegisterName`: the request decoding (`CodecSpec`'s `dec` of the args, `rpcDecode` of
    the args types: more `dec_*` lemmas, for `EmptyArgs`, `WriteArgs`, `CommitArgs`, `string`,
    `NodeMeta`, `ClientWriteArgs`, `PropagateRequest`) and the replies' encoding
    (`rpcEncode` of the reply types: `enc_*` for `EmptyReply`, `VersionResponse`, `Item`,
    `PropagateResponse`, `NodeMeta`), plus `rpcReceiver`'s `rcv` for the two bindings — the
    lab's `Dispatch/` did this for its own codec; here they are proofs over `rpc_gen.go`
    (`Codec.lean` has no server-side lemmas yet).
  * the start (lab `Start.lean`): `craq_alloc` (`Protocol/Alloc.lean`) for the chain's five
    addresses, the rpc world `W` with `W.SS = craqSS γ cAddr chain`, the server addresses'
    `httpRpcAddr W a` (**H4 open point 1**, a premise), the client addresses' remote protocols
    (`addrs_set_proto`, as paxos), the conf addresses' `confProto`, `pend_alloc`, `mapCtx_alloc`.
  (d) `Mains` (12 commands: orch, client0..4, server1..6; paxos's `wp_main`), `TopLevelDefs`
  (`boot`, `system`, `craqKitAddrs := serverAddrs ++ clientAddrs ++ confAddrs`),
  `TopLevelRobustness` (`robust_of_distProtoRB`, as `paxos_remote_robust`), the statement
  `Dsverify/Spec/.../craqnet/TopLevelRobustness.lean`'s `craq_remote_robust.spec`. Its premises
  (coordinator's rule: every hypothesis class and both open points of H4 visible): the
  `InitHyp`s of net/rpc and net/http (H1; dsv-infra, `etc/dsv/README.md`; merge
  `origin/dsv-infra`, now 338ef14dd2), `RpcHttpAddr`, `RpcHttpDial`, `RpcHttpServe`,
  `RpcCallReply`, `LogHyp` (H6); **H4 open point 1** as `∀ SS as, regCtx -∗ ([∗list] a ∈ as,
  addrUnset a) ={⊤}=∗ ∃ W, ⌜W.SS = SS⌝ ∗ [∗list] a ∈ as, httpRpcAddr W a` (the shape of
  `robust_of_distProtoRB`'s start, `Net/Statement/DistBridge.lean`; Net has no rpc allocation
  lemma even for raw `rpcAddr` yet); **open point 2** as `⊢ |==> muxOwner []` per server machine
  (or from net/http's `InitHyp`). Since the classes depend on the start's `GooseGlobalGS`/
  `NetProtoGS` (introduced inside `robust_of_distProtoRB`), the statement takes them as
  functions of those instances (`∀ [GooseGlobalGS .hasLC remoteGF] [NetProtoGS], …`). Then check
  `etc/theorem-loc.py` counts these premises (say so here) and set
  `etc/tcb-collections/dsv-craq.txt`'s roots to the statement.
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
