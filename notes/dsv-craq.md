# dsv-craq: dsverify-lab's craq kit on the net extension (phase 6)

Branch `dsv-craq` (2026-11-23), off `dsv-paxos` (`e3eaf5cd0d`) with `origin/lean` merged (the net/rpc
client's proofs). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/craq/` (run **`craq-bump-1`**: proof `d9f172f` tag
`final`, fork `a0238ac`, Perennial `3afd77e35`; read only, nothing in the lab changed).

**State in one line (2026-11-23, fourth agent: see P5 for the current state; the line below is the first agent's):** the Go and its translation are done and tested;
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
  for the bindings (P4 (c)). **Server side fixed too** (`models-rpc-server` 36728bd8ed, merged):
  `methodOk`'s `NewArg` gives `argDec C argv D Sm Θ := codecSet C ∗ □ (D -∗ ∀ args Φ, Sm args
  Φ -∗ Sm args Φ ∗ C.dec args argv (Θ args))`: decoding owed only of argument bytes a client
  deposited for the method (so the bindings' argument decoders can take `tagOk` the same way,
  from `nodeSpec`/`coordSpec`'s `⌜args = enc…⌝`). `origin/lean` 07268ddb57 (dsv-paxos, dsv-bufio,
  dsv-infra, wildcard listen, Perennial 7b2259a12) merged 2026-11-23: `gen-init --check` (268 up
  to date) and `goose --check --project dsv-craq` pass; the craq leaves build.
- **H6. Perennial's `log`**: `*log.Logger`'s `Printf`/`Println`, `log.Default`, `log.Fatalf`, and
  `log.Printf` with error arguments (`notes/perennial-changes.md`, 2026-11-23). The node and the
  coordinator call them.

## Link check (VR's finding 7, 2026-11-23)

Every package whose initialization or package fact the proofs use is linked by every command:
`go list -deps` of `cmd/orch`, `cmd/client0`, `cmd/server1`, `cmd/server2` (real build, and with
`-tags netmodel`) all contain `transport`, `store`, `store/kv`, `node`, `coordinator`,
`transport/netrpc`, `examples/craqnet`, `net/rpc`, `net/http`, remote, porcupine. The package facts
used (`Base.lean`: `store`/`node`/`coordinator`'s `errors.New` variables) are set by those
packages' own initializers. No fact rests on an init hook: the codec's registration
(`codecSet craqCodec`, in `rpcReady`) is the explicit call `Register()` (`rpc_model_gen.go`, build
tag `netmodel || goose`; a no-op in the real build) made by `newSys` and `Server`, and the go-craq
packages have no `func init`. The commands' `PkgTable.lean` are not generated yet (with `Mains`,
P4 (d)); when they are, recheck that their tables list these packages.

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
  (a) **Done.** `CodecProof.lean` proves `dec_EmptyReply`, `dec_VersionResponse`, `dec_Item`,
  `dec_NodeMeta`, `dec_PropagateResponse` and **`craqCodecLaws : CodecLaws`** (`lake build`
  green; axioms Lean's three): pure decoders with round trips `decX (encX v ++ rest) = some (v,
  rest)` (length bounds from `rep.length < 2^63`), `wp_rpcGetTag`, `wp_rpcDec_t{5,6,12,29,16,20,
  24,28,10,11,9,8}`, `wp_rpcErrDecode`; PropagateResponse via `respL_eq` (uses `entriesOf`'s
  `Nodup`). Local copies `getU64_enc'`, `getTag_encStr'` (the `Codec.lean` ones carry that
  section's instance variables); `wp_rpcDec_t28` needs `maxHeartbeats 4000000`. `Netrpc/`'s
  clients still take the `enc_*`/`dec_*` as arguments: instantiate them with `craqCodecLaws`'s
  fields where the kit uses them. Server side (the bindings' argument decoders, reply encoders)
  not yet: P4 (c).
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
  `InitHyp`s of net/rpc and net/http (H1; dsv-infra, `etc/dsv/README.md`; on `lean`, merged), `RpcHttpAddr`, `RpcHttpDial`, `RpcHttpServe`,
  `LogHyp` (H6); **H4 open point 1** as `∀ SS as, regCtx -∗ ([∗list] a ∈ as,
  addrUnset a) ={⊤}=∗ ∃ W, ⌜W.SS = SS⌝ ∗ [∗list] a ∈ as, httpRpcAddr W a` (the shape of
  `robust_of_distProtoRB`'s start, `Net/Statement/DistBridge.lean`; Net has no rpc allocation
  lemma even for raw `rpcAddr` yet); **open point 2** as `⊢ |==> muxOwner []` per server machine
  (or from net/http's `InitHyp`). Since the classes depend on the start's `GooseGlobalGS`/
  `NetProtoGS` (introduced inside `robust_of_distProtoRB`), the statement takes them as
  functions of those instances (`∀ [GooseGlobalGS .hasLC remoteGF] [NetProtoGS], …`). Then check
  `etc/theorem-loc.py` counts these premises (say so here) and set
  `etc/tcb-collections/dsv-craq.txt`'s roots to the statement.
- **P5. Fourth agent (2026-11-23, from df9b0b26f5)**: (1) the server side.
  `Craq/CodecSrv.lean` states the server's codec laws (`SrvCodecLaws`: `decA_*` decode a
  deposit's argument bytes `⌜args = enc…⌝` into `NewArg()`'s fresh value, giving back exactly
  the encoded value; `enc_*` of the reply types); `Craq/CodecSrvProof.lean` (a subagent, in
  progress) proves them (`craqSrvCodecLaws`) and the pure facts `ArgFacts` (encodings injective
  under `len < 2^63`) and `decLen.spec`. `Craq/Netrpc/Bindings.lean` (**proved**, over
  `L : SrvCodecLaws`, `I : ArgFacts`, `Hlen : decLen.spec` as theorem arguments until the proof
  file lands): per method `newArg_*` (`newArgOk`, i.e. `methodOk`'s body; `methodOk_of`) for all
  10 `NodeBinding` methods (`ClientWrite`, `ReadAll`: spec `False`) and `cnewArg_AddNode`,
  `cnewArg_Write`; the receivers `nodeRcv` (`nodeB cfg b svc a ⊢ craqCodec.rcv (ptrIface
  NodeBinding.ty b) (rcvrIs craqCodec _ (nodeSpec …) "NodeBinding" false)`) and `coordRcv`.
  **Finding F1 (blocks `RemoveNode`, needs Net)**: Net's `callRet` (`Net/Proof/net/rpc/
  ServerDefs.lean`) asks a method's error for a fixed message (`errMsg e msg`), but
  `CoordinatorBinding.RemoveNode` returns `coordinator.RemoveNode`'s error, which can be a
  net/rpc client error from `sendMeta`/`updateNode` (`Client.Call.spec` gives only
  `models_lab.errAny` for non-`ServerError` errors; `isCoordSvc`'s RemoveNode post is `errAny`).
  So `coordRcv` takes RemoveNode's `newArgOk` as a premise `HRN`. Fix in Net, either (a)
  `callRet`'s error branch also admits `errAny e ∗ ∀ msg, (if msg = [] then C.enc replyv (Φ · [])
  else Φ [] msg)` (the server calls `Error()` once), or (b) `Client.Call.spec`'s non-server
  errors get `∃ msg, errMsg err msg` (ErrShutdown, decode and io/net errors have deterministic
  `Error()`), after which `isNodeClient`/`isCoordSvc`'s `errAny` could be strengthened. (2), (3):
  **Closed (2026-11-23)**: `CodecSrvProof.lean` (`craqSrvCodecLaws`, `encString_inj`, `encMeta_inj`,
  `encCommitArgs_inj`, `encWriteArgs_inj`, `encClientWriteArgs_inj`, `encPropReq_inj`, `dec_len`)
  and `Netrpc/BindingsProof.lean` (`craqArgFacts`, `nodeRcv_ok`, `coordRcv_ok`): `lake build`
  green, `#print axioms nodeRcv_ok`/`coordRcv_ok`: Lean's three (`coordRcv_ok` with premise `HRN`, F1).
  `examples/craqnet/ServerProof.lean`: `codecFresh` (`isMutex codecMu codecInv ∗ codecUnset`),
  `wp_Register` (over Net's `SetCodec.spec`) proved.
  **Finding F2 (open point 3, Net)**: `Register()` = `rpc.SetCodec` needs the exclusive
  `codecFresh`, which only net/rpc's initialization can give; net/rpc's package fact
  (`Dsverify/Proof/net/rpc/Base.lean`, the `InitHyp`'s) is persistent and has no such part, and
  Net has no initialization proof for net/rpc. So every machine's spec (client and server) takes
  `codecFresh` as a precondition, and the top level needs it from the machine's boot (a premise
  in the shape Net's eventual package fact decides; a `⊢ |==> codecFresh` premise would be
  inconsistent: it is a heap points-to). Likewise `srvEnv` (`cliEnv ∗ invalidRequest ↦□ ()`):
  the package fact has `cliEnv`'s content but not `invalidRequest`; a precondition for now.
  **Finding F3 (blocks the nodes' `srvServes`, Net)**: Net's `errOk S` (`ServerDefs.lean`: every
  method spec must accept every non-empty error message, for the server's own error answers)
  fails for `nodeSpec`'s `Read`: the message `notFoundMsg` ("key doesn't exist") means a
  linearized not-found (`readCont`, needed by `op`'s `ServerError` case), so a deposit cannot
  give `Φ [] notFoundMsg` for free. (`coordSpec` meets `errOk`.) Fix in Net: `errOk` over the
  messages the server itself sends (its decode error's, "can't find service/method", the
  ill-formed request's), a named set (`srvMsg`), not every message; craq's messages are not in
  it. Until then `runNode`'s `srvServes` for a chain node needs `errOk (nodeSpec …)` as a premise.
  `examples/craqnet/Conf.lean`, `ConfProof.lean` (a subagent, in progress: `choose`, `plan`,
  `mine`, `encode`, `decode`, `sendConf`, `configure`, `awaitConf` over a trivial protocol at the
  conf addresses).
- **P5 (cont.), state at the fourth agent's end.** Proved and built (`lake build` green, Lean's
  three): `Craq/CodecSrvProof.lean`, `Craq/Netrpc/{Bindings,BindingsProof}.lean`,
  `examples/craqnet/{Conf,ConfProof}.lean` (a subagent: `wp_choose`, `wp_plan` (`planOk`),
  `wp_mine`, `wp_Conf_encode(_ptr)`, `wp_decode` (gives `msgOk`: `confOk`, the removals
  `remsOk`), `wp_sendConf`, `wp_configure` (`[LogHyp GF]`), `wp_awaitConf` (post `False`),
  `wp_make_conf_chan`, `wp_recv_msg` (a bag channel of `msgOk`); `confProto` (trivial) at the
  conf addresses (`addrProto a confProto confProto`, set at the start with `addrs_set_proto`); the
  Net specs `net.Dial`/`Listen`/`Accept`/`Conn.Read`/`Write`/`Close` are theorem arguments, as in
  paxos; `wp_ReadFull_lt`/`wp_ReadAtLeast_lt` are local copies of Perennial's proofs with the
  `readatleast-prefix` branch's weaker premise: drop when the pin passes it), and
  `examples/craqnet/ServerProof.lean`: `codecFresh`, `wp_Register`, `coordSpec_errOk`,
  `srvServes_coord`, `srvServes_node`, `removeNodeOk.spec` (F1's premise), **`wp_Server1`** (the
  coordinator's machine, `Server(1)`: pre `isPkgInit kpkg ∗ codecFresh ∗ muxOwner [] ∗ srvEnv ∗
  craqCtx cfg ∗ coordRes cfg`, `cfg.cAddr = 127.0.0.1:7501`; arguments `SetCodec.spec`,
  `coordinator.wp_New/wp_Start/coord_svc`, `netrpc.factory`, `removeNodeOk.spec cfg`;
  `[RpcHttpServe GF]`), **`wp_runNode`** (pre adds `rpcReady`, `nodeRes cfg a ∗ joinTicket cfg.γ
  a`, `errOk (nodeSpec …)` (F3); arguments the node's/kv's/netrpc's specs).
  In progress at the end (a subagent): `examples/craqnet/ClientProof.lean` (`Sys.end`, `readAt`,
  `remove`, `op`, `newSys`, `Client.spec`/`wp_proof`, `Orch.spec`/`wp_proof`); check its state
  (`etc/lean-check.py -q -a`, `grep sorry`) before going on.
  **Next**: (i) `Server.spec` for every `id` (id 1: `wp_Server1`; id ≥ 2: `wp_make_conf_chan`,
  `go awaitConf` (`wp_awaitConf`), `wp_recv_msg`, then `wp_runNode` if `id ≤ N+1` (needs
  `Register()` first: `wp_Register` at the top of `Server`, so `Server`'s pre has `codecFresh`
  and gives `rpcReady`), then the idle loop (post `False`/`True`); `id ≤ N+1` with N ≤ 5 and
  id ≤ 6: every machine's `nodeRes`/`joinTicket` is in its precondition regardless);
  (ii) `Mains` (the 12 commands; generate their `PkgTable`s with `etc/gen-init.py`, recheck the
  linkage per VR finding 7), `TopLevelDefs`, `TopLevelRobustness`, the statement, following
  `paxos_remote_robust` (`robust_of_distProtoRB`; addresses `serverAddrs ++ clientAddrs ++
  confAddrs`; `craq_alloc`, `pend_alloc`, `mapCtx_alloc`, `addrs_set_proto` for client (remote)
  and conf (`confProto`) addresses; server addresses: the H4 allocation premise); premises:
  `InitHyp`s (net/rpc, net/http), `RpcHttpAddr`, `RpcHttpDial`, `RpcHttpServe`, `LogHyp`, H4's two
  open points, and the findings' premises F1 (`removeNodeOk.spec`), F2 (`codecFresh` per
  machine: Net must decide; a `|==>` premise would be inconsistent), F3 (`errOk (nodeSpec …)`),
  `srvEnv`. F2 means the statement cannot be closed honestly until Net gives net/rpc's
  initialization (or a per-machine boot fact): ask the coordinator.
  **Tier check** (land gate, `etc/tier-check.py --check`, 2026-11-23): 13 craq violations
  (`Craq/Hyps -> Net.Proof.net.rpc.Results`; `Craq/Protocol/{All,Alloc,Fire,Laws,Simple}` proof
  imports (ported from the lab's style); `examples/craqnet/{ConfProof,ServerProof,ClientProof}
  -> KitProof`, `KitProof -> ModelProof`, `ClientProof -> Net.Proof.net.rpc.SetCodec` (told to
  use the Spec)). Restructure at landing: move `KitProof`'s helpers (`wp_ServerAddrs`, …) to a
  defs module or take them as arguments; `Protocol/` lemma files are defs, not proofs.
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
