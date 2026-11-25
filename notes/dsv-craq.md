# dsv-craq: dsverify-lab's craq kit on the net extension (phase 6)

Branch `dsv-craq` (2026-11-23), off `dsv-paxos` (`e3eaf5cd0d`) with `origin/lean` merged (the net/rpc
client's proofs). Plan: `notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`.
Source: dsverify-lab `master` `915f964`, `examples/craq/` (run **`craq-bump-1`**: proof `d9f172f` tag
`final`, fork `a0238ac`, Perennial `3afd77e35`; read only, nothing in the lab changed).

**State (2026-11-24, eleventh agent, P15: on lean b64d2397f8, Perennial d9c8c1d97):** `lean` merged
(the real-`fmt` pin bump and after); the proved theorem is the plain **`craq_remote_robust :
craq_remote_robust.spec`** (statement unchanged: `Robust [] (system σ) g (2 ^ 31) (2 ^ 63)`): Net's
`DialHTTP.wp` takes no strings hypotheses since lean's phase 7 S5 batch 7 (57d66cdcee: Perennial's
`strings.Cut`/`TrimLeft` proofs, passed in Net's Links); `StringsPending`,
`stringsPending.spec` and `craq_remote_robust_of_strings` are gone. `#print axioms`: Lean's three.
Non-vacuity open (below). Ready to land.

**Older state (2026-11-24, tenth agent, P14: on lean 37bfea9484):** `lean` merged (Perennial b3f2fc485, dsv-steps63 landed); `Client.Call`'s frame bound discharged (P13); the closed `craq_remote_robust` waits for the real-`fmt` pin bump (`pin-bump-52d62e83c/2026-11-24`: Perennial ed1955557's proved `strings.Cut`/`TrimLeft`), until then `craq_remote_robust_of_strings`; non-vacuity instances: none without axioms (P14). Lands right after the pin bump.

**Older state (2026-11-23, eighth agent, P12: review #24's craq findings fixed):** craq is on
`models-rpc-http`'s shapes verbatim (merged `origin/models-rpc-http` fda1e58c0a and `origin/lean`
69adf61913); the dial is Net's proved `net.rpc.DialHTTP.wp`; the net/rpc world's allocation is
proved; the statement's step bound is `2 ^ 31 - 1`; craq lands after models-rpc-http. See P12.

**Older state line (seventh agent: F1 discharged, the statement has no finding premise left, P10; fifth agent: `craq_remote_robust` proved over its premises, see P8, P7, P6, then P5; the line below is the first agent's):** the Go and its translation are done and tested;
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

## net/rpc over HTTP from Net (2026-11-25, dsv-fix2b; supersedes H2, F2 and the `RpcBoot`s below)

`craq_remote_robust` keeps one net premise, `RpcHttpServe` (`Craq/HttpRpc.lean`): `http.ListenAndServe(a,
nil)`, which Net does not prove (it proves `http.Serve` on a listener), now over Net's `muxRpc`. The
rest is Net's: `rpc.HandleHTTP` (`net.rpc.HandleHTTP.spec`, over net/http's `Handle`), the package-level
`rpc.RegisterName` on `DefaultServer`'s owned, empty registry (`RegisterName.spec_fresh`,
`defaultSrvFresh`), and the eleven client and server commands' first-run boots (no `RpcBoot` premise:
kitgen `boot=`, `etc/dsv/craq.py`; `BootLinked.lean`'s `boot_netrpc`, `boot_craqnet`: `transport/netrpc`'s
initializer runs net/rpc's, the machine's first run of net/rpc and net/http, Net's
`net.rpc.wp_init_first_http`). The thread bound is `2^30` (net/http's first initialization, `Threads30`;
Upamanyu approved `2^31 → 2^30` on #8, 2026-11-25). `#print axioms`: Net's interim
`net.http.wp_init_first`, `net.http.wp_initialize'`, `net.rpc.wp_initialize'`, besides Lean's three
(`net.http.Handle` proved by S5, lean `676aede0a1`; merged into dsv-fix2b 2026-11-25).

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
  `examples/craqnet/ClientProof.lean` (a subagent; `lake build` green, no tier violations):
  `wp_Sys_end`, `wp_Sys_readAt`, `wp_Sys_remove`, `wp_op` (both paths, `notFoundMsg`,
  `lin_opAU`), `wp_newSys`, `Client.spec`/`Client.wp_proof` (pre adds `codecFresh`, the conf
  address's `addrProto … confProto`, `cfgKit cfg`), `Orch.spec`/`Orch.wp_proof`; its own
  `awaitConf.spec`, `configure.spec` (ConfProof's `wp_awaitConf`/`wp_configure` with the Net
  specs applied), `KIn_countable`, `KOut_countable`.
  **Finding F4 (blocks `Orch`, in the kit's `Kit.lean`)**: remote's `Check.spec` needs
  `PendDec (kvR γ) kvS` and the output encoding injective, and neither holds: `ovK (.got none)`
  and `ovK .done` are both `Out{}` (`kvR_encOut_not_inj`), and `kvDec` decodes `Out{}` to a put
  as `.done`, so `PendDec.ok` fails for (put, `.got none`) and (get, `.done`). `Orch.wp_proof`
  takes them as arguments `hdec`/`hinj`, which are false: fix before the statement. Either (a)
  one `KOut` value for both (a put answers `got none`), with `liftOut` depending on the input in
  `lin_opAU` (`none` is `.done` for a put, `.got none` for a get), re-checking `ModelSet`/
  `ModelProof`; or (b) remote's `Check` asks injectivity and `PendDec.ok` only of outputs the
  input can produce (a change to examples/lib/remote: ask the coordinator).
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
- **P6. Fifth agent (2026-11-23, from f35a3d5a7e)**. Done:
  (1) **F4 fixed, proof only** (3d67b9b188): the store has one output `got none` for a put's
  success and a get's not found (kit.go answers both `Out{}`); `ModelSet.lean`'s `KOut` is `got
  (Option Str8) | bad` (`bad`: an answer no operation gives, what an ill-formed `Out` decodes to;
  never output; `ovK .bad = Out{V: "\x00"}`); `kvStep` answers a put `got none`; `Kit.lean`'s
  `liftOut i` depends on the input (a put's `got none` is `.done`); `decAns` is input-independent
  (`ovK`'s inverse). `ModelDefs.lean` proves `kvS_pendDec` (`PendDec (kvR γ) kvS`) and
  `kvR_encOut_inj`; `Orch.wp_proof` uses them (no false arguments). kit.go unchanged.
  (2) **Tier split** (kit tier-clean, `etc/tier-check.py`: 0 craqnet violations): `ModelProof` →
  `ModelDefs` (defs: helpers, `Model.spec`, the F4 lemmas) + `ModelProof` (`Model.wp_proof`);
  `KitProof` → `KitDefs` (helpers) + `KitProof` (`Codec`/`Gen.wp_proof`); `KitSpecs.lean` (defs):
  `cfgKit`, `serverAddrs_chain`, `codecFresh`, `wp_Register`, `KIn`/`KOut_countable`,
  `awaitConf.spec`, `configure.spec`, `Client.spec`, `Orch.spec`, `serverRes`, **`Server.spec`**;
  `ServerProof.lean` (proof): `wp_Server1`, `wp_runNode`, **`Server.wp_proof`** (every id: the
  coordinator, or a chain machine: Register, awaitConf goroutine, `<-ch`, `runNode` if `id ≤
  N+1`, idle loop); arguments the packages' specs, `awaitConf.spec`, `HRN` (F1), `HE` (F3).
  (3) **LogHyp per Go's preconditions** (rabia review lessons): `log.Printf`/`log.Println` have
  bodies in Perennial's trusted model, so `LogHyp.wp_Printf`/`wp_Println` are now theorems; the
  class keeps `wp_Default` (returns a non-nil logger) and `*Logger`'s `Printf`/`Println`, which
  now require `l ≠ null` (a nil logger panics); `nodeFields`' pure part is `⌜ch = chan.nil ∧ lg ≠
  null⌝` (node `New` from `wp_Default`), the `wp_log` macros discharge it.
  (4) **PkgTables**: `etc/dsv/craq.py` `PROGRAMS` (the twelve commands) and `HYP_IMPORTS =
  'none'` (as gryff: net/http's names-only imports are outside the inventory); `gen-init`
  generated `cmd/*/PkgTable.lean` (transport/netrpc's `Init` no longer takes net/http's InitHyp).
  **models-rpc-http (1a4d9546c9) does not build here**: merged, `Net/Proof/net/rpc/DialHTTPPath.lean:157`
  fails (`irename «$a1»: unknown hypothesis`): it was written against the old `bufio.NewReader`
  spec, and lean (merged here) has dsv-bufio's revision. So the merge was undone (not pushed); the
  adaptation (H4's client side on Net's `rpcAddrP`/`DialHTTP.spec`, `RpcHttpAddr`/`RpcHttpDial`
  removed, `rpcPkg_dialEnv`, `connected` in net/rpc's fact, `DialHTTP.spec` + `receiptBound ≤
  2^64` as `Connect`/`New` arguments) is `git stash@{0}` and the scratchpad's
  `craq-rpchttp-adapt.patch`: reapply when models-rpc-http is rebased on lean.
  **Next**: `Mains.lean` (12 `wp_main`s), `Link.lean` (namespace `Perennial.EtcdGrove.dsvcraq`,
  the lab's `Craq/Proof/Link.lean`: `NodeP.Laws` from `Protocol/`'s `wp_proof`s, the codec
  laws' fields, `netrpcP.wp_NewNodeClient`/`factory`/`wp_NewCoordinatorClient`, `kv.wp_New`,
  coordinator/node specs, `awaitConf`/`configure` from ConfProof with Net's net specs),
  `TopLevelDefs`, `TopLevelRobustness`, the statement. **F2's premise (decided)**: per machine,
  the command's initializer from `ownGoState ∅` returns `ownInitializing getIs ∗ isPkgInit cmd ∗
  codecFresh ∗ invalidRequest ↦□ ()` (∗ `muxOwner []` for net/http), the shape Net will give
  (gryff's `wp_initialize'_own`); sound because only the boot holds `ownGoState ∅`.
- **P7. Fifth agent, later (f65f97ae7f)**. Built (`lake build`, 2861 jobs): `Mains.lean` (12
  `wp_main`s over `KitSpecs`' specs), **`Link.lean`** (namespace `Perennial.EtcdGrove.dsvcraq`:
  `nodeLaws`, `wp_NewNodeClient`/`factory`/`wp_NewCoordinatorClient` from `craqCodecLaws`,
  `wp_awaitConf`/`wp_configure` over Net's `net.*.wp_proof`, `wp_Server` (args `HRN`, `HE`),
  `wp_Client`, `wp_Orch`; instance args `[LogHyp] [RpcHttpAddr] [RpcHttpDial] [RpcHttpServe]
  [NaInvG]`), `TopLevelDefs.lean` (`boot`, `system`, `craqKitAddrs = serverAddrs ++ clientAddrs
  ++ confAddrs`), the statement **`Dsverify/Spec/.../craqnet/TopLevelRobustness.lean`'s
  `craq_remote_robust.spec`** (premises, each `∀ G L` at `heapAt G L` (rabia's) and the start's
  `π`: net/rpc's and net/http's `InitHyp`, `LogHyp`, `ra`/`rd`/`rs` (the H4 classes; `ra` per
  `G`), `rpcAlloc` (H4's allocation: `regCtx -∗ addrUnset* ={⊤}=∗ ∃ W, W.SS = SS ∗
  httpRpcAddr*`), **`RpcBoot` for the eleven client/server commands** (F2: `{{ ownGoState ∅ }}
  cmd.X.initialize' #() {{ ownInitializing getIs ∗ isPkgInit cmd.X ∗ rpcBootRes }}` for every
  consistent `getIs`; `rpcBootRes = codecFresh ∗ invalidRequest ↦□ () ∗ muxOwner []`), F1
  (`removeNodeOk.spec`), F3 (`errOk (nodeSpec …)`: **false of Net's current `errOk`**, so the
  statement is vacuous until Net restricts `errOk` to `srvErrMsg`; alternatively restate
  `RpcHttpServe.ServeHTTP` over a local `srvServes` with the restricted `errOk` and prove it for
  `nodeSpec`)). PkgTables: `etc/dsv/craq.py` `HYP_IMPORTS = 'known'` with `MAIN = [bufio, path,
  internal.bytealg, net.url, crypto.tls]`, `MAIN_GEN = [bufio]` (as gryff; `'none'` made the
  tables' `net.http` entries fail); `gen-init --check` clean.
  **Not yet: `Dsverify/Proof/.../craqnet/TopLevelRobustness.lean`, the proof** (paxos's and
  rabia's shape): `robust_of_distProtoRB craqKitAddrs`; split `Hs` (servers, clients, confs);
  `craq_alloc serverAddrs.tail` (Nodup by `decide`) → `γ`, `isCraq`, `ownState γ KvM.init` (=
  `(kvR γ).sysState kvB.init`, `lift_init`), `tailTok`, `nextHalf`, per chain address two
  `roleHalf`s, `nlogAuth`, `joinTicket` (one `roleHalf` of each to `coordRes`, the other with
  `nlogAuth` to `nodeRes`); `rpcAlloc (craqSS γ cAddr chain) serverAddrs` → `W`; `cfg := ⟨γ, W,
  serverAddrs[0], serverAddrs.tail⟩`, `craqCtx cfg`, `cfgKit cfg` (rfl); `mapCtx_alloc`;
  `addrs_set_proto` for `clientAddrs` (remote's `reqP`/`repP` of `kvR γ`) and `confAddrs`
  (`confProto` both ways); `pend_alloc`; the 12 machines' resources; per machine: `haveI` the
  premises at `heapAt G L`, then a `wp_boot` from `ownGoState ∅`: orch with the generated
  `cmd.orch.wp_initialize'`, the others with `RpcBoot` (its `rpcBootRes` → `codecFresh`,
  `muxOwner []`, and `srvEnv` from `isPkgInit net.rpc` (its fact is `cliEnv`'s content) ∗
  `invalidRequest`), then `cmd.X.wp_main` with `Link`'s `wp_Orch`/`wp_Client`/`wp_Server`. Then
  `TopLevelRobustness.lean`'s `craq_remote_robust : craq_remote_robust.spec`, `#print axioms`,
  `etc/theorem-loc.py` (check it counts the premises), `etc/tcb-collections/dsv-craq.txt`.
  **Lean moved** (coordinator, 2026-11-23): `lean` c4e044df92 (models-rpc-server landed, Perennial
  c95e92207, `/shared/perennial-c95e92207`); this branch may stay on models-rpc-server 36728bd8ed
  for now; when merging lean, repoint `.lake/package-overrides.json` and `PERENNIAL_DIR`, rerun
  gen-init.
- **P8. State at the fifth agent's end (cc9472f5aa)**: **`craq_remote_robust` is proved**
  (`examples/craqnet/TopLevelRobustness.lean`, `lake build` green, 2863 jobs; `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound`), over the statement's premises (P7's list). The
  proof: `wp_bootR` (a boot from `ownGoState ∅` whose initializer returns a resource `R` for
  `main`), `init_of_gen` (the orchestrator: the generated `wp_initialize'` with `R = True`),
  `rpcPkg_cliEnv` (net/rpc's fact is `cliEnv`); the allocation as P7 planned. No `sorry`, no axiom
  under `Dsverify/` (craq). `etc/theorem-loc.py --file …/TopLevelRobustness.lean
  craq_remote_robust`: tcb 687 lines, all premises; `--list-tcb` lists both `InitHyp`s,
  `LogHyp`, `RpcHttpAddr`/`Dial`/`Serve`, `rpcAlloc`, `RpcBoot`/`rpcBootRes`,
  `removeNodeOk.spec`, `errOk`/`nodeSpec` (so it counts the premises). `etc/tcb-collections/
  dsv-craq.txt` (roots `^Dsverify/Proof/github_com/despreston/go_craq/`); `etc/tcb-report.py
  --check` needs a full build (not run: the rules forbid a full `lake build`). Tier check: no
  craqnet violations; the older `Craq/Hyps`, `Craq/Protocol/*` ones remain (restructure at
  landing). `etc/goose.py`/`etc/gen-init.py` equal origin/lean's; `gen-init --check` clean.
  **Caveats for the reader**: (a) **F3's premise is false of Net's current `errOk`** (every
  non-empty message), so the statement is vacuous until Net restricts `errOk` to the server's own
  messages (Upamanyu: will land on models-rpc-server/-http); then the premise is provable for
  `nodeSpec` (its Read's `notFoundMsg` is not a server message) and should become a lemma. (b) F1
  (`removeNodeOk.spec`) becomes provable with `Client.Call`'s `∃ msg, errMsg err msg`. (c) F2:
  `RpcBoot` is in the shape Net will give (a per-machine boot resource). (d) H4: the client side
  awaits models-rpc-http on lean (the adaptation patch, P6); the server side and `rpcAlloc` await
  Net's next piece. (e) Not merged: lean c4e044df92 (Perennial c95e92207).
- **P9. Sixth agent (2026-11-23, from 240a21f95a): lean, net-rpc-errors, F3.** Merged origin/lean
  76c00a8d81 (Perennial 160fcf12a, `/shared/perennial-160fcf12a`): lean's `Dsverify/Proof/net/{rpc,http}/Init.lean`
  (facts `True`) replace craq's own `Base.lean` (dropped; the commands' `Base.lean` import the
  `Init`s); `etc/dsv/craq.py` drops `HYP_IMPORTS = 'known'` (default `'all'`, dsv-inithyp-fix);
  gen-init rerun (twice), `--check` clean. Since net/rpc's fact is `True`, `rpcBootRes` now carries
  `net.rpc.srvEnv` (as dsv-epaxos's) and `rpcPkg_cliEnv` is gone. Remote's landed API
  (remote-adapt.md): `mapCtx_alloc ⊤ clientAddrs 18`, `Orch.spec` and the orchestrator's boot
  carry `[∗list] a ∈ clientAddrs, budUnits a 18` (`K = 6` operations × `readTries = 3`),
  `wp_Check … 18 (by decide)`, `reqP` per address, `opMaybe`'s third component, `newClient` a
  plain WP. Merged `net-rpc-errors` (Net's `errOk` over `srvErrMsg`): **F3 discharged**,
  `ServerProof.lean`'s `nodeSpec_errOk` (Read's `notFoundMsg` is not a server message,
  `notFoundMsg_not_srv`); the statement's `errOk (nodeSpec …)` premise is gone. Tier: clean
  (`X.wp_proof` ghost laws of `Craq/Protocol` renamed `X.holds`; `Craq/Hyps` imports net/rpc's
  defs and specs, the clients take `Client.Call`/`Client.Close` through `RpcClientSpecs`, whose
  instance `Link.lean` makes from Net's proofs). **F1 stays** (`removeNodeOk.spec`): it is false of
  the model (RemoveNode's error can be a net `*OpError`, whose model `Error()` is not deterministic,
  so no `errMsg e msg`), so the statement is still vacuous until Net gives a deterministic
  `OpError.Error` (trusted) or `callRet` admits `errAny` (notes/net-rpc-errors.md).
  `DefaultServer` now comes with the boot (`HttpRpc.lean`'s `defaultServer γ` in `rpcBootRes`,
  `Server.spec`, and `RpcHttpServe.RegisterName`'s precondition, whose post keeps that `γ`), not from
  net/rpc's `True` fact (the landing lesson; epaxos's shape). **Built on fk-lean1** (3a02ce3300):
  `craq_remote_robust` and `nodeSpec_errOk` depend on `propext`, `Classical.choice`, `Quot.sound`
  only; a joint import with the six landed statements (paxos, rabia, epaxos, quepaxa, swiftpaxos,
  remote's counter) loads; all seven build on this branch. `etc/theorem-loc.py`: tcb 595 lines, all
  premises, no axioms. Dup scan (scratchpad `dups.py`): no craq duplicates. Tier check clean; gen-init
  `--check` clean; `proof_roots.namespace()` `Perennial.EtcdGrove.`; goose.py/gen-init.py equal lean's.
- **P10. Seventh agent (2026-11-23, from 41b2955e96): C1(b), F1 discharged.** Upamanyu chose
  option (b) for C1 (#24): net-rpc-errors e3e67f8b3d gives `callRet` a third branch,
  `models_lab.errAny e ∗ ∀ msg, (if msg = [] then C.enc replyv (Φ · []) else Φ [] msg)` (the
  server calls `Error()` once; `""` makes it a success response), no trusted text; merged here.
  `Craq/Netrpc/Bindings.lean`: **`cnewArg_RemoveNode`** (`coordB cfg b svc ⊢ newArgOk …
  (coordSpec … "RemoveNode") …`): RemoveNode's error from `isCoordSvc` (`nil ∨ errAny`) goes to
  `callRet`'s `nil` or `errAny` branch; for the latter, the empty message gives
  `L.enc_EmptyReply` into `Φ encEmptyReply []`, a non-empty one `Φ [] msg` (`coordSpec`'s
  RemoveNode already accepts every message, unchanged). `coordRcv`/`coordRcv_ok`, `wp_Server1`,
  `Server.wp_proof`, Link's `wp_Server` lose `HRN`; `removeNodeOk.spec` is deleted. The other
  bindings' `errMsg` branches add one `ileft`. **`craq_remote_robust`'s statement loses the
  premise** `(∀ G L, letI := heapAt G L; ∀ (π : NetProtoGS) (cfg : Cfg remoteGF), letI := ra G;
  removeNodeOk.spec (GF := remoteGF) cfg) →` (and the header's F1 bullet). Remaining premises,
  each argued true of the model and of Go in the final report of this agent (summary): the
  `InitHyp`s (initializers run without panicking; facts `True`), `LogHyp` (Go's `log.Default`
  never nil; `*Logger` methods safe for concurrent use, non-nil receiver; fmt recovers method
  panics), `RpcHttpAddr`/`Dial`/`Serve` + `rpcAlloc` (instantiated by Net's coming
  `rpcAddrP` over the HTTP handshake; Go's `DialHTTPPath`, `RegisterName`, `HandleHTTP`,
  `ServeHTTP`, `ListenAndServe` behave as stated), the 11 `RpcBoot`s (each command's initializer
  creates the codec registry, net/rpc's variables, `DefaultServeMux`, `DefaultServer`). F1 and F3
  discharged, no false premise is known: **non-vacuous** modulo those library hypotheses.
  `etc/theorem-loc.py --list-tcb`: tcb 463 lines (was 595), all premises, no axioms.
  **Built on fk-lean1** (0ac5872a7a): craq's `TopLevelRobustness` and the six landed ones (swiftnet,
  rabianet, epaxosnet, quepaxanet, paxosnet, remote's counter), 4973 jobs green; a joint import of
  the seven loads, and `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for each.
  (`newArg_Ping`'s `errMsg` branch needed the `ileft` too: the first build caught it.) Dup scan:
  no craq duplicates. Tier check ok (227 known, none new); gen-init `--check` 271 up to date;
  `proof_roots.namespace()` `Perennial.EtcdGrove.`; goose.py/gen-init.py equal the lean base
  76c00a8d81's (origin/lean has moved on to af67426be3, not merged). theorem-loc counts both
  `InitHyp` premises.
- **P3. Order of the port** (done up to the kit) (each file through `Craq/wip/port.py`, then `etc/lean-check.py`): `Kv/` (the
  rest: `Commit`, `ReadVersion`, `AllItems`, `AllNewerDirty`, `AllNewerCommitted`, `New`; first errors
  are the drift above), `Protocol/` (with P1), `Iface`/`Specs` (over `Net/Proof/net/rpc`'s `RpcWorld`,
  `errMsg`, `serverErr`, `models_lab.errAny`), `Node/`, `Coord/`, `Netrpc/` (over the proved client),
  then the kit (`Kit/` rewritten onto remote, as paxos's `Kit.lean`/`KitProof.lean`/`Mains.lean`),
  then the statement (`craq_remote_robust`, as `paxos_remote_robust`).

## Non-vacuity: open (decision 2026-11-24)

**Decision** (kaashoek, 2026-11-24): dsv-craq lands **without** non-vacuity instances; the gap is
recorded here and real instances are a follow-up. Why: the instances P13 wrote
(`examples/craqnet/NonVacuityLinked.lean`) were all local axioms, each restating the premise it
instantiated (the eleven `RpcBoot`s literally the premise's statement), so they showed nothing about
the premises' consistency.

**Premise classes of `craq_remote_robust.spec`** with no axiom-free instance (all of them;
`Dsverify/Spec/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`, checked
against the statement at afff9fd399):

- `net.rpc.InitHyp`, `net.http.InitHyp`: their closure reaches names-only initializers;
- `LogHyp` (`Craq/LogHyp.lean`: `log.Default`, `*Logger.Printf`/`Println`; Perennial's `log` is
  names only);
- `RpcHttpServe` (`Craq/HttpRpc.lean`: net/http's `DefaultServeMux`, `rpc.HandleHTTP`,
  `http.ListenAndServe`; not in Net);
- the eleven `RpcBoot`s, one per command (`cmd.client0`..`client4`, `cmd.server1`..`server6`):
  net/rpc's and net/http's initializers, names only.

Until P15 the proved theorem also took `stringsPending.spec` (`craq_remote_robust_of_strings`;
Perennial's `strings.Cut`/`TrimLeft`); since the pin 52d62e83c those are Perennial's proofs
(passed by Net's own Links since 57d66cdcee) and the theorem is `craq_remote_robust`.

**The removed axiom-based files** are in history: `Dsverify/Proof/github_com/despreston/go_craq/
examples/craqnet/NonVacuityLinked.lean` (added c17f4f4c68, last at 296417da29) and the scratch
`Dsverify/Scratch/CraqAxioms.lean` (296417da29), both deleted by 7fd59eedf5.

**Follow-up order:** dsv-gryff's cheap instances first (its leaf library classes: `strings.Index`,
`sort.Slice`, `math/rand.Seed`); craq has no such leaf class, its first candidate is `LogHyp` (a
spec of Go's `log` in Perennial). Then `net.rpc.InitHyp`, `net.http.InitHyp`, `RpcHttpServe` and
the eleven `RpcBoot`s, which depend on Upamanyu's model initialization of net/rpc and net/http
(their initializers translated with bodies, net/http's server in Net); shared with dsv-gryff's
`RpcHttpHyp`/`RpcBootHyp`.

## Which lab run

`craq-bump-1` (the end of craq-net-2 → craq-net-clients-1 → craq-bump-1): clients on nodes of their
own, a chain of 3-5 with late joins and either read mode chosen at random, removals asked by client
nodes. Its axioms: Lean's three and porcupine's `CheckOperations.wp_proof` (here the verified
porcupine replaces it).
- **P11. Landing prep (2026-11-23).** Upamanyu signed off net-rpc-errors (trusted 3d0cc4bc8b and the
  #8 point). Merged origin/lean 29f93a3c2c (Perennial ccfeb3895, `/shared/perennial-ccfeb3895`;
  dsv-json-main included) and net-rpc-errors b58da6a1a6; PkgTables regenerated with gen-init (the
  twelve craqnet `cmd/*/PkgTable.lean`: the new pin's `slices` imports `iter`). The statement
  (`Dsverify/Spec/.../craqnet/TopLevelRobustness.lean`, the proof's `TopLevel*`) is textually
  unchanged against bcfe226b18. **Built on fk-lean1** (0e6cbf1f25): a scratch module importing
  craq's `TopLevelRobustness` and the six landed ones, 4996 jobs green; `#print axioms` of all seven:
  `propext`, `Classical.choice`, `Quot.sound`. Scratch dropped. Here: tier-check ok (227 known, none
  new); gen-init `--check` up to date; `proof_roots.namespace()` `Perennial.EtcdGrove.`; goose.py,
  gen-init.py and the six landed `TopLevelRobustness` files equal origin/lean's; dup scan
  (`dups.py` at the new pin): no craq duplicates (the 4 hits are the scanner's known false positives).
- **P12. Eighth agent (2026-11-23/24): review #24's craq findings fixed.** Merged `origin/lean`
  69adf61913 (net-sticky-read included) and `origin/models-rpc-http` fda1e58c0a (as dsv-gryff did;
  craq now lands after models-rpc-http). Merge conflicts: `models/README.md` (mrh's net/http row,
  lean's json rows), `Net/GeneratedProof/net/http/chunk5-8` (regenerated, `goose.py --project
  models-net` at Perennial ccfeb3895, identical to dsv-gryff's). Integration fixes of mrh x lean
  (not craq's; upamanyus's landing merge must do the same or better): `modelReadMIMEHeader`
  (dsv-gryff's `fmt.Lent` fix), `Dsverify/Proof/net/http/Init.lean` + `mime/multipart`,
  `net/http/internal/ascii` True facts (dsv-gryff's), `Proto.lean`'s `accept_addrs_shared_au`
  drops the new `rdlTok`, `Errs.lean`'s `errAny_opErrPtr` takes the `*OpError`'s read-only fields
  (lean's `OpError.Error` reads `e.Op`; `DialHTTPPath` persists its fresh OpError), and net/http's
  `connReader.{abortPendingRead,startBackgroundRead}`, `conn.hijackLocked`, `hjPre` carry the
  end's `∃ b, rdlTok cn true b` (net-sticky-read's `deadline_au`; `hijackOk` unchanged).
  `goose.py --project dsv-craq` regenerated (qualified field types).
  Findings: (1, critical) `Craq/HttpRpc.lean` rewritten: the classes `RpcHttpAddr`/`RpcHttpDial`
  are gone; `httpRpcAddr W a` is Net's `net.rpc.rpcAddrP W a (connectReq defaultRPCPath)
  connectAns`; the client dials through Net's `net.rpc.DialHTTP.spec` (`RpcClientSpecs.dialHTTP`,
  Link's instance `net.rpc.DialHTTP.wp`), so `isClient` is models-rpc-http's (handshake, then
  frames). The world's allocation is proved (`craq_rpc_alloc`, TopLevelRobustness proof: a
  registry ghost map, `inv regN' (regInv W)`, `addrs_set_proto`, `W.hs`/`W.hsAns` HTTP's), so
  `rpcAlloc` is no longer a premise. (2, high) the dial precondition is Net's: `rpcReady` now
  carries `rpcEnv` (`receiptBound ≤ 2^64`, `srvEnv` ⊇ `cliEnv`, `httpEnv`, `connected ↦□
  connectedStatus`); `rpcBootRes` gains `httpEnv` and `connected`; the bound is the
  deployment's; `Client.spec`/`Server.spec` take `rpcEnv`. (3) lean merged (above). (4) craq's
  `connectReq`, `connectedAns`, `defaultRPCPath`, `defaultServer` def, `rpc.DialHTTPPath.spec`,
  `rpc.DialHTTP.spec` deleted; `RpcHttpServe` restated in the kits' shape (`muxOwner`, `muxHas`,
  abstract `defaultServer`, `RegisterName`, `HandleHTTP`, `ListenAndServe`; `ServeHTTP`/
  `handlerOk`/`muxRoute` gone). (5) headers rewritten; **step bound**: net/rpc's server (Net's
  `Server.ServeHTTP.spec`) needs `threadBound ≤ 2^31`, so `HandleHTTP`/`ListenAndServe` take it
  and the statement is now `Robust … (2 ^ 31 - 1)` via dsv-epaxos's `robust_of_distProtoLisRBT`
  with no listener (`las = []`). Statement diff: premises `ra`, `rd`, `rpcAlloc` removed (and the
  `letI := ra G`s); `rs` now `∀ G L, letI := heapAt G L; ∀ π, RpcHttpServe remoteGF`; bound
  `2 ^ 63` → `2 ^ 31 - 1`; `rpcBootRes` (its definition, in the tcb) gains `httpEnv`,
  `connected`, and uses `RpcHttpServe.defaultServer`. swiftpaxos (landed) needed mrh's
  adaptation too (dsv-gryff bb8e39f9c3: `Start.lean` RpcWorld by field names, `LibDepsLinked`
  `NewWriterSize.wp_proofRep`; `BootTable.lean` regenerated by `etc/dsv/_swiftpaxos_boot.py`); no
  landed statement changed. **Built on fk-lean1** (commit before the scratch drop): craq's
  `TopLevelRobustness`, the six landed ones (swiftnet, rabianet, epaxosnet, quepaxanet, paxosnet,
  remote's counter), `Net.Proof.net.{http,rpc}.Results` and `Dsverify/Scratch/Axioms.lean`, 5126
  jobs green; `#print axioms` of all seven: `propext`, `Classical.choice`, `Quot.sound`. Scratch
  dropped. Here: tier-check ok (227 known, none new); gen-init `--check` 274 up to date;
  `_swiftpaxos_boot.py --check` clean; copy-part `--check` 0 differ; goose `--check` dsv-craq,
  models-net, dsv-swiftpaxos, dsv-epaxos up to date; `proof_roots.namespace()`
  `Perennial.EtcdGrove.`; dups (`dups-ccf.py`): the 4 known false positives, none craq's; the
  landed `Spec/*/TopLevelRobustness.lean` and `etc/gen-init.py` equal origin/lean's;
  `etc/goose.py` differs from lean only by models-rpc-http's models-net lines.
- **P13. Ninth agent (2026-11-24, from f3ecf63fc2): lean b3f2fc485, steps63, frames, non-vacuity.**
  Merged `origin/lean` 5c7f7d2e59 (Perennial b3f2fc485, `/shared/perennial-b3f2fc485`; models-rpc-http,
  net-rpc-rerr, rpc-defaultserver, prove-ps2-s5srv, kitgen/kitlibs-check landed): the Net/ conflicts
  (mrh x lean integration fixes of P12) take lean's side (its landing merge did them); the notes'
  duplicated mrh sections dropped (lean's own); gen-init rerun (twelve craqnet PkgTables). Merged
  `origin/dsv-steps63` c7addffcdd (awaits kaashoek's approval).
  * **rpc-defaultserver**: `RpcHttpServe` loses `defaultServer`/`defaultServer_persistent`/
    `RegisterName`: `DefaultServer` is Net's `net.rpc.defaultServer γ` (in `rpcBootRes`, the server
    proofs, `HandleHTTP`'s precondition), and `rpc.RegisterName` is Net's proved
    `net.rpc.RegisterName.wp` (the server proofs take `net.rpc.RegisterName.spec`, Link passes the
    proof). Nothing else of S5/rpc-defaultserver is a craq premise (net/http's `ListenAndServe`, the
    mux and `rpc.HandleHTTP` are not in Net yet: `RpcHttpServe` keeps `muxOwner`, `muxHas`,
    `HandleHTTP`, `ListenAndServe`).
  * **net-rpc-rerr's `Client.Call.spec`** asks `sm.length + 16 ≤ maxFrameN` and the encoded
    arguments `≤ maxFrameN` (1 GiB). `wp_Call_tag` (`Netrpc/Defs.lean`) takes `HS : ∀ bs, S M bs Φ ⊢
    ⌜bs.length ≤ maxFrameN⌝` (the method's deposit bounds its encoding) and `Hsm` (auto: `simp`);
    `nodeSpec_frame`/`coordSpec_frame` prove `HS` for every method from the deposits, with
    `Craq/WireLen.lean` (each encoding's length; the strings of at most 2 bytes, `nodup_le2_length`).
    The bounds the deposits now carry: **keys of at most 2 bytes** (`keyOk`, `Wire.lean`; the kit's
    keys are "k0", "k1") and values shorter than 256 bytes (`kvOk`): `valsElem` carries `kvOk`
    (the protocol's records: `craqWf`'s fourth conjunct, `assign` takes `kvOk k x`), so a Write's
    and a store's items' keys are bounded; `nodeSpec`'s Commit/LatestVersion/Read deposits carry
    `keyOk k`, Fwd/BackPropagate `reqKeysOk req` (a request's keys are a store's: `store_keysOk`
    from the node's invariant, `reqKeysOk_of`; at most `1 + 256 + 256^2` entries, so ~1.2 MB);
    `coordSpec`'s Write `kvOk k x`, RemoveNode `a.length < 256`; `craqCtx` adds `∀ b ∈ chain,
    b.length < 256` (AddNode's and Update's addresses). The client interfaces (`isNodeClient`,
    `isCoordClient`, `isNodeSvc`'s Read, `isCoordSvc`'s Write) take these as pure premises; the
    store's `Commit` returns `keyOk k` (its item's `valsElem`), so `commit`/`sendCommitToPrev` have
    it. The kit: `KIn`'s keys are `keyOk` (`inOk`; `Gen`'s keys are 2 bytes), the removals' are
    server addresses (`serverAddrs_short`). Not a statement change.
  * **Step bound** (dsv-steps63, notes/dsv-epaxos.md "Step bound 2^63"): the statement is
    `DistDeploy … → Robust [] (system σ) g (2 ^ 31) (2 ^ 63)` (no `threads` binder); the proof calls
    `robust_of_distProtoLisRBT … (2 ^ 31) (2 ^ 63)`.
  * **strings.Cut/TrimLeft** (Net's `DialHTTP.wp` takes them as pending callee hypotheses until the
    pin includes Perennial ed1955557, not in b3f2fc485): NOT statement premises. `Link.lean`'s
    `StringsPending GF` class (fields `cut`, `trimLeft`: Perennial's `EtcdGrove.strings.Cut.spec`,
    `TrimLeft.spec`) feeds `rpcClientSpecs`' `DialHTTP.wp sp.cut sp.trimLeft`; `wp_Server`,
    `wp_Client`, the client factories take `[StringsPending GF]`; the top-level proof is
    `craq_remote_robust_of_strings (hs : stringsPending.spec) : craq_remote_robust.spec`. **The
    closed `craq_remote_robust` waits for the pin bump**: then it is
    `craq_remote_robust_of_strings (fun => ⟨Perennial's Cut proof, TrimLeft proof⟩)` and
    `StringsPending` can go.
  * **Non-vacuity**: `examples/craqnet/NonVacuityLinked.lean` (test-only, no importer):
    `nonvacuous_premises`, the statement's premises in its own form: `net.rpc`/`net.http`
    `InitHyp` (theorems over local axioms `local_rpc_wp_init`/`local_http_wp_init`; the
    inithyp-instances tool of math-rand-isinit walks a kit's own packages only), `LogHyp` (three
    local axioms), `∃ rs` (`local_rpcHttpServe`: local opaque `local_muxOwner`/`local_muxHas`, local
    axioms for persistence, `HandleHTTP`, `ListenAndServe`) with the eleven `RpcBoot`s (local axioms,
    one per command). No unsatisfiable field.
- **P14. Tenth agent (2026-11-24, from the ninth agent's unpushed 296417da29): lean 37bfea9484.**
  Merged `origin/lean` 37bfea9484 (dsv-steps63 and the land-queue batches landed; Perennial still
  b3f2fc485): no conflict (the ninth agent's merge of 5c7f7d2e59 had resolved the Net/ and generated
  ones, lean's side), and the branch's diff against lean is craq's own files only. `gen-init --check`
  (274), `kitgen --check`, `goose.py --check --project dsv-craq` clean without regenerating.
  Dropped: `Dsverify/Scratch/CraqAxioms.lean` (scratch), and **the axiom-based
  `examples/craqnet/NonVacuityLinked.lean`** (P13's: every instance was a local axiom, the eleven
  `RpcBoot`s each its premise restated; the coordinator's rule for this round is no new axioms, so
  only axiom-free instances count; the file is in history, c17f4f4c68/296417da29). **Non-vacuity,
  what remains** (no premise class of craq's statement has an axiom-free instance at this pin):
  `net.rpc.InitHyp`/`net.http.InitHyp` (their closure reaches names-only initializers: dsv-gryff's
  walks rest on local axioms for them), `LogHyp` (Perennial's `log` is names only), `RpcHttpServe`
  (net/http's server, `DefaultServeMux`, `rpc.HandleHTTP`: not in Net yet), the eleven `RpcBoot`s
  (net/rpc's and net/http's initializers: names only). **Strings**: lean's pin b3f2fc485 does not
  contain Perennial ed1955557 (52d62e83c does), so `DialHTTP.wp` still takes `h_Cut`/`h_TrimLeft`
  and the theorem is `craq_remote_robust_of_strings`; after the pin bump: `craq_remote_robust :=
  craq_remote_robust_of_strings (fun => ⟨…Cut proof, …TrimLeft proof⟩)`, delete `StringsPending`.

- **P15 (2026-11-24, eleventh agent): onto the real-`fmt` pin.** Merged `lean` af4fd74b00 (Perennial
  52d62e83c), then b64d2397f8 (Perennial d9c8c1d97; no conflict either time); the twelve generated
  `cmd/*/PkgTable.lean` regenerated (`etc/gen-init.py`: the pins' new packages, `internal/abi`,
  `internal/gomodel`, `reflect`, in the closures). First (at 52d62e83c) a bridge
  `Proof/strings/FromPerennial.lean` turned Perennial's `strings.Cut`/`TrimLeft` proofs into the
  specs Net's `DialHTTP.wp` took as hypotheses; lean's 57d66cdcee then discharged those hypotheses
  in Net itself (and deleted `Spec/strings/{Cut,TrimLeft}.lean`), so the bridge went and
  `Link.lean`'s `rpcClientSpecs` passes `net.rpc.DialHTTP.wp` as is. `StringsPending` and
  `stringsPending.spec` deleted; `craq_remote_robust_of_strings` became `craq_remote_robust` (no
  hypothesis). The statement is unchanged (its step bound already `2 ^ 63`).

## dsv-fix2 (2026-11-25): net/rpc's and net/http's package facts from `Net/`

The kit's net/rpc and net/http are `Net/`'s packages for their initializations too: their facts
(`Net/Proof/net/{rpc,http}/PkgInit.lean`) and `wp_initialize'` (`Net/`'s interim axioms, by
`etc/gen-init.py`'s `NET_AXIOM_INITS`), so the statement's `net.rpc.InitHyp`/`net.http.InitHyp`
premises are gone (`Dsverify/Proof/net/{rpc,http}/Init.lean` deleted). The other net/rpc premises
stay: the command's initializer runs net/rpc's before anything runs net/http's, so net/http's first
run is inside net/rpc's, which `Net/`'s first-run axioms do not cover (notes/dsv-gryff.md,
"dsv-fix2"). Next: net/rpc's first run proved from its translated initializer (dsv-fix2b), then the
kit's net/rpc premises discharged from `Net/`'s specs.
