# dsv-vr: dsverify-lab's vr kit on the net extension (phase 6)

Branch `dsv-vr` (2026-11-23), off `origin/dsv-paxos` (`e3eaf5cd0d`). Plan:
`notes/dsverify-net-port-plan.md`, phase 6; the pattern: `notes/dsv-paxos.md`. Source: dsverify-lab
`master` `915f964`, `examples/vr/` (run **`vsr-bump-1`**, the end of vsr-net-1 → vsr-net-clients-1 →
vsr-bump-1: clients on nodes of their own, Perennial `3afd77e35`; proof `c8b5962` tag `final`, fork
`go-vsr` `9c4be18`; read only, nothing in the lab changed). Worktree `/shared/etcd-grove-dsvvr`.

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/vr/` (module `github.com/tangledbytes/go-vsr`, the fork's path): the fork's `pkg/{assert,client,events,ipv4port,log,network,queue,replica,time}` and `examples/{vsrkv,vsrwire}` unchanged; the kit `examples/vsrnet` rewritten onto `examples/lib/remote` (`kit.go`) with its twelve commands `cmd/{orch,client0..5,server1..5}`; `kit_test.go` runs the twelve machines in one process (real `encoding/json`, `log/slog`), the model's verdicts and the codec. Left out of the fork: `cmd/`, `internal/simulator`, `pkg/utils`, `examples/vsrspec` (the lab's) |
| translation | `etc/goose.py` project `dsv-vr` into the part `Dsverify/` (remote and `net` the part `Net/`'s, lintest and porcupine the main tree's); **names only, into the part**: the `encoding/json` model (`models/encoding/json`, `std_models`; `Dsverify/Code/encoding/json.toml`) and `log/slog` (`Dsverify/Code/log/slog.toml`). Every `Dsverify.GeneratedProof` module of the project builds |
| the protocol's proof | `Dsverify/Proof/github_com/tangledbytes/go_vsr/`: the lab's `VsrProof/X/Y.lean` at `X/Y.lean`, ported by editing. Done: `Model/Basic.lean` (the pure VR model, 1960 lines; the lab's `Harness.Model` key-value map restated there: `KvInput`, `KvOutput`, `kvStep`), `Ghost/Impl/Pure.lean` |
| trust base | `etc/tcb-collections/dsv-vr.txt` (roots `^Dsverify/Proof/github_com/tangledbytes/`; nothing linked yet) |

Module mapping for the rest of the port: `VsrProof.X` → `Dsverify.Proof.github_com.tangledbytes.go_vsr.X`
(the lab's `Spec/<pkg>.lean` hub files keep their place under it, as paxos kept its hubs);
`Vsr.Code.github_com.tangledbytes.go_vsr.*` → `Dsverify.Code.github_com.tangledbytes.go_vsr.*` (and
`GeneratedProof`). The translations of go-vsr's packages are the lab's line for line (same goose
output sizes: replica 3572, client 791, ipv4port 651, network 685 lines), but `events` (1321: the lab
excluded `Event.FromReader` by a goose configuration; here it is translated).

## What changed against the lab (so far)

- **The deployment is remote's.** The lab's orchestrator ran `harness/remote.RunRemote` (its
  driver, recorder and `check.KV`, the porcupine axiom); here `Orch` sends the configuration
  (`Configure`, the lab's `New`) and then runs `remote.Check` against **the kit's own model**,
  `kit.go`'s `Model` (a key-value map with pending puts: state `Cur` (the map) and `Pend` (puts of
  unknown outcome); an answered put takes effect, an answered get reads `Cur` or a pending put of its
  value at its key, which then leaves `Pend`; the state is the most permissive configuration, so the
  step is deterministic). Inputs `In{Put, K, V}`, outputs `Out{Unknown, Done, Found, V}` (`Done`: an answered put; remote's
  `pend_choice` needs outputs that encode apart, and a put's answer and a get's not-found were both
  `Out{}`), `Codec()` bytes (three header bytes). **`Equal` is true only with nothing pending** on
  either side (then the state stands for one configuration; with pending puts two histories may reach
  one state with different sets, so no `Equal` on them is sound; porcupine's cache only loses hits).
  Each client is a machine of its own (`remote.ServeClient`), so twelve machines.
- **Client `c` makes its go-vsr client before `ServeClient`** (paxos's finding: `ServeClient.spec`'s
  `newClient` is a persistent triple with precondition `True`; a second go-vsr client with id `c+1`
  would reuse its request numbers). The configuration wait (`waitConf`) is before it too.
- **Gen and choose use `primitive.RandomUint64`** (Perennial's any-value), not `math/rand`
  (Perennial's `math/rand` is names only; the lab had its own trusted model). `Gen(c)` takes no
  operation index (remote's `gen func(int) any`), so a put or get of `k0`/`k1` at random, a put's value
  `v<c><r>`; the lab alternated put/get of one key per round.
- **Addresses** are loopback constants (`Addrs`, `CfgAddrs`, `ClientAddrs`: `127.0.0.1:75xx`, a port
  per machine and role), not `ports(addrs, ConfigPort)` (`strings.Split`). The first operation of a
  client waits `StartMs + c·StaggerMs` (the lab's `Start(c)`, which remote has no hook for).
- **The kit links `vsrwire`** (a blank import in `kit.go`; finding 7).
- **`RegisterJSON` is hand-written** (`register.go`: nothing, in the real build;
  `register_goose.go`: nothing, under goose), not jsongen's: see "Findings".

## State

### Round 5 (2026-11-23 night; the current handoff; Round 4 and older are history)

Branch merged with `origin/lean` `af67426be3` (Perennial pin unchanged, `160fcf12a`).

**log/slog proved** (no premise left):
- Translation: `log/slog` is the landed model `models/log/slog` translated with its bodies
  (`std_models += ["log/slog"]`, `Dsverify/Code/log/slog.toml` translate-all; `goose --check` clean).
- Specs, one canonical copy: `Dsverify/Spec/log/slog/Logger.lean` (`isLogger`, `argOk`,
  `NoFmtArg`, `New.spec`, `DiscardHandler.load_spec`, `Logger.{Debug,Info,Warn,Error}.spec`,
  `Debug.spec`); vr's `Spec/sloglib.lean`, `Proof/replica/LibHyps.lean`, `Proof/network/LibHyps.lean`
  deleted (importers now import the canonical module). Nothing in Net/ or the main tree had slog specs.
- **Narrowed to Go's truth:** `New.spec` is at `dhV` (DiscardHandler's value,
  `interface.mkOk discardHandler.ty #(zero_val discardHandler)`, `Dsverify/Proof/log/slog/Base.lean`)
  only: Go's `New(nil)` panics. `DiscardHandler.load_spec` returns `h = dhV`; `isLogger l` is
  `l`'s handler field `↦□ dhV` (was: some handler). `argOk` on the logging calls stays (the vr call
  sites state it); the proofs do not use it (a discard handler formats nothing).
- Proofs: `Dsverify/Proof/log/slog/Logger.lean` (`DiscardHandler.load_proof`, `New.wp_proof`,
  `Logger.{Debug,Info,Warn,Error}.wp_proof`: `Enabled` of `discardHandler` is false;
  `Debug.wp_proof`: the default logger's `defaultHandler` is enabled from `LevelInfo` up).
- Init: `log.slog` left `HYP_INITS` (now `['encoding.json']`) for `PKGS`; its fact `pkgState`
  (`Base.lean`: `DiscardHandler ↦□ dhV`, `defaultLogger ↦□ dl`, `dl`'s handler `↦□ defHV`); its
  `Init.lean` generated (`etc/dsv/vr.py` `SPECIAL['log.slog']`). `log.slog.InitHyp` is gone: the
  statement lost the premise `∀ G L, log.slog.InitHyp remoteGF`.
- `LibHyps` keeps only `connReaderOk` (docstring: true of Go; waits on Perennial's
  readatleast-prefix, mit-pdos/perennial#688). `Link.lean` passes the slog proofs.

### Round 4 (2026-11-23 evening; history)

Branch merged with `origin/lean` `76c00a8d81` (Perennial pin `160fcf12a`, `/shared/perennial-160fcf12a`);
PkgTables regenerated (`etc/gen-init.py`, PERENNIAL_DIR set; `--check` clean); `goose.py --check
--project dsv-vr` clean. **All Lean builds run on fk-lean1** (`/shared/tmp/fklean1-check.sh`).

**Remote adapted** (remote-serveclient landed, lean `866c324ee6`; `remote-adapt.md` items 1-5):
- `Start.lean`: `mapCtx_alloc ⊤ clientAddrs 24`: 24 call units per client address (`Check`'s 8
  operations × `readTries`); the orchestrator's share carries them (`budUnits a 24`), client `c`'s
  share the pure `ρ.bud (clientAddrs.getD c []) = some 24`.
- `OrchProof.lean`: `Orch.spec` takes the units; `wp_Check … 24 (by decide)`.
- `ClientProof.lean`: against remote's own `ServeClient.spec` (`ServeClientB.spec` gone).
  `newClient` is the one-shot WP: it returns the system made before, consuming the exclusive
  `sysRes γ c sys 1` (go-vsr client, `nextReq`) and starting the far side's count (`budUsed_zero`).
  `sysTok γ c a sys := ∃ n m, ⌜n ≤ m + 1⌝ ∗ sysRes γ c sys n ∗ budUsed a m`; `Op_svcOp` counts each
  call's unit with `budUsed_add` (`m + 1 ≤ 24`), so `Op.spec`'s `n < 2 ^ 28` holds: the budgets bound
  the request counter. `Link.lean`'s `wp_Client` passes `EtcdGrove.remote.wp_ServeClient`.
- `Mains.lean`: the client mains carry the budget fact, the orchestrator's the units.

**The JSON dependency, separated** (`examples/vsrnet/JsonHyps.lean`; read its header): every
`encoding/json` premise is a field of one `Prop`, `JsonHyps` — `Unmarshal`, `NewEncoder`,
`Encode_conn` (`encoding.json.*.spec`, `Proof/events/LibHyps.lean`), `newDecoder`, `Decode_frame`
(`pkg.events.*.spec`, `Spec/events.lean`), `codecOk` (`vsrnet.codecOk`, `Spec/json.lean`) and
`RegisterJSON` (`RegisterJSON.codecSet_spec`: the kit's `RegisterJSON()` leaves `codecSet`) — plus
the data classes `DecoderRep`/`EncoderRep` and `encoding.json.InitHyp`. `codecSet` is no longer a
precondition of any machine (`pkgStates`/`srvLibState` gone): `mkClient`/`runReplica` get it from
`RegisterJSON`'s call. **`RegisterJSON.codecSet_spec` is false of today's placeholder** (empty
`RegisterJSON`), so `JsonHyps` has no instance until jsongen's codec is in: the statement is vacuous
until then, by design (the JSON premises are visible, not hidden).

**Other premises** (`examples/vsrnet/LibHyps.lean`): `LibHyps` = the seven `log/slog` specs and
`connReaderOk` (finding 5; now over Net's landed `net.connReadE`, vr's copy gone).

**The statement** (`Dsverify/Spec/github_com/tangledbytes/go_vsr/examples/vsrnet/TopLevelRobustness.lean`,
`vr_remote_robust.spec`), in the landed kits' shape:
premises `∀ G L, encoding.json.InitHyp`, `∀ G L, log.slog.InitHyp`, `∀ [DecoderRep] [EncoderRep]`,
`∀ G L π, LibHyps`, `∀ G L π, JsonHyps`; then `DistDeploy vrKitAddrs (system σ) g →
Robust [] (system σ) g threads (2 ^ 63)`. Proof: `examples/vsrnet/TopLevelRobustness.lean`
(`robust_of_distProtoRB`, `vr_start`, each machine's `wp_boot` from its generated `wp_initialize'`
and `wp_main`). Definitions: `TopLevelDefs.lean` (`boot`, `system`, `vrKitAddrs`, `heapAt`); the
address lists moved to `Wire/Addrs.lean` (defs) so the statement imports no proof module.
Links: `examples/vsrnet/Link.lean` (was `Linked.lean`), namespace `Perennial.EtcdGrove.dsvvr`
(`proof_roots.namespace()` = `Perennial.EtcdGrove.`, as on lean).

**One canonical copy:** `bufio.errWf`/`errOrNil` moved to `Dsverify/Proof/bufio/ErrOrNil.lean`
(swiftpaxos's `lib/Bufio.lean` and vr's `Spec/jsonlib.lean` had identical copies; J1's main-tree
`Proof/bufio/ErrOrNil.lean` will replace it). `dups.py` over all landed kits: no real duplicate left.

**Tier check:** 144 violations, all vr's older files (78 defs→linking, 30 defs→proof, 21
proof→linking, 15 proof→proof: package proofs importing callees' `Results`, `Mains`/`KitLib`
importing proofs); the new files (statement, `TopLevelDefs`, `JsonHyps`, `LibHyps`, `Link`) add
none. Restructure before landing.

**Checks (round 4, head `22684c5047`):**
- fk-lean1: `lake build` of vr's `TopLevelRobustness` and the five landed ones (swiftnet, epaxosnet,
  paxosnet, rabianet, quepaxanet): green (4990 jobs). `#print axioms` (`lake env lean` of a scratch
  file there) of `vr_remote_robust` and the five landed theorems: `propext`, `Classical.choice`,
  `Quot.sound` only. (The `sorry` warnings in the log are goose's generated-proof stubs, e.g.
  `GeneratedProof/log/slog.lean`, not in any closure.)
- Here: `gen-init.py --check` clean (271 files); `goose.py --check --project dsv-vr` clean;
  `proof_roots.namespace()` = `Perennial.EtcdGrove.` (= lean's); `tier-check`: 144 new violations
  (above); `dups.py`: no real duplicate. `errorf-wrap-check.py` needs `.lake/tcb.json` of a full
  build (`tcb-report.py` refused: 409 modules out of date on fk-lean1's worktree), so not run; vr's
  Go calls no `fmt.Errorf` (its inits use `errors.New`).
- Fixed on the way: `Proof/network/Ghost.lean` (lean's `OpError.Error` model maps an empty
  `AnyString` to `"error"`).
- No landed statement changed (Upamanyu's rule): the `bufio.errOrNil` move only relocates two
  identical definitions; swiftpaxos's and epaxos's statements are untouched and rebuild green.

**Not done, not JSON:** `log/slog` (7 specs in `LibHyps`, plus `log.slog.InitHyp`): the landed
`models/log/slog` translates with bodies (tried: `std_models += ["log/slog"]`, `slog.toml`
translate-all; patch in the coordinator's scratchpad `vr-slog-translate.patch`), so the specs could be
proved from the model (DiscardHandler's `Enabled` is false) and the InitHyp generated; needs a
gen-init entry with the package fact (the two globals) and the proofs. Note `New.spec` as stated
(any handler) is **false of Go** (`New(nil)` panics): narrow it to `DiscardHandler`'s value when
proving it. `connReaderOk` (finding 5) needs Perennial's `ReadAtLeast` premise narrowed to
`ys.length < min` (perennial-readatleast-prefix) or an exact count in Net's `Conn.Read` spec.

**After J1 and jsongen land:** (1) regenerate the kit's codec with jsongen (`json.toml` as is; the
real `RegisterJSON` replaces `register*.go`); (2) prove `RegisterJSON.codecSet_spec` from J2's
`SetCodec` spec; (3) prove `codecOk` (jsongen's codec for the kit's types: the lab's ~8k lines,
plus `log.Logs`' `MarshalJSON`/`UnmarshalJSON`, which call `json.Marshal`/`Unmarshal` back through
the registered codec: a recursive dependency the proof must cut, e.g. by Löb induction); (4) move
`JsonHyps`' `Unmarshal`/`NewEncoder`/`Encode_conn` to J1's statements (`codecSetWith`/`codecOkWith`
at our `kitFn`s), drop `Dsverify/Code/encoding/json.lean`, `Spec/jsonlib.lean`,
`Dsverify/Proof/bufio/ErrOrNil.lean` and `encoding.json.InitHyp` (J1 proves the init); (5) J1 lacks
`NewDecoder`/`Decode` and `Marshal` specs, which vr needs (its decoder hypotheses, `Logs.MarshalJSON`).

Done: the Go (`go vet`, `go test ./...` green: the deployment test, ~5 s, the fork's own tests), the
translation (builds), the pure model, **the package initialization** (step 1) and **the ghost layer**
(step 2; `lean-check` clean). **No `sorry`, no axiom in the part's vr files**: every node's
`wp_initialize'` (orch, server1 checked) prints Lean's three axioms only, over the two init
hypotheses (below).

**Configuration (since the dsv-infra merge, `4771f33ec4`):** the kit's goose project and gen-init
entries are `etc/dsv/vr.py` (format `etc/dsv/README.md`; `HYP_INITS` is what was `DSV_HYP_INITS`
below); `etc/goose.py` and `etc/gen-init.py` are dsv-infra's, unchanged. `gen-init.py --check` and
`goose.py --check --project dsv-vr` clean.

Step 1, as done: `Base.lean` for every vr package (fact `True` but `events`'), the hand-written
`Dsverify/Proof/{encoding/json,log/slog}/{Base,Init}.lean` (fact `True`; `Init.lean`'s class
`InitHyp GF`, a `Prop`, is the hypothesis, its `wp_initialize'` is read off it), and the additive
gen-init entry (`DSV_VR`, `DSV_HYP_INITS`: gen-init treats the two packages as external, imports
their `Init.lean` instead of Perennial's `Link`, and adds `variable [<pkg>.InitHyp GF]` to the
sections of every generated file whose package's closure holds them, `dsv_hyp_fix`; `SPECIAL`
entries for `events` (its error, the hook's mutex and `frameDecoder`), `network` (`ErrNoConn`) and
`vsrwire` (its `init()`, through `pkg/events/SetFrameDecoder.lean`)). Facts weaker than the lab's
for now: `events`' `hookKnown` keeps only `frameDecoder ↦ _` under the mutex (the lab's also the set
decoder's spec and the flag `γh`), `vsrwire`'s is `True` (the lab's `frameDecoderSet`), `network`'s
`True` (the lab's `ErrNoConn` value); each is strengthened with the proof that needs it.

Step 2, as done: `Ghost/Impl/*`, `Ghost/System` over any `GF` (`[GooseGlobalGS .hasLC GF]`, `[HasExt
netExt]`); the client's atomic update `AU <{∃∃ σ, absOwn γ σ}> @ ↑clientN, ∅ <{…}>` is now
`Impl.AUof g i Q`, remote's one-shot update (`remote.lin`'s shape, relational as the lab's AU:
`|={⊤ \ vsrE, ∅}=> ∃ σ, absOwnI g σ ∗ ∀ σ' o, absOwnI g σ' ∗ ⌜kvStep σ i σ' o⌝ -∗ |={∅, ⊤ \ vsrE}=> Q σ σ' o`,
`vsrE` the namespace `vsr` all the layer's invariants are in); `lin_commit` fires it as paxos's
`opAU_commit` (`fupd_mask_subseteq`). The mask premises `↑clientN ⊆ E` (+ the disjointness of
`clientN`) became `⊤ \ vsrE ⊆ E`. Step 3 instantiates remote's `RBase.Eop` with `vsrE` and
`sysState` with `absOwn`.

**Since the resume (2026-11-23 ~03:50 UTC; dsv-infra `884cb306c9` merged):**
`examples/vsrnet/CodecProof.lean` (`Codec.wp_proof`: `Codec()` meets `codecOk (kvR g)`; `outOk_out`)
and `examples/vsrnet/KitProof.lean` (`wp_digit`, `wp_digits`, `Gen.spec`/`Gen.wp_proof`: `Gen` meets
lintest's `genSpec` with inputs `∃ i : KIn, x = inV i.1`; `kin_get`/`kin_put`); both `lean-check`
clean, no `sorry`. `digit`/`digits`/`Gen` need no `isPkgInit` (genSpec's precondition has none).
Ported since (lean-check clean, no `sorry`, committed): the leaves `Spec/{queue,assert,time,vsrkv,ipv4port}.lean`
+ `Proof/<p>/*.lean` (no hypotheses: Perennial proves `time.Now`, `Time.UnixNano`, `strings.Split`;
**ipv4port changed**: the kit's addresses share one IP (`127.0.0.1:75xx`), so `ByLess` sorts by port,
`ipv4port.portLt`, over `ipv4port.addrs` (a hand copy of `Addrs()`; the lab's single port made `Less`
always false and the order empty); `ipCfgDef` states the exact IP and `a ∈ addrs`; client/replica
`New` callers must name `portLt`/`addrs`), the pure JSON theory `Proof/jsoncodec/{ScanDef, StrSteps,
NumSteps, ScanSteps, ScanBounds, ScanIdx, Enc, ScanLemmas, ScanTop, Facts, Inj, Frame, DigVal}` and
the wire `Wire/{LineBound,Basic}.lean` (`protoOf γ : Proto GF`, connection ids `Nat`; `protos γ` over
`addrProto` of `VsrWire.addrs`, a second hand copy of `Addrs()`: merge with `ipv4port.addrs` and prove
`Addrs()` returns it; the configuration section moved to `examples/vsrnet/Conf.lean`).
Done too: `examples/vsrnet/Conf.lean` (the configuration protocol, 859 lines, lean-check clean, Lean's
three axioms over its hypotheses `net.{Dial,Listen,Listener.Accept,Conn.Write,Conn.Close}.spec` and
`conn_readerOk` (finding 5); `CfgAddrs.wp_proof`, `wp_choose`, `wp_Conf_encode`, `wp_decode`,
`wp_sendConf`, `Configure.wp_proof`, `conf_size` (the orchestrator's `ghost_size`), `conf_learn`,
`wp_awaitConf`, `waitConf.wp_proof`; `confProtos γ` covers all 12 cfg addresses, the orchestrator's
unused one too: the start sets it). Was in progress: `confBytes`, `ConfOk`, `cfgAddrs`, `confProto`, `ackProto`; `choose`, `encode`, `decode`,
`sendConf`, `Configure`, `awaitConf`, `waitConf`; `io.ReadFull` over a connection through a hypothesis
`conn_readerOk` mirroring dsv-bufio's `Net/Proof/net/ConnIo.lean`), and the spec hubs
`Spec/{json,log,events,vsrwire,network,client,replica}.lean` (+ `Proof/network/Defs`, `Proof/log/*`).
**Hubs done** (`525da02193`, clean): `Spec/{log,events,json,vsrwire,network,client,replica}.lean`,
vocabulary `Spec/jsonlib.lean` (the repository's `models_lab.jsoncodec.JsonCodec`/`marshalOk`/…;
`encoding.json.kitFn` = the kit package's `jsonMarshal`/`jsonUnmarshal` (check against jsongen's names
when it exists); `kitCodecOk`, `codecFns`, `codecSet`; **`class encoding.json.DecoderRep GF`**, a data
class (`decOk dec rd I R U`, `decErr dec rd`) standing for the model's `Decoder` fields (names-only
translation): no instance, a section variable of the hubs from events on — at the statement it must be
a premise like the InitHyps, or be replaced by the model's real `Decoder` representation when its Lean
half lands) and `Spec/sloglib.lean` (`log.slog.isLogger`); `Proof/network/Defs`, `Proof/replica/Inv`,
`Proof/jsoncodec/{Codec,Valid,Stream}`, `Proof/log/Logs` (NewLogs, Len, OpAt, ClientIDAt, RequestIDAt,
After, Add, Merge proved). Changed against the lab: connections are `net.isConn c cn s a` (Nat ids),
`events.{w,r}stream` take `c : GoInterface`, `rstream` over `DecoderRep`; the hook predicates are
`events.hookLockInvFull`/`hookKnownFull` (Base's weaker `hookKnown` to be strengthened);
`events.initialize'.spec` dropped (generated Init); the lab's theorem `codec_ok` is the hypothesis
statement `vsrnet.codecOk : Prop` (finding 2); `vsrnet.jsonCodec` a local instance. Left of log:
`Proof/log/{Json,Results}` (need Marshal/Unmarshal hypotheses).
**Done after the hubs:** `Proof/{events,vsrwire}/*` (`1415bd3b4b`; Results on Lean's three axioms over
the hypotheses in `Proof/events/LibHyps.lean`: `encoding.json.Unmarshal.spec`, `NewEncoder.spec` (over a
new data class `encoding.json.EncoderRep GF`, `encOk enc w`, mirroring `DecoderRep`: no instance), and
`Encoder.Encode_conn.spec` (the lab's `jsonstream.wp_Encode_conn`, stated over `net.isConn`/`sendTok`
at the kit's codec rather than a generic writer contract: a generic one needs `errOrNil` of the
writer's errors and no `OpError.Error` spec exists), plus the hubs' `vsrnet.codecOk` and
`events.Decoder.Decode_frame.spec`); `Proof/client/*` (Results on Lean's three axioms over
`network.TCP.Send.spec`, `∀ jc, events.Event.ToWriter.spec`, `log.slog.Logger.{Error,Debug}.spec`;
`client.addrs_eq : VsrWire.addrs = ipv4port.addrs := rfl`; `sort.wp_Sort` at `portLt`). The slog
vocabulary `log.slog.argOk` (ArgWf ∨ errAny ∨ NoFmtArg) and the `Logger.*` specs live in
`Proof/replica/LibHyps.lean` (canonical; client and network import it; move to `Spec/sloglib.lean`
later). `Proof/network/*` (`0d3e2b63df`; Results on Lean's three axioms over `net.{Dial,Listen,Listener.Accept,
Conn.Close,Conn.RemoteAddr}.spec`, `events.{Event.FromDecoder,newDecoder,NewNetworkEvent}.spec`,
`log.slog.Debug.spec` (`Proof/network/LibHyps.lean`); `OpError`'s and `TCPAddr.String`'s strings
proved via the extension's `AnyString`; internal specs over `net.connAt`/`isListener`/`netLis`; no
`Log.lean` (the lab's slog model is a hypothesis)). Network findings: (a) under `attribute [local
instance] GooseGlobalGS.gooseInvGS` a lemma's fupd is not eliminable by `imod` inside a WP goal (the
semireducible instance does not unify with `goose_irisGS.invGS`): drop the attribute in files with
such lemmas; (b) `json.NewDecoder` swallows `recvTok` (into `decOk`), so `handleConn` takes the
connection's `connIs` before making the decoder (and `Send` before calling `f`).
`Proof/replica/*` (`fb9c971261`, 32 files clean; `New`, `Submit` on no hypotheses; `Run` over the four
`log.slog.Logger.*` specs, `∀ jc, network.TCP.Send.spec`, `∀ jc, events.Event.ToWriter.spec`, bundled as
`replica.Hyps` (`Proof/replica/Hyps.lean`) for the handlers; discharge the last two from network's and
events' Results). Note: `log.slog.NoFmtArg` (no `String()`/`Error()` method) is as faithful as the lab's
slog model; the kit's logger is `slog.New(slog.DiscardHandler)`, which reads no argument, so a narrower
hypothesis about that logger could replace it.
**All package proofs are done.** Next (in progress by helper agents): the kit layer
(`examples/vsrnet/`: `Orch`, `Client`/`Op`/`mkClient` over remote's `Check`/`ServeClient`;
`Server`/`runReplica`), then `Mains`/`Linked`/`TopLevelRobustness` as paxos's (the statement
`vr_remote_robust`, the start's ghost allocation and protocols, linking every Results theorem and
leaving only library hypotheses), `etc/tcb-collections/dsv-vr.txt`.
**Kit layer (`fc8f1bbe4b`, clean, Lean's three axioms over their premises):** `OrchProof.lean`
(`Orch.spec`/`Orch.wp_proof`: Configure (with `conf_size`) then remote's `Check`; `kvS_pendDec`, masks),
`ClientDefs.lean` (`sysRes γ c sys n`, the client machine's resource; `reply_short`: a valid reply's
result < 2^16, so `Op`'s output is a `KOut`), `OpProof.lean` (`Op.spec`/`Op.wp_proof`, one call, from
`slotUpd (kvR γ.gn) i Ψ`), `MkClientProof.lean` (`mkClient.spec`; precondition `pkgStates` =
`frameDecoderSet ∗ codecSet ∗ ErrNoConn`'s value: package facts missing, see events' open item;
hypotheses `slogNew.spec`, `slogDiscard.spec` (DiscardHandler's type is names-only: no points-to)),
`ClientProof.lean` (`Client.spec`/`Client.wp_proof` over **`ServeClientB.spec`**, finding 6).
`ServerProof.lean` (clean): `srvShare γ id` (the lab's `serverRes`: protos, confProtos, sysInv,
regInv, replica `id-1`'s initial share, given to every server machine since N is known only after
`waitConf`), `srvLibState` (= the client's `pkgStates`: `frameDecoderSet ∗ codecSet ∗ ErrNoConn`),
`runReplica.spec`/`wp_proof`, `Server.spec`/`Server.wp_proof` (replica's `Run` hypotheses discharged
from network's and events' Results). New slog hypotheses `log.slog.New.spec`,
`log.slog.DiscardHandler.load_spec` (duplicates of MkClientProof's `slogNew`/`slogDiscard`: merge).
**Round 3 (2026-11-23, after #24 comment 7092077493; branch merged with `origin/lean` 07268ddb57,
Perennial 7b2259a12):** the work the blockers do not block.
- (a) **Package facts.** `pkg/events/Base.lean`'s fact is the hook's lock with its flag
  (`hookKnownFull`; `hookLockInvFull γh`: `frameDecoder` is `nil` with the flag `[]`, or
  `kitFrameDecoder` = `vsrwire`'s `decodeFrame` with `[()]`); `examples/vsrwire/Base.lean`'s is
  `frameDecoderSet`; `pkg/network/Base.lean`'s is `errors.newVar ErrNoConn noConnMsg`. Their
  generated `Init.lean`s prove them (`etc/dsv/vr.py`: events' init allocates the flag with
  `mono_list_own_alloc`; vsrwire's init calls `pkg/events/SetFrameDecoder.lean`'s
  `wp_SetFrameDecoder`, no hypothesis; network's keeps `errors.New`'s field). **Design change
  against the brief:** the lock invariant names the function (`f = kitFrameDecoder`) instead of
  storing its spec (`frameDecOk f`, the lab's): `frameDecOk` mentions `DecoderRep`, `JsonCodec`,
  `NetProtoGS` and the json/net `Assumptions`, which as package-fact parameters would have had to
  propagate into every importer's `IsPkgInit` instance and every proof section; with the name, the
  fact names no class, the `Spec/events.lean` ↔ `Base` cycle is gone, and **no InitHyp-style
  class for `Decode_frame.spec` is needed**: `FromDecoder`'s proof gets `frameDecOk` from
  `decodeFrame`'s spec (`Proof/vsrwire/Hook.lean`), so `events.Decoder.Decode_frame.spec` is an
  ordinary hypothesis of `events.Event.FromDecoder.wp` (it was one of `vsrwire.init0.wp`).
  `NewTCP.spec` no longer takes `ErrNoConn` (the package fact); `pkgStates`/`srvLibState` are
  `codecSet` alone; `KitLib.kit_frameDecoderSet` reads the hook from `isPkgInit` of the kit.
  **Finding 7:** nothing linked `vsrwire` in this port (the lab's kit linked it through its
  generated codec, `json_gen.go`), so the hook was never set and `frameDecoderSet` was unsatisfiable
  in the deployment (the old `pkgStates` premise was vacuous); `kit.go` now imports `vsrwire`
  blank (`go test` green; translation regenerated).
- (b) **slog:** one copy of each hypothesis: `log.slog.New.spec`, `DiscardHandler.load_spec`,
  `Logger.{Debug,Info,Warn,Error}.spec` in `Proof/replica/LibHyps.lean`, `log.slog.Debug.spec` in
  `Proof/network/LibHyps.lean` (MkClientProof's `slogNew`/`slogDiscard` merged away). Narrowing to
  the `DiscardHandler` logger considered, not done: `DiscardHandler`'s type is names-only, so its
  value cannot be named; a narrower hypothesis needs a shared `dh : GoInterface` across
  `load_spec`, `New.spec` (at `dh`) and the `Logger.*` specs (on loggers holding `dh`, where
  `argOk` could go: a discard handler formats nothing). Worth doing with the statement.
- (c) **Addresses:** one list, `VsrWire.addrs` (`Wire/Addrs.lean`); `ipv4port.addrs`,
  `client.addrs_eq` gone; `KitLib.wp_Addrs` proves `Addrs()` returns it (one copy; MkClientProof's
  and ServerProof's duplicates of `wp_Addrs`, `wp_RegisterJSON`, `wp_logger` merged into
  `examples/vsrnet/KitLib.lean`).
- (d) **net linked:** `net.Dial`, `Listen`, `Listener.Accept`, `Conn.Write`, `Conn.Close`,
  `Conn.RemoteAddr` are `Net/Proof/net/*`'s `wp_proof`s (network `Results.lean`, `Orch.wp_proof`,
  `Client.wp_proof`, `runReplica`/`Server.wp_proof` no longer take them); `events.NewNetworkEvent`
  is events' proof. `net.Conn.Read` stays behind `connReaderOk` (finding 5).
- (e) **Start, mains, links** (no statement): `examples/vsrnet/Start.lean` (`vrKitAddrs` =
  `VsrWire.addrs ++ cfgAddrs ++ clientAddrs`; `orchShare`, `clientShare`; **`vr_start`**: from
  `regCtx` and the addresses unset, `ghost_alloc`, the three address groups' protocols, remote's
  `mapCtx_alloc` and `pend_alloc` over `absOwn γ`, and every machine's share),
  `examples/vsrnet/Mains.lean` (the twelve `wp_main`s, from `Orch.spec`/`Client.spec`/
  `Server.spec`), `examples/vsrnet/Linked.lean` (`LibHyps`, one `Prop` bundling the 14 library
  hypotheses; `wp_Orch h`, `wp_Server h`, `wp_Client h wp_ServeClientB`: every package result
  linked; `wp_Check` remote's). All build (`lake build ...vsrnet.Linked`), Lean's three axioms.

**What is waiting on #24 (do not state `vr_remote_robust` before):** (1) remote's `ServeClient`:
`Client.wp_proof` (so `wp_Client`) takes `ServeClientB.spec` (newClient's WP as a resource, a call
budget); when remote gives it, `wp_Client` loses that premise and `clientShare` may need the budget
token from the start. (2) `codecSet` (in `pkgStates`/`srvLibState`, the `wp_main`s'
preconditions beyond the start's shares): needs jsongen's codec for `log.Logs` (finding 2) and its
registration's spec (`RegisterJSON` then gives `codecSet`). Finding 5 (`ReadFull` at 0) is
Perennial's `readatleast-prefix` (af905abba, not landed): then `connReaderOk` leaves `LibHyps`.
**Then the statement:** `TopLevelDefs`/`TopLevelRobustness` as paxos's: `robust_of_distProtoRB`
over `vrKitAddrs`, `vr_start`, the `wp_main`s with `wp_boot`; premises: `LibHyps`, the two
`InitHyp`s (`encoding.json`, `log.slog`), `DecoderRep`/`EncoderRep` (data classes; or the
model's representation when its Lean half lands); confirm `etc/theorem-loc.py` counts them;
`etc/tcb-collections/dsv-vr.txt`.

**(Earlier, done:)** helper agents proved `Proof/replica/*`, `Proof/client/*`, `Proof/network/*`,
`Proof/{events,vsrwire}/*`, each ending with `Results.lean` over hypotheses for library specs
(`Proof/<p>/LibHyps.lean`).
After the hubs, the package proofs are independent of each other (each imports only hubs):
`events`+`vsrwire`, `network`, `client`, `replica` (31 files, ~7k lines), then `Top/` (kit specs
`Orch`/`Client`/`Server`, mains, `Linked`, `TopLevelRobustness`). The Go JSON codec proofs
(`Proof/jsoncodec/Go*`, `vsrnetjson`, `jsonstream`) stay out (finding 2): hypotheses.

Step 3, done (but the kit specs `Orch`, `Client`, `Server`, next):
`examples/vsrnet/ModelSet.lean` (the pure side: `Rep s Cur Pend` (`s` holds `(lk Cur, Pend)` and every
configuration of `s` is dominated by it, `DOk`), `stepG` (the Go `step` as a function), **`stepG_pSeq`**
(`step`'s verdict is `pSeq kvB`'s and its next state represents the next set), `rep_init`, `rep_eq`,
the codec values' injectivity, `kvDec_box`), `examples/vsrnet/ModelProof.lean` (`wp_lookup`, `wp_has`,
`wp_push`, `wp_erase`, `wp_set`, `wp_equalPairs`, `wp_stepGo`, `kvRep`/`kvS`, **`Model.wp_proof`**:
`Model()` meets `isModel kvS`). `lean-check` clean, no `sorry`.

Step 3's first file: `examples/vsrnet/Kit.lean` (`lean-check` clean): the kit's inputs `KIn` (`InputOk`,
`InputBounded`, a key below 256 bytes: `EncIn` writes its length in a byte), the map's step as a
function (`kvFn`, `kvStep_fn`), linkv's pending-writes store `kvB` (gets reads, puts writes), the
Go values and `Codec()`'s bytes (`inV`, `outV`, `unkV`, `encInB`, `encOutV`), **the far side's store
`kvR g : RBase GF Store KIn KvOutI`** (`sysState := absOwnI g`, `Eop := vsrE`), and
**`lin_AUof`**: remote's `lin (kvR g) i Φ ⊢ AUof g i (fun _ _ o => Φ o)` (the store's linearization
point is the ghost layer's client update, which `ghost_register` takes). (Was remaining in step 3, now done above: the
porcupine model's set (`ModelSet.lean`: the configurations `(Cur, Pend)` stands for, as paxos's
`woSet`, and the decoding of porcupine's operations, `woDec`'s counterpart) and the Go model's proof
(`ModelProof.lean`: `lookup`, `set`, `has`, `erase`, `push`, `equalPairs`, `step` against linkv's set
step), then the kit's specs.)

**Building** (no full `lake build`): the worktree's `.lake` was seeded from `/shared/etcd-grove-netswap`
(same Perennial pin `9c3b81f30`): `.lake/packages` and `.lake/build/lib/lean` but the parts this
port never imports (RaftWitness, RaftTla, RaftNoAx, KvNet, WalTester, SpecPlan, PorcupineDag, Bbolt,
`Proof/go_etcd_io`, `Proof/k8s_io`, the examples' proofs but `examples/lib`): 4.3 GB. Lake rebuilt
Perennial and `Net/` where they differ; then `lake build <targets>` and `etc/lean-check.py`. Remember
`export PATH=$HOME/.elan/bin:$PATH`.

### Next steps, in order

1. (done) **Package initialization** (`etc/gen-init.py`, `dsv_inits`). Every package needs a `Base.lean`
   with its `IsPkgInit` instance (`define_is_pkg_init`; `instances()` finds it) before gen-init runs
   (it raises on a package without one). Facts (the lab's `Top/PkgStates.lean`): `True` but
   `network` (`errors.newVar ErrNoConn "network: no connection to the source address"`), `events`
   (`hookKnown`: `frameDecoder` and its mutex), `vsrwire` (`frameDecoderSet`). The two names-only
   packages (`encoding.json`, `log.slog`) must not get gen-init's trust-boundary axioms
   (`initFuncsOk`/`opaqueInitsOk`): use its `ASSUMED` mechanism (unused since 2026-10-17: importers
   take `initialize'.spec` as a hypothesis `wp_<name>`). The additive entry (tried, reverted until the
   `Base.lean` files exist):

   ```python
   DSV_VR = 'github_com.tangledbytes.go_vsr'
   DSV_VR_NODES = ['orch'] + [f'client{c}' for c in range(6)] + [f'server{s}' for s in range(1, 6)]
   DSV_PKGS += [f'{DSV_VR}.pkg.{p}' for p in ['assert', 'log', 'ipv4port', 'events', 'queue', 'time',
                                              'network', 'client', 'replica']] + \
       [f'{DSV_VR}.examples.{p}' for p in ['vsrwire', 'vsrkv', 'vsrnet']] + \
       [f'{DSV_VR}.examples.vsrnet.cmd.{n}' for n in DSV_VR_NODES]
   DSV_PROGRAMS.update({f'{DSV_VR}.examples.vsrnet.cmd.{n}':
                        f'Proof/{DSV_VR.replace(".", "/")}/examples/vsrnet/cmd/{n}/PkgTable.lean'
                        for n in DSV_VR_NODES})
   ```
2. (done) **The ghost layer** (`Ghost/Impl/{Defs,Basic,Alloc,Client,Lin,Step}`, `Ghost/System`): over a
   generic `GF` (the lab's fixed `netDistGF` gone, as paxos), and the client's atomic update
   `AU <{∃∃ σ, absOwn γ σ}> @ ↑clientN, ∅ <{…}>` in the registry (helping: the replica that executes
   a request first commits it) replaced by remote's one-shot update, as paxos's `opAU`
   (`remote.lin (kvR Γ)`, `lin_opAU`): the registry's entries hold it, `Lin.lean` fires it.
3. (done but the kit specs) **The far side's store and the model** (`examples/vsrnet/Kit.lean`, `ModelSet.lean`,
   `ModelProof.lean`, as paxos's): linkv's pending-writes store of the key-value map (`PendSpec`:
   gets are reads, puts writes), `RBase` with the VR state's abstract half as `sysState`; the Go
   `step` on `(Cur, Pend)` against linkv's set step (the representation: the configurations whose map
   agrees with `Cur` after some of `Pend` take effect, …; remote's lemma decides the exact direction
   needed); the model's Go functions (`lookup`, `set`, `has`, `erase`, `push`, `equalPairs`, `step`).
4. **The leaves** (`assert`, `queue`, `ipv4port`, `time`, `log`, `vsrkv`), then `events`/`vsrwire`
   (over the JSON hypotheses), `network` (the transport: `Net/Spec/net/*` + `Proto.lean`'s laws, as
   paxos's `NetProof.lean`: the lab's `Write`/`Read`/`Dial`/`Listen`/`Accept`/`Close` call sites
   become the canonical specs with `writeP`/`write_acc`, `read_au`, `dial_au`, `listen_au`,
   `accept_au`, `close_au`; JSON's `Encoder` writes through `net.Conn.Write` and its `Decoder` reads
   through `net.Conn.Read`, so the hypotheses below must be stated over a writer/reader the net
   library's laws give), `client`, `replica` (20 handler files), then the kit (`Top/` → `Kit`,
   `KitProof`, `Mains`, `Linked`), the statement and its proof.
5. The generated JSON codec's proofs (the lab's `Proof/vsrnetjson`, `Proof/jsoncodec`: ~8k lines)
   wait for jsongen's codec (finding 2); until then the codec's `JsonCodec` correctness is part of the
   JSON hypotheses.

## Hypotheses (missing model pieces; the coordinator's rule of 2026-11-23)

**Current set (round 3):** `examples/vsrnet/Linked.lean`'s `LibHyps` bundles every library
hypothesis the machines rest on: `log.slog.{New.spec, DiscardHandler.load_spec, Debug.spec,
Logger.{Debug,Info,Warn,Error}.spec}`, `connReaderOk` (finding 5), `events.newDecoder.spec`,
`events.Decoder.Decode_frame.spec`, `encoding.json.{Unmarshal.spec, NewEncoder.spec,
Encoder.Encode_conn.spec}`, `vsrnet.codecOk`; plus the classes `encoding.json.InitHyp`,
`log.slog.InitHyp` (Prop, section variables of the generated inits) and `encoding.json.DecoderRep`,
`EncoderRep` (data, no instance). The list below is the older plan.

Stated in Lean so far: `encoding.json.InitHyp GF` and `log.slog.InitHyp GF`
(`Dsverify/Proof/{encoding/json,log/slog}/Init.lean`: the packages' `wp_initialize'`, a class every
generated init theorem above them takes as an instance). The rest not stated yet; each to be a
hypothesis of the kit's theorems named after the lab's spec, until the piece lands:
- **encoding/json** (the model's Lean half: `models/encoding/json`'s translation with its bodies in
  `Net/` and its specs; `notes/dsverify-net-port-plan.md` 5.1 "For the Lean half"): the lab's
  `encoding.json.SetCodec.spec`, `Marshal.spec`, `Unmarshal.spec`, `Valid.spec`,
  `NewEncoder.spec`, `Encoder.Encode.spec`, `RawMessage.MarshalJSON.spec`,
  `RawMessage.UnmarshalJSON.spec` (`Harness/Proof/encoding/json/{Codec,Valid,Raw,Stream}.lean`), and
  `NewDecoder.spec`, `Decoder.Decode.spec` (the lab proved its Decoder in the kit,
  `VsrProof/Proof/jsonstream/`, over its own buffer policy; the model's is jsontext's, so these are
  hypotheses here), with `initialize'.spec` (the `ASSUMED` route above). Vocabulary:
  `Net/Proof/models_lab/jsoncodec/Codec.lean`'s `JsonCodec`, `marshalOk`, `unmarshalOk`, `scanOk`.
- **log/slog** (no model at all, Go or Lean, here or in Perennial; the lab had its own,
  `Harness/Proof/log/slog.lean`, 422 lines): `log.slog.New.spec`, `Logger.{Debug,Info,Warn,Error}.spec`,
  `log.slog.Debug.spec` (package-level), the `DiscardHandler` variable's value, `initialize'.spec`
  (`isInit`). go-vsr calls `slog.Debug` 15 times, `(*Logger).Debug/Info/Warn/Error` 84 times.

## Findings

1. **remote's `gen func(int) any`** has no operation index: the lab's `Gen(c, j)` (put then get of
   the same key per round) cannot be expressed; the port draws at random. A design note for remote,
   not a blocker.
2. **jsongen refuses go-vsr's `log.Logs`**: it has `MarshalJSON`/`UnmarshalJSON` (upstream go-vsr's,
   kept by the lab's vsr-bump-1 fork `9c4be18`; `models/internal/jsonvsr` copied the earlier fork
   `215992d`, which has none, and the plan says "the vsr kit fork has none"): `models/json/jsongen.py
   examples/dsverify/vr/examples/vsrnet/json.toml …` exits 2 on `log.Logs` (root and the
   `Logs` fields of `DoViewChange`, `StartView`, `NewState`). The lab's jsongen supported user JSON
   methods (`jencMarshaler`/`jdecUnmarshaler`). So the kit has no generated codec and no model build:
   either jsongen supports the two methods again (a models change) or the fork drops them (a change to
   the system under test: the methods only re-encode `[]Log`, but their decoding differs from the
   default on a non-nil target). Not decided here.
3. **`encoding/json`'s `RawMessage` is `jsontext.Value`** in Go 1.27.3's default build, so the main
   tree's names-only `encoding/json` (the real package) does not translate a kit that names
   `json.RawMessage` (`Unknown identifier encoding.json.jsontext.Value`); the port translates the
   model's names instead (its `RawMessage` is its own `[]byte` type), which is also what the
   eventual Lean half will be.
6. **BLOCKER: remote's `ServeClient.spec` cannot be met by this kit's client** (nor `Serve.spec`).
   (a) `newClient` is specified as a persistent `{{True}}` triple yet called once: it would have to
   produce the exclusive `tok sys` (the `Sys` flags, go-vsr's request numbers, the ghost counter
   `nextReq`) from nothing any number of times (paxos escaped: its `tok` was persistent); (b) no budget
   on calls: `svcOp`/`Serve.spec` cover unboundedly many `op` calls with one `tok`, but each `Op`
   registers a request (`ghost_register`, budget < 2^28 per client, which bounds every message line), and
   remote's `reqP` admits any number of slots. Fix (a change to `examples/lib/remote`): pass
   `newClient`'s WP as a (non-persistent) resource, and budget calls (e.g. a per-address slot bound in
   `reqP` from `Check`'s `ops`, `tok (k+1) → tok k`). `examples/vsrnet/ClientProof.lean` states that
   contract as `ServeClientB.spec`, a premise of `Client.wp_proof` only (not dischargeable as remote
   stands; probably refutable since a dialer can open more slots than the budget).
5. **`io.ReadFull` over a connection needs a reader contract at length 0.** Perennial's
   `io.ReadFull.spec` (and `ReadAtLeast`) asks the reader's `Pre` for every remaining length up to and
   including `len(buf)`, so at 0, which dsv-bufio's `conn_readerOk` (`Pre := 0 < m`) rules out. So
   `examples/vsrnet/Conf.lean` takes the hypothesis `conn_readerOk : connReaderOk` with
   `Pre := fun _ _ => True`, which today's `net.Conn.Read.spec` does not give (`ReadOut` gives only
   `sint.nat k = 0` for an empty read: the count could be negative, #24 item 4). To discharge it, one
   of: Perennial's `ReadFull`/`ReadAtLeast` premise to `ys.length < xs.length` (ReadAtLeast only reads
   while bytes remain); `Conn.Read`'s count exact (`sint.Z k = …`); a `conn_readerOk` variant on
   dsv-bufio allowing `m = 0` (the revised dsv-bufio `75ef5881aa` still has `0 < m`; VR's Go uses no bufio, so the port does not merge it). Not decided here (a Perennial or Net/ change).
4. `ServeClient`'s `newClient` (paxos's finding) applies here as well; the kit sidesteps it the same
   way.

7. **Nothing linked `vsrwire`** in the port's kit (the lab's linked it through its generated
   codec), so `events`' frame-decoder hook was never set: in Go `FromDecoder` fell back to
   `fromDecoderUnnamed`, and the proof's `frameDecoderSet` premise was unsatisfiable. Fixed:
   `kit.go` imports `vsrwire` blank (round 3). A note for the other kits: check that a package
   whose `init` a fact relies on is linked.

## Which lab run

Ported: **`vsr-bump-1`** (dsverify-lab `master` `915f964`, `examples/vr/`): fork `9c4be18`, proof
`c8b5962` tag `final` (33k lines in `VsrProof/`, of which ~8k the generated JSON codec's proof and
~2k the JSON stream), Perennial `3afd77e35`. Its `dsv_goal_check` rests on Lean's three axioms and the
lab's porcupine axiom (`CheckOperations.wp_proof`), which remote's verified porcupine replaces.
