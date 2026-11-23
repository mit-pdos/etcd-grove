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
- **`RegisterJSON` is hand-written** (`register.go`: nothing, in the real build;
  `register_goose.go`: nothing, under goose), not jsongen's: see "Findings".

## State

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
later). **Open (events' package facts):** `pkg/events/Base.lean`/`examples/vsrwire/Base.lean` still
have the weak facts; the hub specs take `hookKnownFull`/`frameDecoderSet` as preconditions. To make
them package facts: move `frameDecOk`, `rstream`, `hookLockInvFull`, `hookKnownFull`,
`frameDecoderSet` out of `Spec/events.lean` into a module importing no package `Base` (now a cycle),
and vsrwire's initialization needs `Decode_frame.spec` (an `InitHyp`-style hypothesis in
`etc/dsv/vr.py`) and events' init must allocate the hook's flag. Until then the kit gets
`frameDecoderSet` from a direct `init0` call.
**Now in progress (helper agents, parallel):** `Proof/replica/*`, `Proof/client/*`, `Proof/network/*`,
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

## Which lab run

Ported: **`vsr-bump-1`** (dsverify-lab `master` `915f964`, `examples/vr/`): fork `9c4be18`, proof
`c8b5962` tag `final` (33k lines in `VsrProof/`, of which ~8k the generated JSON codec's proof and
~2k the JSON stream), Perennial `3afd77e35`. Its `dsv_goal_check` rests on Lean's three axioms and the
lab's porcupine axiom (`CheckOperations.wp_proof`), which remote's verified porcupine replaces.
