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

### Round 11: the encoder proved; JsonHyps down to the Decoder (2026-11-25; the current handoff)

Brief (coordinator, 2026-11-25): finish `vr_remote_robust` with as few premises as possible; no new
premise route for JSON; slog from the merged lean; bounds as the other kits.

**Merge.** `origin/lean` 40b1b706d6 (727 commits; Perennial `fce59af75`, `.lake/package-overrides.json`
= `/shared/tmp/manifest-fce59af7.json`). Conflicts: `Net/Proof/models_lab/{Results,jsoncodec/Linked}.lean`
(union: lean's `Bool`, vr's `Nesting`/`AppendCompact`), `jsoncodec/AppendQuotedUint.lean` (lean's). Lean's
`jsoncodec/Quote.lean` (JSON batch 2b) now has `jsonQuote_plain`, `decU64_eq_decN`: vr's `QuoteBridge.lean`
deleted, `LogEnc`/`PayloadEnc` use `Quote`. `gen-init` (L1: one `Init.lean` per Go package; encoding/json's
and jsoncodec's inits now the main tree's) and `kitgen vr` regenerated.

**The encoder, proved (statement: `EncoderRep` and two `JsonHyps` fields removed).** The main tree's
`encoding/json` translates `NewEncoder` and `Encoder.Encode` with their bodies, so:
`Proof/encoding/json/EncoderModel.lean` (defs: `encOkModel`, the model's `Encoder` fields; `encRepModel`,
an `EncoderRep`), `Proof/encoding/json/Codec/NewEncoder.lean` (`NewEncoder.wp_proof` at `encRepModel`),
`Proof/encoding/json/Codec/Encoder__Encode_conn.lean` (`Encoder.Encode_conn.wp_proof` over
`marshalAny.wp` and `net.Conn.Write.wp_proof`: `writeP`/`write_acc`, the write error kept). Linked in vr's
`Link.lean` (`encEncodeConn`; `attribute [local instance] encRepModel`); `TopLevelRobustness`'s proof
takes `letI := encRepModel` per machine. `Proof/net/ErrOrNil.lean` (defs): `net.opErr_errOrNil`,
`net.resErr_errOrNil`, moved from vr's `network.*` (which now call them).
**Spec change** (ledger `notes/specs-only/ledger.md`, 2026-11-25): `Encoder.Encode_conn.spec` takes
`isPkgInit pkg_id.net` (the `Write` spec names `poll.ErrDeadlineExceeded`'s value, which only `net`'s
init gives); vr's `events.wstream` holds it (`network.wstream_of_pool` takes it, `Send` has it by
`iPkgInit`), `ToWriter` passes it.

**Statement diff (round 10 → now)**: the premise `∀ G L π, ∃ (_ : DecoderRep) (_ : EncoderRep), JsonHyps`
becomes `∀ G L π, ∃ (_ : DecoderRep), JsonHyps`, `JsonHyps` = `{newDecoder, Decode_frame}`; docstring.

**Remaining premise** (the only one; true of Go, witnessed only by local axioms in `NonVacuityLinked.lean`):
`newDecoder`, `Decode_frame` over some `DecoderRep`. Why not proved: the main tree translates neither
`NewDecoder` nor `Decoder.Decode` (`Code/encoding/json.toml`). What proving them takes:
1. translate `NewDecoder`, `Decoder.{Decode,readValue,badStart,fetch}`, `endsInNumber`,
   `(*SyntaxError).Error` (a main-tree goose configuration change; `etc/goose.py` regenerates
   encoding/json for every project mapping it);
2. `fetch`'s `copy(dec.buf[:cap(dec.buf)], dec.buf[dec.prevStart:])` copies within one array
   (dst before src): Perennial's `wp_slice_copy` takes the two slices' points-to separately, so a
   lemma for an overlapping forward copy (Perennial: `copyForward` copies from index 0 up, which is
   memmove when dst ≤ src) is needed (a general Perennial change, `notes/perennial-changes.md`);
3. the representation over the fields (`decOkM`/`decErrM` of `NonVacuityLinked.lean`), with the
   statement fixing it (the `∃ DecoderRep` goes) and `Decode_frame`'s proof: `readValue`'s loop over
   `jsoncodec.Scan` (`scanOk scanF scanFn`; facts: `scanF` of a proper prefix of `encEvent m` after
   whitespace is More, of `ws ++ encEvent m ++ "\n" ++ …` is Done at the value's end), `fetch` over
   `net.conn_readerOk`'s `Read` with the protocol's lines (`rstreamAt`), every error path to `decErrM`
   (the sticky error), then `*Frame`'s `JSONModelUnmarshal` (proved). The lab's analogue
   (`VsrProof/Proof/jsonstream/`, its own buffer) was ~2k lines.

**Premise witness.** `examples/vsrnet/TopLevelWitness.lean` (new): `vr_remote_robust.premisesSat :
premise_sat% vr_remote_robust.spec` (twelve fresh machines, `vrKitAddrs` distinct and valid by
`decide`; the JSON premise is an Iris contract, left out by `premise_sat%`); `etc/premise-witness.py
--check` ok, vr not in the baseline.

**Checks (round 11, head after the scratch drop).** Built on fk-lean2 (`FKLEAN_HOST=fk-lean2
/shared/tmp/fklean1-check.sh`; the local slots were held by a whole-machine build): vr's
`TopLevelRobustness`, `TopLevelWitness`, `NonVacuityLinked`, `Net.Proof.models_lab.Results`,
`Proof.encoding.json.Results`; scratch `Dsverify/Scratch/Axioms.lean` (committed, built, dropped):
`vr_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`, `paxos_remote_robust`,
`encoding.json.NewEncoder.wp_proof`, `encoding.json.Encoder.Encode_conn.wp_proof`, `dsvvr.encEncodeConn`,
`net.resErr_errOrNil`: each `[propext, Classical.choice, Quot.sound]`; `nonvacuous_premises`: those and the
two local axioms (test-only). Here: `tier-check --check` ok (208 known, no new); `gen-init --check` 272 up to
date; `kitgen --check vr` ok; `goose --check --project dsv-vr` up to date (Perennial fce59af75);
`copy-part --check` 0 differ; `premise-witness --check` ok.

**Next.** The Decoder (above, three steps), which removes the last premise; then land.


### Round 10: ready to land; connReaderOk discharged; reps per heap; non-vacuity (2026-11-24; history)

Brief: merge lean (Perennial `b3f2fc485`), adopt kitgen, write `NonVacuityLinked.lean`, the landing
lessons, all checks; builds on fk-lean1.

**Merge.** `origin/lean` 5c7f7d2e59 (286 commits: JSON work, kitgen, kitlibs-check,
dsv-export-leaks; Perennial `b3f2fc485`): `.lake/package-overrides.json` →
`/shared/perennial-b3f2fc485`; `gen-init` run (with `PERENNIAL_DIR=/shared/perennial-b3f2fc485`):
the twelve commands' `PkgTable.lean` gain `internal.testlog` (Perennial's `os`). Lean has **no**
JSON batch 2b (`jsonQuote_plain`/`decNat_decN` bridges: vr's `QuoteBridge.lean` stays), no
`NewDecoder`/`Decoder.Decode` spec, and no proof of `NewEncoder`/`Encode_conn` (`Results.lean`: "not
yet proved"): so `JsonHyps` keeps its four fields.

**kitgen adopted.** `etc/dsv/vr.py` has a `KITGEN` section (the boot tables, per notes/dsv-kitgen.md
"Migration": `table='server1'`, the four owned packages, the docs, opens, variables, `q`, `post`;
and the jsongen codec, `vsrnet/json.toml`, which `kitgen --check` now checks); `etc/dsv/_vr_boot.py`
deleted. Output: `BootTable.lean`, `BootCmdsLinked.lean` byte-identical but the header line.

**`connReaderOk` discharged (statement: `LibHyps` premise removed).** Perennial `b3f2fc485` has
mit-pdos/perennial#688 (readatleast-prefix: `io.ReadFull` asks `Pre` only at `ys.length <
xs.length`). `ConfDefs.lean`'s `wp_sendConf`/`wp_awaitConf` now read through Net's
`net.conn_readerOk wp_Read` (`Pre = fun _ m => 0 < m`, at `net.connIface t`), `Conf.lean`/`Link.lean`
pass `net.Conn.Read.wp_proof`; `LibHyps.lean` deleted.

**Reps per heap (statement change, the non-vacuity finding).** The round-9 statement quantified
`∀ [DecoderRep remoteGF] [EncoderRep remoteGF]` once, outside `∀ G L π`. Those classes are
heap-free (`Loc → … → IProp GF`), so a representation over the model's fields (a points-to,
which depends on the machine's heap `heapAt G L`) cannot be one instance for every heap, and a
heap-free one cannot make `newDecoder`'s and `Decode_frame`'s triples true together (Decode reads
`dec`'s fields in the heap of the WP; a resource that does not own them there makes it stuck;
`newDecoder` must return the resource). So the premise, as stated, had **no true instance**.
Now: `(∀ G L π, letI := heapAt G L; ∃ (_ : DecoderRep remoteGF) (_ : EncoderRep remoteGF),
JsonHyps) →`; the proof `obtain`s them per machine. This implies the old statement (a constant
family is an instance of the new premise). The main tree's classes have the same shape (heap-free):
a future main-tree instance over the model's fields will need the heap (a class argument or a
per-heap use, as here).

**Non-vacuity.** `examples/vsrnet/NonVacuityLinked.lean` (test-only, imported by nothing):
`encOkM`, `decOkM`, `decErrM` over the model's `Encoder`/`Decoder` fields (`encRep`, `decRep`);
`wp_NewEncoder` **proved** from the model's translated `NewEncoder`; `Encode_conn`, `newDecoder`,
`Decode_frame` **local axioms** (test-only; truth arguments in the file header); `jsonHyps_holds`,
`nonvacuous_premises` (the statement's premise in its own form).

**Statement diff (b297b05df9 → now)**: the `LibHyps` premise removed; the reps' binder moved
inside the JSON premise as an `∃` per heap; docstring. Nothing else.

**Remaining premise**: `∀ G L π, ∃ reps, JsonHyps` with `NewEncoder`, `Encode_conn`,
`newDecoder`, `Decode_frame` (main tree's statements / `events`' over `DecoderRep`).

**Checks (round 10)**: see "Round 10 checks" below (filled in at the final head).

### Round 9: all of TypeCodecs proved; JsonHyps loses `types`; lean merged twice (2026-11-24; history)

Brief: steps 4–6 of round 8 (prove `TypeCodecs`' fields, removing each from the statement), then
check whether `JsonHyps`' `NewEncoder`/`Encode_conn`/`newDecoder`/`Decode_frame` can be
discharged; builds on fk-lean1 (`/shared/tmp/fklean1-check.sh`; scratchpad `vrb.sh LOG TARGETS`;
single-file elaboration: scratchpad `rl.sh FILE NAME` scp's FILE to fk-lean1's
`wt/dsv-vr/Dsverify/Scratch/NAME.lean` and runs `lake env lean` there, against that worktree's
last build: fast, but only for files whose imports that build has).

**Merges.** (1) `origin/lean` ddc690bf03 (Perennial pin `47ec64a9d`; `.lake/package-overrides.json`
→ `/shared/perennial-47ec64a9d`; here `gen-init` needs `PERENNIAL_DIR=/shared/perennial-47ec64a9d`,
the worktree's `.lake/packages/perennial` is stale). (2) `origin/lean` c2118c0b56 (zeldovich's
JSON batch 2a, as agreed on #24): batch 2a's `AppendString` (`bs ++ jsonQuote s`, no premise) and
`AppendUint` (`decU64`) are canonical, vr's dropped; vr's jsoncodec `.wp` links moved from
`Net/Proof/models_lab/Results.lean` into `Net/Proof/models_lab/jsoncodec/Linked.lean` (`Results.lean`
keeps the inits and the `#print axioms`); local bridges in `Net/Proof/models_lab/jsoncodec/QuoteBridge.lean`:
`decNat_decN`, `decU64_decN`, `escASCII_plain`, `quoteFrom_plain`, `jsonQuote_plain` (**replace
by batch 2b's `jsonQuote_plain`/`decNat` bridge when 2b lands**); `AppendQuotedUint.wp_proof` over
the new `AppendUint` spec; `LogEnc` over the new `AppendString`. **Not merged:** `origin/lean`
9cf9b73123 (9 commits later) moves Perennial to `580868e54`, which fk-lean1 does not have
(`/home/ubuntu/eg/perennial-580868e54` missing; `/shared/perennial-580868e54` exists here): the
merge was made and undone; merge it once fk-lean1 has the pin.

**Step 4: `TypeCodecs.frame`.** `Proof/vsrnetjson/FrameDec.lean`: `wp_jdecRaw`
(`append((*p)[0:0], b[j:k]...)`), `wp_jdecMember_Frame_{type,data}`, `wp_jdec_Frame`,
`vsrnet.frameUnmarshalOk`.

**Step 5: the 11 payloads.** `Proof/log/LogsJson.lean`: `log.Logs.UnmarshalJSON.wp_proof` and
`log.Logs.MarshalJSON.wp_proof` over the main tree's `Unmarshal.spec`/`Marshal.spec` (the codec
route); both specs in `Spec/log.lean` restated (they were the lab's, unproved and unused; their
precondition `kitCodecOk F` is now `codecRoute J F`, `J`'s deposit a premise);
`logs_{un,}marshalsByCodec`, `codecRoute_persistent` there too (`omit` the section's `JsonCodec`).
`Proof/vsrnetjson/PayloadDec.lean`: the lab's `Request`, `DecFlat`, `DecMore`, `DecLogs` decoders
ported by script (scratchpad `vr9/paydec.py`; bundle `vsrnet.DecSpecs`), the `Logs` member
`vsrnet.wp_jdec_logs` (new: `jdec_p0_log_Logs`, `b[j:k:k]`, `Logs.UnmarshalJSON`), and
`vsrnet.unmarshalOk_<T>` (generated by scratchpad `vr9/top.py`; Heartbeat's tail hand-fixed).

**Step 6: `event`.** `Net/`: `jsoncodec/Compact.lean` (pure: `cmpRun`, ported; `nestRun`, new),
`AppendCompact` (spec + proof, ported, over `Valid`, `IsSpace`, `htmlByte`), `Nesting` (spec +
proof, new; precondition: the bytes do not end in a backslash), linked in `jsoncodec/Linked.lean`.
`Proof/vsrnetjson/PayloadEnc.lean`: the lab's `EncFlat`, `EncLogs`, `Marshal` ported (scratchpad
`vr9/payenc.py`, `payenc2.py`; the depth arguments added; bundle `vsrnet.EncSpecs`), the `Logs`
member `vsrnet.wp_jenc_logs` (`Logs.MarshalJSON`, then `wp_jencValue`: `Valid`, `Nesting`
(`nestRun_logs`: at most 2), `AppendCompact` (`cmpRun_logs`)), and `vsrnet.eventMarshalOk`
(`(*Event).JSONModelMarshalPtr`).

**Wiring.** `Spec/json.lean`: `vsrnet.TypeMethods` (13 fields: `event`, the 11 payloads, `frame`)
is **not a premise**: built in `Link.lean` (`vsrDecSpecs`, `vsrEncSpecs`, `vsrTypeMethods`,
`vsrCodecOk j`); `vsrnet.TypeCodecs` is gone; `codecOk_of hc hs hu`, `JsonHyps.codecOk j hc hs hu`.

**Statement diff (round 8 head 57f4412a7a → now): `JsonHyps` loses its field
`types : examples.vsrnet.TypeCodecs`** (and `TypeCodecs`, its 13 fields, is deleted); nothing
else (`TopLevelRobustness.lean` unchanged).

**Remaining premises.** `JsonHyps`: `NewEncoder`, `Encode_conn` (the main tree's statements; lean
9cf9b73123 has their specs but no proofs: `EncoderRep` is still a class), `newDecoder`,
`Decode_frame` (lean has no `encoding/json` `NewDecoder`/`Decode` spec: zeldovich's have not
landed); `LibHyps`: `connReaderOk` (finding 5); data classes `DecoderRep`, `EncoderRep`.

**jsoncodec specs added under `Net/` this round** (one spec file per function, `Net/Spec/
models_lab/jsoncodec/<F>.lean`, proof `Net/Proof/.../<F>.lean`, linked in `jsoncodec/Linked.lean`):
`AppendCompact`, `Nesting`. Pure helpers: `Compact.lean`, `QuoteBridge.lean`.

**Checks (round 9, final head).** fk-lean1: vr's `TopLevelRobustness`, `Proof/vsrnetjson/Vacuous`,
`Net.Proof.models_lab.Results` built (2995 jobs); scratch `Dsverify/Scratch/Axioms.lean` (committed
cae7d19a42, built: 5320 jobs, dropped): `vr_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`,
`epaxos_remote_robust`, `quepaxa_remote_robust`, `paxos_remote_robust`, `counter_remote_robust`,
`typeCodecOk_logs`, `codecOk_of`, `dsvvr.{vsrRegisteredCodecOk, vsrScanOk, vsrTypeMethods, vsrDecSpecs,
vsrEncSpecs, vsrCodecOk}`, `log.Logs.{Un,}MarshalJSON.wp_proof`, `jsoncodec.{scanOk_scanF, Nesting.wp,
AppendCompact.wp}`: each `[propext, Classical.choice, Quot.sound]`; `jsonQuote_plain`, `decNat_decN`:
`[propext, Quot.sound]`; every jsoncodec `.wp` in `Results.lean` on Lean's three. Here:
`tier-check --check` ok, 227 known (no new); `gen-init --check` 273 up to date; `goose --check
--project dsv-vr` up to date (Perennial 47ec64a9d); `_vr_boot.py --check` rc 0 (vr has not adopted
kitgen; `_swiftpaxos_boot.py` is gone from lean); `copy-part --check` 0 differ;
`proof_roots.namespace()` `Perennial.EtcdGrove.`; dups 4 (the known parse artifacts; scratchpad
`dups-47ec.py`); `jsongen --check` (vsrnet) rc 0; `etc/goose.py`, `etc/gen-init.py` equal lean's.

### Round 8: jsoncodec's runtime specs, scanOk and the registered codec proved (2026-11-24; history)

Brief: discharge vr's JSON premises one at a time (round 7's list); generic library pieces where
other kits can use them; the statement may only lose premises; no GitHub posts.

**Done (1): a runtime-spec library for `models.lab/jsoncodec`, generic, in `Net/`** (where the
main tree's `encoding/json` already takes jsoncodec's vocabulary: `Net/Proof/models_lab/jsoncodec/
Codec.lean`; nothing in `Proof/`/`Spec/` had jsoncodec specs; lean has no others, checked
f08ee893fb). One spec file per function, `Net/Spec/models_lab/jsoncodec/<F>.lean` (`<F>.spec`), its
proof `Net/Proof/models_lab/jsoncodec/<F>.lean` (`<F>.wp_proof`, callees as hypotheses: tier rule),
linked in `Net/Proof/models_lab/Results.lean` (`jsoncodec.<F>.wp`, `#print axioms` each: Lean's
three):
- the pure scanner moved out of vr: `Net/Proof/models_lab/jsoncodec/Scan/{Def,StrSteps,NumSteps,
  Steps,Bounds,Idx,Lits}.lean`, namespace **`JsonScan`** (was vr's `VsrJson`; vr's remaining
  `VsrJson` files `open JsonScan`): `spB`, `strL`, ..., `goL`, `scanL`, **`scanF`** (was
  `VsrJson.scanF`; `vsrnet.scanF := JsonScan.scanF`, the same function), `skipEnd`; `Lits.lean`:
  `decN`, `okB`, `plainEnc` (AppendString's plain subset), `numEnd`, `numL_full`, `strL_full`,
  `valD`, `decN_okB`, `scanL_num`, `scanL_str` (top-level number/string without vr's `JV`);
- specs+proofs: `SkipSpace`, `Scan` (`JsonScan.scanF`, any input), `ValueEnd`, `At`, `Next`,
  `Empty`, `Str`, `Member`, `Digits`, `Uint`, `QuotedUint` (with the new `noEscape`), `String`,
  `AppendUint`, `AppendQuotedUint`, `AppendString` (plain subset only: true of today's panic model
  and of zeldovich's escaping AppendString, prove-ps2-jsonj4: **for a #24 post**, offer them to adopt
  it); internal helpers as defs-tier lemmas (`ScanString.lean`: `wp_isDigit`, `wp_scanDigits`,
  `wp_isHex`, `wp_scanString`, tactics `ldidx`/`ldagain`/`fin_ret`; `ScanNumber.lean`,
  `ScanScalar.lean`; `DecBase.lean`: `wp_SkipSpace_ns`, `wp_noEscape`). The decoders' specs are
  the lab's (at valid input of the shapes decoders meet), not full functional specs.
- `Valid` (on one complete value with nothing after it, lab `wp_Valid_ok`; what the frame's
  `JSONModelUnmarshal` needs, step 4). Not done: `FoldEq`, `AppendInt`, `AppendCompact`, `Bool`,
  `Int` (not needed so far: with exact keys the decoders never reach `FoldEq`).

**Done (2): `scanOk`.** `Net/Proof/models_lab/jsoncodec/ScanOk.lean` (`scanOk_of`), linked
`models_lab.jsoncodec.scanOk_scanF : ⊢ scanOk JsonScan.scanF scanFn`. It left
`registeredCodecOk` (which became `marshalOk ∗ unmarshalOk`) before (3) removed the whole field.

**Done (3): `registeredCodecOk` proved; `JsonHyps.codec` removed.** `Proof/vsrnetjson/`:
`LogDec.lean` (`jdec_log_Log`, `jdecMember_log_Log`), `SLogDec.lean` (`jdec_S_log_Log`: this
codec appends a zero `Log` and decodes in place, `&s[n]`, unlike the lab's), `RegUnmarshal.lean`
(`vsrnet.registeredUnmarshalOk`: `Frame`/payload pointers excluded by `unmarshalsByCodec`,
`payload_unmarshaler`, `frame_unmarshaler`), `LogEnc.lean` (`jenc_log_Log`, `jenc_S_log_Log`, with
the depth arguments), `RegMarshal.lean` (`vsrnet.registeredMarshalOk`; `*Event` excluded by
`marshalsByCodec`), `Registered.lean` (`vsrnet.registeredCodecOk_of` over the helpers' specs).
`examples/vsrnet/Link.lean`: `vsrScanOk`, `vsrRegisteredCodecOk` (Net's `.wp`s), and
`j.codecOk vsrRegisteredCodecOk vsrScanOk` (`JsonHyps.codecOk` takes both now).
**Statement diff (round 7 head ace1737dcb → now): `JsonHyps` loses the field
`codec : examples.vsrnet.registeredCodecOk (GF := GF) (hG := hG)`; nothing else** (the
`TopLevelRobustness` spec file is unchanged; `vsrnet.registeredCodecOk` stays defined in
`Spec/json.lean`, now `⊢ marshalOk ∗ unmarshalOk` at `codecPart`, and is a theorem).

**Remaining premises** (`JsonHyps`): `NewEncoder`, `Encode_conn`, `newDecoder`, `Decode_frame`,
`types : vsrnet.TypeCodecs` (13 fields: `event`, the 11 payloads, `frame`); `LibHyps`:
`connReaderOk`; data classes `DecoderRep`, `EncoderRep`. Next, in order: (4) `TypeCodecs.frame`
(`vsrwire`'s `Frame.JSONModelUnmarshal`: `Valid`, then `jdec_Frame`/`jdecMember_Frame`/`jdecRaw`;
needs a `Valid` spec (lab `wp_Valid_ok`), `Uint` at max 255 for the type; lab `vsrnetjson/
Frame.lean`, `Unmarshal.lean`); (5) the 11 payloads' `JSONModelUnmarshal` (lab `DecFlat`,
`DecMore`, `Request`, `UnmarshalAll`; `DoViewChange`/`StartView`/`NewState` through
`Logs.UnmarshalJSON`, which now has the registered codec's proof to stand on); (6)
`TypeCodecs.event` (`jenc_Event` etc.; lab `EncFlat`, `EncLogs`, `Marshal`, `MarshalTop`). Each
removes a field of `TypeCodecs` (restate `TypeCodecs` without it and have `codecOk_of` take the
proof, as `codec` went).

**Checks (round 8, final head).** Builds: fk-lean1 for the work; the final checks on this host
(fk-lean1's lock had a queue of five; coordinator's instruction): `.lake/package-overrides.json` →
`/shared/perennial-ccfeb3895`, and `/shared/tmp/build-slot.sh` fails here at `systemd-run --scope`
(needs interactive auth), so scratchpad `bslot.sh` (the same script with `systemd-run --user
--scope`). Scratch `Dsverify/Scratch/Axioms.lean` (committed cee5c4242b, built, dropped): 5154 jobs;
`vr_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`, `epaxos_remote_robust`,
`quepaxa_remote_robust`, `paxos_remote_robust`, `counter_remote_robust`, `typeCodecOk_logs`,
`codecOk_of`, `dsvvr.vsrRegisteredCodecOk`, `dsvvr.vsrScanOk`, `jsoncodec.scanOk_scanF`: each
`[propext, Classical.choice, Quot.sound]`. Final head: `Net.Proof.models_lab.Results`, vr's
`TopLevelRobustness`, `Vacuous` built (2975 jobs), every jsoncodec `.wp` (with `Valid.wp`) on
Lean's three axioms.
Here: `tier-check --check` ok, 227 known (no new); `gen-init --check` 274 up to date;
`goose --check --project dsv-vr` up to date; `_vr_boot.py --check`, `_swiftpaxos_boot.py --check`
rc 0; `copy-part --check` 0 differ; `proof_roots.namespace()` `Perennial.EtcdGrove.`; dups 4 (the
known parse artifacts; scratchpad `dups-vr8.py` = `dups.py` at Perennial ccfeb3895); `jsongen
--check` rc 0; `etc/goose.py`, `etc/gen-init.py` equal the merged lean's (merge-base).

### Round 7: J3's premise shapes, RegisterJSON from the boot (2026-11-24; history)

Coordinator's decisions (round 6's open points): (1) restate the JSON premises in J3's true
shapes; (2) prove `RegisterJSON` from a first-run boot as swiftpaxos's; (3) discharge the
restated premises from jsongen's code; (4) keep `newDecoder`/`Decode_frame` over `unmarshalVia`.

**Design (two contracts, no Löb).** The kit's contract `vsrnet.jsonCodec` (`encP`, `decP`,
unchanged but `codecSet` is now the main tree's `codecSetWith` at the kit's functions) is the
per-type methods' contract. The registered codec cannot meet it (`jsonMarshal(*Event)` panics), so
it meets `encoding.json.codecPart jsonCodec` (`Spec/jsonlib.lean`, generic: `J` restricted to the
values the dispatch sends to the codec: `marshalsByCodec`/`unmarshalsByCodec`). The `Logs`
recursion of the lab (one codec calling back into itself through `Logs.MarshalJSON`) is gone:
`DoViewChange`'s methods reach the registered codec, whose fact (`registeredCodecOk`) does not
depend on the types' facts, and the codec's `[]log.Log` path calls no method. So no Löb lemma is
needed (none exists on any branch either).

**(1) done: the premises.** `JsonHyps` (`examples/vsrnet/JsonHyps.lean`) now:
`NewEncoder`, `Encode_conn` (the main tree's statements themselves), `newDecoder`,
`Decode_frame` (precondition `codecSet ∗ unmarshalVia _ F (&Frame)` in place of
`codecSet ∗ kitCodecOk F`), `codec : vsrnet.registeredCodecOk`, `types : vsrnet.TypeCodecs`
(14 fields, `typeCodecOk vsrnet.jsonCodec scanF T`). Removed: `Unmarshal` (the main tree's
`Unmarshal.wp`), `RegisterJSON` (proved, (2)). `kitCodecOk F` (vr's internal bundle) is now
`codecOkWith (codecPart jc) … ∗ □ ∀ T ∈ kitTypes, typeCodecOk jc F T`; `vsrnet.codecOk` (what
the proofs take) is derived: `vsrnet.codecOk_of`, `JsonHyps.codecOk`. `Proof/events/LibHyps.lean`
(the `.kitSpec`s) deleted. Truth arguments: the docstrings of `registeredCodecOk`, `TypeCodecs`
(`Spec/json.lean`), `Decode_frame` (`Spec/events.lean`).

**(2) done: the boot.** `etc/dsv/_vr_boot.py` (from `_swiftpaxos_boot.py`) generates
`examples/vsrnet/BootTable.lean` (`gOff`, `KitG`, `wf_*`, `wfO_*`; owned = the path
`vsrnet → replica → network → encoding/json`, the first package on each level whose closure has
encoding/json) and `BootCmdsLinked.lean` (each command's `kitG`, `wp_boot`). `BootLinked.lean`
(hand-written): `boot_json` (allocs, `io`, `sync`; `sync.init_Mutex` over `codecInv`, returns
`codecFresh`), `boot_network`, `boot_replica`, `boot_vsrnet` (generated bodies, the path's call
first-run). `wp_package_init_first` is swiftpaxos's (`InitFirst.lean`, imported). `KitLib.lean`:
`RegisterJSON.spec` (`codecFresh` → `codecSet`), `wp_RegisterJSON` over the main tree's
`SetCodec.spec`. `codecFresh` threads boot → `wp_bootR` (TopLevel) → `Mains` → `Client.spec`/
`Server.spec` → `mkClient.spec`/`runReplica.spec` → `RegisterJSON()`.

**(3) started: discharging the premises.** `TypeCodecs` now states only the substantive parts
(13 fields: `event` = `marshalAt jsonCodec ((*Event).JSONModelMarshalPtr)`, and
`unmarshalAt jsonCodec scanF ((*T).JSONModelUnmarshal)` for the 11 payloads and `frame`); the rest
of `typeCodecOk` for all 14 kit types, `log.Logs` whole, is proved in
`Proof/vsrnetjson/Vacuous.lean` (`marshal_val_none`, `marshal_ptr_none`, `unmarshal_ptr_none`:
`encP`/`decP` give no deposit there; `typeCodecOk_logs`, `typeCodecOk_of_unmarshal`,
`typeCodecOk_event`, `codecOk_of`). Statement change: premises weakened only (a field removed,
the others narrowed).

**What remains of (3)** (the substantive premises), in a suggested order:
1. A runtime-spec library for `models.lab/jsoncodec` (the Go in `models/jsoncodec/jsoncodec.go`,
   translated under `Net/Code/models_lab/jsoncodec`): `SkipSpace`, `ValueEnd`, `At`, `Next`,
   `Empty`, `Member`/`Str`, `Uint`/`QuotedUint` (signature changed against the lab: returns
   `(y, st, k)`; `Set`/`TypeErr` statuses), `FoldEq`, `AppendUint`, `AppendString`, `AppendRaw`
   (proved in `Net/`), `Valid`. The lab's `VsrProof/Proof/jsoncodec/Go{Base,Dec,Enc,Number,Scan}.lean`
   (~2.3k lines, lab master 915f964) are the guide; adapt them, against the pure scanner already
   ported (`Proof/jsoncodec/Scan*.lean`, `VsrJson.scanF`). Put them generic (Net or the main
   tree's `Proof/models_lab/jsoncodec/`) so other kits reuse them.
2. `scanOk scanF scanFn` (the lab's `ScanOk.lean`, from `GoScan`): part of `registeredCodecOk`.
3. `registeredCodecOk`'s `marshalOk`/`unmarshalOk` at `codecPart jsonCodec`: only `[]log.Log`
   (`jenc_S_log_Log`) and `*[]log.Log` (`jdec`… of `json_gen.go`); every other `codecPart`
   deposit is excluded by `marshalsByCodec`/`unmarshalsByCodec` (`go_type_set` on `*Event`,
   `*Frame`, `*payload`). Lab guide: `vsrnetjson/{EncLogs,DecLogs,LogsDec,SLogDec}.lean`.
4. `TypeCodecs.frame` (`vsrwire`'s generated `JSONModelUnmarshal`, `jdec_Frame`,
   `jdecMember_Frame`, `jdecRaw`; lab: `vsrnetjson/Frame.lean`).
5. The 11 payloads' `JSONModelUnmarshal` (lab: `DecFlat`, `DecMore`, `Request`,
   `UnmarshalAll`); `DoViewChange`/`StartView`/`NewState` reach `Logs.UnmarshalJSON` (prove
   `log.Logs.UnmarshalJSON.spec` of `Spec/log.lean` over the main tree's `Unmarshal.spec` at
   `codecPart jsonCodec`, the codec route; its `hdec`/`hval` premises are `vsrnet.dec_logs`'s).
6. `TypeCodecs.event` (`jenc_Event`, events' `jencAny`, `jenc_<payload>`; `Logs.MarshalJSON`
   over the main tree's `Marshal.spec` at `codecPart jsonCodec`; lab: `EncFlat`, `EncLogs`,
   `Marshal`, `MarshalTop`).
Each step removes one premise field (or `registeredCodecOk`) from `JsonHyps` (`JsonHyps.codecOk`
then calls the theorem). No Löb is needed (design above).

**Checks (round 7, head after the scratch drop).** fk-lean1 (`/shared/tmp/fklean1-check.sh`;
helper `scratchpad/vrb.sh`): vr's `TopLevelRobustness` and `Proof/vsrnetjson/Vacuous` build
(2912 jobs); scratch `Dsverify/Scratch/Axioms.lean` (committed, built, dropped):
`vr_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`, `epaxos_remote_robust`,
`quepaxa_remote_robust`, `paxos_remote_robust`, `counter_remote_robust`, `typeCodecOk_logs`: each
`[propext, Classical.choice, Quot.sound]`. Here: `tier-check --check` ok, 227 known (no new;
`RegisterJSON`'s proof is named `wp_RegisterJSON` so `KitLib` stays defs); `gen-init --check` 274
up to date; `goose --check --project dsv-vr` up to date; `_vr_boot.py --check` and
`_swiftpaxos_boot.py --check` ok; `copy-part --check` 0 differ; `proof_roots.namespace()`
`Perennial.EtcdGrove.`; dups.py 4 hits (the known parse artifacts); `jsongen --check` 0;
`etc/goose.py`, `etc/gen-init.py` equal lean's; no landed `TopLevelRobustness` differs from lean.
No `InitHyp` premise (vr has none).

### Round 6: JSON on the main tree (2026-11-23 late; history)

Brief: move vr onto the main tree's JSON (J1/J2/J3 landed on `lean` 69adf61913,
`prove-ps2-jsonj2`, `ps2-jsongen`). Merged `origin/lean` 69adf61913 (Perennial pin `ccfeb3895`,
`/shared/perennial-ccfeb3895`; fk-lean1 `/home/ubuntu/eg/perennial-ccfeb3895`).

**Goal 1 (done): the main tree's `encoding/json`.** `etc/dsv/vr.py`: `"encoding/json="` (main),
dropped from `packages`/`owned`, `MAIN = MAIN_GEN = ['encoding.json']`, `HYP_INITS = []`; goose and
gen-init (twice) rerun. Hand-written `Base.lean`s import `Proof.encoding.json.Base`. Deleted for
the main tree's: vr's `isSpaceB`, `DecoderRep` (`Spec/jsonlib.lean`), `EncoderRep`,
`NewEncoder.spec` (`Proof/events/LibHyps.lean`), `Dsverify/Proof/bufio/ErrOrNil.lean` (and
swiftpaxos' `lib/Bufio.lean`'s identical `errWf`/`errOrNil`, which now collide with
`Proof/bufio/ErrOrNil.lean` in the gates' closure: it imports the main tree's; its statement is
untouched). `Spec/jsonlib.lean` keeps only vr's names: `kitFn`, `kitCodecOk F := codecOkWith F
(kitFn …)`, `codecFns c := codecFnsWith (kitFn …) c`, and `codecSet` (no mutex). vr's two
codec-route specs collide by name with the main tree's and are not the same statement, so they are
renamed, unchanged: `encoding.json.Unmarshal.kitSpec`, `encoding.json.Encoder.Encode_conn.kitSpec`.
**Statement diff: only `(∀ G L, letI := heapAt G L; encoding.json.InitHyp remoteGF) →` removed.**

**Goal 2 (done): jsongen's codec.** Per-type (J3): `vr.py` `jsonmodel_roots` = events' `Event`,
`Request`, `Reply`, `Prepare`, `PrepareOK`, `Commit`, `StartViewChange`, `DoViewChange`,
`StartView`, `GetState`, `NewState`, `Heartbeat`, `vsrwire.Frame`, `log.Logs` (whose own
`MarshalJSON`/`UnmarshalJSON` the methods call); `"models.lab=Net"` lean root. goose.py's
no-`go.work` route (`-modfile` in `GOFLAGS`) fails under go/packages (its `GO111MODULE=off` probe),
so `examples/dsverify/vr/go.work` (`use .`), as quepaxa's. Registered codec
(`examples/vsrnet/json.toml`): the unnamed roots only, `[]log.Log` (what `Logs`' methods pass) and
`fromDecoderUnnamed`'s frame; `RegisterJSON` is jsongen's (`json_model_gen.go`:
`SetCodec(&json.Codec{jsonMarshal, jsonUnmarshal, jsoncodec.Scan})`), `register*.go` deleted. No
`[]events.Request` root: no code passes one to encoding/json. Checks: `jsongen.py … --check` 0;
`goose.py --check --project dsv-vr` up to date; `go test ./examples/vsrnet/` (the codec's generated
test against real encoding/json, and kit_test) ok; the same-package methods' generated tests
(`go test -tags netmodel -overlay`, jsonmodel_forks.py's step 3 for vr's roots; scratchpad script
`vr_jsonmodel_test.py`) ok for events, log, vsrwire.

**Fallout fixed:** `Proof/network/Ghost.lean`'s `network.opErr_errOrNil` now over Net's
`net.wp_OpError_Error` (lean's `OpError.Error` builds Go's message form); `Base.lean` of `log`,
`events`, `vsrwire` import `Net.Proof.models_lab.jsoncodec.Base` (their `JSONModel*` methods import
`models.lab/jsoncodec`); `KitLib.wp_RegisterJSON` (the placeholder's empty body; unused) deleted.

**Checks (round 6).** fk-lean1, head a734ce736c with the scratch module `Dsverify/Scratch/Axioms.lean`
(dropped after): `Build completed successfully (5077 jobs)`; `#print axioms` of `vr_remote_robust`,
`swiftpaxos_remote_robust`, `rabia_remote_robust`, `epaxos_remote_robust`, `quepaxa_remote_robust`,
`paxos_remote_robust`, `counter_remote_robust`: each `[propext, Classical.choice, Quot.sound]`.
Here: `tier-check --check` ok, 227 known (as lean); `gen-init --check` 274 up to date;
`goose --check` dsv-vr, dsv-epaxos, dsv-swiftpaxos up to date; `_swiftpaxos_boot.py --check` ok;
`copy-part --check` 0 differ; `proof_roots.namespace()` `Perennial.EtcdGrove.`; dups.py 4 hits, the
known regex false positives; `jsongen --check` 0; `git diff origin/lean -- etc/goose.py
etc/gen-init.py` empty; no landed `TopLevelRobustness` spec differs from lean.

**Goals 3-4: what the landed J2/J3 change in vr's premises (stopped: a statement decision).**
- `codecOk` (`⊢ kitCodecOk scanF` at `vsrnet.jsonCodec`) is now **false of the code for good**:
  the registered codec covers only `[]log.Log` and the unnamed frame (`jsonMarshal(*Event)` reaches
  `jencAnyExtra`, a NotModelled panic). Under J3 the named types are `typeCodecOk J F T` (their
  `JSONModel*` methods) and the codec is `codecOkWith F fm fu` for the unnamed roots only, so the
  premise must be restated (per type + codec) or proved (goal 4) — a restatement is a change other
  than removal.
- `RegisterJSON.codecSet_spec` is false (precondition `isPkgInit vsrnet` only; `SetCodec` panics if
  a codec is set). Provable from `SetCodec.spec` given `isPkgInit sync ∗ isMutex codecMu codecInv ∗
  codecUnset`, which encoding/json's first initialization makes (`codecMu`, `codec` allocated, the
  mutex initialized) but the generated `Init.lean` drops. **Without a new premise:** a vr boot as
  swiftpaxos's (`etc/dsv/_swiftpaxos_boot.py`, `BootTable`, `BootLinked`): prove json's first run
  returns them (its body is translated) and thread them to `RegisterJSON`'s callers (`mkClient`,
  `runReplica`); then this premise goes (removal) and `codecSetWith` replaces `codecSet` inside
  vr's proofs. **With a premise** (as `RpcBoot`/`RpcFirstInit`): a statement change.
- `Unmarshal.kitSpec` → the main tree's proved `Unmarshal.spec`: needs `unmarshalVia J F ptr` at
  `FromDecoder`'s eleven calls (`*events.Request` …: per-type, `typeCodecOk`), i.e. goal 4.
- `Encode_conn.kitSpec` → the main tree's `Encoder.Encode_conn.spec` (unproved: `EncoderRep` is a
  class): it quantifies over every `J` and takes `marshalVia J F v`; it is not implied by vr's, so
  the swap is a change other than removal. `NewEncoder`: already the main tree's (same statement).
- `newDecoder`/`Decode_frame` (goal 5): the main tree has no `NewDecoder`/`Decoder.Decode` spec
  (`Code/encoding/json.toml` translates neither); vr's premises stay (true of Go).
- No Löb lemma (`codecOkWith_löb`) on `lean` yet (grep `Proof/encoding/json`); goal 4's `Logs`
  recursion (`DoViewChange.JSONModelMarshal` → `Logs.MarshalJSON` → `json.Marshal([]Log)` →
  codec) needs it or an equivalent.

**Goal 4 scope** (not started): the lab's `VsrProof/Proof/vsrnetjson` (5071 lines) and `jsoncodec`
(~6k with the stream) prove the lab's single program-wide codec; jsongen's output is now 14
per-type method sets (`Dsverify/Code/.../pkg/events.lean` grew ~12k lines, `log` ~1.5k, `vsrwire`
~2k) plus a small codec (`[]log.Log`, frame). Per type `T`: `typeCodecOk vsrnet.jsonCodec scanF
T` from the generated `jenc_`/`jencA_`/`jdec_`/`jdecMember_`; `Logs` by Löb over `codecRoute`.
Reuse `Proof/jsoncodec/{ScanDef,StrSteps,NumSteps,…}` (already ported, pure).

### Round 5 (2026-11-23 night; history)

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

**Tier check: clean** (`etc/tier-check.py --check`: ok, no vr violation; `tier-baseline.txt` and
`tier-linking.txt` untouched; restructured on `dsv-vr-tier`, `08ded1641d`, merged at `65bd34df70`).
The 144 (78 defs→linking, 30 defs→proof, 21 proof→linking, 15 proof→proof) went as follows:
- **Splits** (`M` keeps its `wp_proof`s, `MDefs` the rest; names and statements unchanged):
  `Proof/network/HandleConn`, `examples/vsrnet/{ModelProof,CodecProof,KitProof,OrchProof,OpProof,
  MkClientProof,ClientProof,ServerProof,Conf}` (`ConfDefs`). Non-linking importers import the
  `*Defs`, the packages' `Spec/<pkg>.lean` (not `Proof/<pkg>/Results`, `Proof/log/Logs`) and
  `Net.Spec.net.*` (not `Net.Proof.net.*`).
- **Leaf callees in `replica.Hyps`** (`Hyps.lean`, the existing structure): 17 fields for the
  `assert`, `ipv4port`, `queue`, `time`, `log.Logs` specs the handlers call (`H.wp_Push`, ...);
  `replica/Results.lean` passes the proofs.
- **Callees as explicit hypotheses** `(wp_X : X.spec)`: `replica.{New,Replica.Submit}`,
  `network.{TCP.handleConn,TCP.Send,Network.Send,TCP.serve,TCP.Run,NewTCP,TCP.Recv,Network.Recv}`
  (leaf specs; `wp_handleConn` for `Send`/`serve`), `client.{New,Client.Request,Client.Run,
  Client.Submit}`, `Op` (`TCP.Recv`, `CheckResult`), `mkClient` (`NewReal`, `client.New`),
  `Orch` (`CfgAddrs`, `Configure`, `Model`, `Codec`, `Gen`), `Client` (`CfgAddrs`, `waitConf`,
  `mkClient`, `Codec`), `runReplica` (the package results it calls), `Server` (`CfgAddrs`,
  `waitConf`, `runReplica`). The packages' `Results.lean` keep their signatures; `Link.lean`
  composes the rest (`wp_Orch`, `wp_Server`, `wp_Client` unchanged). No class, no new axiom.

**Checks (round 5, tier restructuring merged; head `65bd34df70`, the commit carrying this note
on top):**
- fk-lean1 (`fklean1-check.sh`): vr's `TopLevelRobustness` and the five landed ones (swiftnet,
  rabianet, epaxosnet, quepaxanet, paxosnet): green (4999 jobs). `#print axioms` of
  `vr_remote_robust`, `swiftpaxos_remote_robust`, `rabia_remote_robust`, `epaxos_remote_robust`,
  `quepaxa_remote_robust`, `paxos_remote_robust` (a scratch module on a throwaway branch, not
  committed here): `propext`, `Classical.choice`, `Quot.sound` only, each.
- Here: `tier-check.py --check` ok (no vr violation; baseline and tier-linking = `origin/lean`'s);
  `gen-init.py --check` clean (271 files); `goose.py --check --project dsv-vr` clean;
  `proof_roots.namespace()` = `Perennial.EtcdGrove.`; `dups.py`: no real duplicate (its 4 hits are
  parse artifacts: `inductive`, `is`, `of`, `per`). vr's statement byte-identical to `77b42ad9c2`'s;
  no landed statement changed.

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
