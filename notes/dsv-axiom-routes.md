# dsverify axioms by route (mit-pdos/etcd-grove#49, fix 3 and fix 4)

2026-11-25. A triage for Upamanyu's review of coordinator-E's items 1, 3 and 4 (#49,
2026-11-25T15:30:08Z). His rule: **translate real Go first, then a Go model, then hand-written trusted
code, and axioms last.** Research only: no Lean was changed. Each row was checked against the Go source at
the pinned versions and, where it says "goose-clean", by running the pinned translator (Perennial
`fce59af75`'s `goose`, every declaration translated, empty config) on the package; "goose fails" quotes the
first error.

## Summary

| | translate | Go model | trusted code | stays an axiom |
|---|---|---|---|---|
| fix 3: 9 initializer axioms (on `lean`) | 6 (os/signal, yaml.v2, io/ioutil, grpc/codes, zerolog, gogoproto*) | 3 (encoding/gob: new; uuid: `models/uuid` exists; gogo proto: new) | 0 | 0 |
| fix 4: 21 axioms (`dsv-fix4` @ `63375d95ac`) | 10 (fmt.Println, uuid.ID, math/rand ×4, os/signal.Notify ×2, sort.Ints, Time.UTC) | 11 (gob ×4 + its 3 wire laws; gogo Register ×3; uuid.New) | 0 (runtime signal hooks and the godebug read only, as Perennial already does) | 0 |

\* gogoproto translates as it is, but over the gogo-proto model (its `RegisterExtension`).

**No axiom needs to stay for a reason that holds up.** Every one of the 30 has a route. What does stay:

- **Two environment premises, not axioms**: `math/rand.Seed` (the GODEBUG `randseednop` setting at its
  default; as `crypto.fips140.GodebugFips140Off`) and `os/signal.Notify` (no SIGINT, SIGTERM or SIGUSR1
  delivered). Today both are axioms whose whole content is that environment claim. Translated, each claim
  becomes a premise on the one trusted read (`internal/godebug`'s value; the runtime's `signal_recv`).
  These are the "two environment claims" Upamanyu was to review with fix 4.
- **Waiting on Perennial**: `fmt.Println` (perennial#671 stage 2, the real printer; perennial#663, a real
  `os.Stdout`). Small, but not ours to do here.
- **Waiting on a new model**: encoding/gob (7 fix-4 axioms and its init) and gogo/protobuf `proto` (3 fix-4
  axioms, its own init and gogoproto's). These are the two large items, and each retires a whole family.

Order by value per day: the quick translations first (io/ioutil, os/signal init, grpc/codes, sort.Ints,
Time.UTC, uuid via its model, math/rand); then zerolog (it also opens the 16 zerolog function axioms
already on `lean` to proof); then the gogo-proto model (6 axioms); then the gob model (8 axioms).

## 1. The nine fix-3 initializer axioms on `lean`

Each is `Dsverify/Proof/<pkg>/Init.lean`'s `axiom wp_initialize'`, reviewed in
`notes/axiom-review/dsv-inits/`. Each package fact is `True`, so the axiom's only content is "the
initializer returns". A translated initializer gets the same statement as a theorem. The route is
the main tree's pattern for this (`Code/crypto/tls.toml`, `Proof/crypto/tls/Init.lean`): translate
the variables and `init` functions; skip, with a goose `[[skip]]` reason, an initializer that no
translated code reads, whose skipping is unobservable (it terminates, cannot panic, has no effect
beyond its variable); and keep `imports` to the packages that already have proved initializers.
`init` functions cannot be skipped. They must be translated.

| package @ version | what its initializer really does | route | estimate |
|---|---|---|---|
| `os/signal` (go1.27.3, 659 lines) | zero-valued `handlers` (mutex, nil map, `[65]int64`, nil slice), `watchSignalLoopOnce`, `watchSignalLoop`; `init()` (signal_unix.go:27) is `watchSignalLoop = loop`. No panic path. | **translate**: the variables and `init.0`; `loop` and the runtime hooks stay names (goose refuses only their bodies, "external function", which init never runs) | ½ day |
| `encoding/gob` (go1.27.3, 4,857 lines) | 41 variable initializers and 3 `init`s: `reflect.TypeFor`, `bootstrapType` registering the built-in types in reflect-keyed maps, `mustGetTypeInfo`, `checkId`, the int/uintptr size switches. Panics only on its own constants. | **Go model** (new): a standard-library model of `encoding/gob`, as `models/encoding/json` is of encoding/json (Encoder/Decoder over a per-type generated codec; `models/net/rpc/rpcgen.py` already generates gob's encoding and merging decode). Its initializer is then the model's, trivial. Not translatable: goose fails (`complex` builtin, dec_helpers.go:103), and every `init` is reflection. Keep the axiom until the model lands | ½ day on top of the model (model: fix 4, below) |
| `github.com/google/uuid` v1.3.1 (427 lines in the model) | `NameSpaceDNS/URL/OID/X500 = Must(Parse(<constant>))`, `jsonNull`, `xvalues` literal, `timeNow = time.Now`, `rander = rand.Reader`, pool flags. No `init`. | **Go model, existing**: `models/uuid` (v1.3.1's code; `NewRandom` over `primitive.RandomUint64`; "Goose takes it"), whose initializer is only `xvalues`. Real v1.3.1 fails goose's modelcheck on `NameSpaceX500 = Must(Parse(…))` (hash.go:18, in-place construction). Wire the model into dsv-swiftpaxos's `module_models` (as gods is), retranslate, prove init. The model's premise: the program never assigns `crypto/rand.Reader` | ½–1 day |
| `gopkg.in/yaml.v2` v2.4.0 (9,639 lines) | `reflect.TypeOf` of 5 types and one `Elem()`; two `regexp.MustCompile` of constants; literals; `make`s; `init()` (resolve.go:20) fills `resolveTable` (indices < 256) and `resolveMap` from a constant list | **translate**: goose takes the package but one function body (modelcheck, scannerc.go:2297, `*end_mark = parser.mark`). Translate literals, `make`s and `init.0`; `[[skip]]` the six `reflect` variables and the two regexps (no translated code reads them: the functions that do stay names, as yaml is not reached by any spec); cut `imports` to proved packages (regexp's own initializer pulls in `regexp/syntax` and the unicode tables) | 1 day |
| `io/ioutil` (go1.27.3, 151 lines) | `var Discard io.Writer = io.Discard`; no `init` | **translate** (goose-clean): Perennial's `io` translates `Discard` and proves its init | ¼ day |
| `google.golang.org/grpc/codes` v1.84.0 (361 lines) | `strToCode`, a map literal of 17 constants; `init()` (code_string.go:27) is `internal.CanonicalString = canonicalString` | **translate**: `codes` with bodies and `grpc/internal`'s variables (393 lines: constants, closures, zero values; both goose-clean). Cut `grpc/internal`'s imports to `context` and `time`: `connectivity`'s `logger = grpclog.Component(…)` would pull in grpclog's env-reading `init`. (`models/grpc` holds the same files.) | ½–1 day |
| `github.com/rs/zerolog` v1.23.0 (3,191 + 736 lines) | string and number literals, function literals and values (`json.Marshal`, `time.Now`), `sync.Pool` literals, `new(int32)`; `init.0` = `SetGlobalLevel(TraceLevel)` (an atomic store) and `disabledLogger = &Nop()` (`New(ioutil.Discard)`); `init.1` sets `internal/json.JSONMarshalFunc`; `internal/json`'s `init` fills a table | **translate**: goose takes zerolog with bodies but for one initializer, `ch = newCallerHook(…)` (modelcheck, context.go:393: in-place construction), which gets a `[[skip]]` (a struct literal; read only by `Context.Caller`, which stays a name); `internal/json` is goose-clean. Its imports' initializers are proved (Perennial; the main tree's `encoding/json`) or are item 5's `io/ioutil`. **Bonus**: the translation's bodies let the 16 zerolog function axioms on `lean` (`notes/axiom-review/dsv-fix4/zerolog.md`) be proved too | 1–2 days (the init) |
| `github.com/gogo/protobuf/proto` v1.3.2 (16,026 lines) | 51 initializers (`errors.New`, `reflect.TypeOf((*T)(nil)).Elem()`, `make`/map literals: `protoTypedNils`, `revProtoTypes`, `enumValueMaps`, `protoFiles`, `extensionMaps`, …); 3 `init`s calling `RegisterType` on its own wrapper types (duration, timestamp, wrappers) | **Go model** (new, a module model like `models/gods`): goose fails on the real package (labels on plain statements, decode.go:192; the `print` builtin, properties.go:445; reflect/unsafe table codecs). The model keeps the registry: `RegisterEnum` and `RegisterFile` verbatim (map code with the real duplicate panic), `RegisterType` and `RegisterExtension` with `reflect.Type` keys replaced by the typed-nil message value (generated code passes only typed nils; `MODEL:`), and the API rabia's generated code calls. The registry is then program state, as coordinator-E's item 2 asks for protobuf-go's | 3–5 days, with difftest (shared with fix 4's 3 Register axioms) |
| `github.com/gogo/protobuf/gogoproto` v1.3.2 (1,458 lines; `protoc-gen-gogo/descriptor` 4,125) | 76 `&proto.ExtensionDesc{…}` literals, three `var _ =`, the descriptor bytes; `init()` = 76 `RegisterExtension` (**panics on a duplicate** field number for an extended type) and `RegisterFile("gogo.proto", …)` | **translate** (both packages goose-clean) over the gogo-proto model. The init spec takes the precondition "these 76 (type, field) pairs are not registered", which the kit's proof discharges (gogoproto is the only package that registers extensions: review's attack 2). That is the same shape as coordinator-E's grpc fix | 2–3 days after the model |

## 2. The 21 axioms of `dsv-fix4` (@ `63375d95ac`)

Reviews in `notes/axiom-review/dsv-fix4/` on that branch. "Why an axiom today" is the real
reason (goose's or Perennial's), not the review's.

| # | axiom | Go function (package) | why an axiom today | route | estimate |
|---|---|---|---|---|---|
| 1 | `encoding.gob.NewEncoder.wp_proof` | `gob.NewEncoder` (encoding/gob) | untranslatable: reflect throughout, `complex` builtins, unsafe | **Go model** (new std model of encoding/gob, as `models/encoding/json`; the codec generated per type in gob's format, which `rpcgen.py` already emits for net/rpc) | 1–2 weeks for 1–7 together (model + difftest + Lean specs) |
| 2 | `encoding.gob.NewDecoder.wp_proof` | `gob.NewDecoder` | same | Go model (as 1) | (in 1) |
| 3 | `encoding.gob.Encoder.EncodeW.wp_proof` | `(*Encoder).Encode` on an `*MSync` | same | Go model (as 1) | (in 1) |
| 4 | `encoding.gob.Decoder.Decode.wp_proof` | `(*Decoder).Decode` | same | Go model (as 1) | (in 1) |
| 5 | `wireBytes_peel` | gob's wire format (a stream of one value determines it) | a law of real gob's encoding, with no code to prove it of | **Go model**: becomes a lemma about the generated decoder (the generator is the trusted artifact, as pbgen/rpcgen) | (in 1) |
| 6 | `wireFits_of` | gob's size limit (`tooBig`) | same | Go model: lemma about the generated encoder | (in 1) |
| 7 | `wireBytes_exists` | gob encodes every well-formed `*MSync` | same | Go model: lemma about the generated encoder | (in 1) |
| 8 | `raxos.hyp.fmt.Println.wp_proof` | `fmt.Println` = `Fprintln(os.Stdout, a...)` | Perennial excludes `Println` (`fmt.toml`: `"!Println"`) and leaves `os.Stdout` unallocated (`TrustedCode/os.lean`, perennial#663); its printer for non-basic operands is reflection (stage 2 of perennial#671) | **translate**, once Perennial has a real `os.Stdout` and printer (both open there). Interim, if needed sooner: Perennial-trusted `Println` beside its trusted `Printf`/`Print` (route 3, still better than an axiom here) | 2–4 days in Perennial |
| 9 | `gogo.proto.RegisterEnum.wp_proofMsgType` | `proto.RegisterEnum` (gogo v1.3.2, properties.go) | gogo proto is names only (the package fails goose); the function itself is plain map code | **Go model** (the gogo-proto registry model of fix 3): verbatim; the spec gets "`message.MsgType` not yet registered", and the duplicate panic is real | 3–5 days for 9–11 with fix 3's gogo items |
| 10 | `gogo.proto.RegisterType.wp_proof` | `proto.RegisterType` | reflect (`TypeOf`, `ValueOf().Kind/Pointer`, `Zero().Interface()`, a `reflect.Type`-keyed map) and `log.Printf` | **Go model**: the registry keyed by the typed-nil value; `log.Printf` is Perennial's trusted model | (in 9) |
| 11 | `gogo.proto.RegisterFile.wp_proof` | `proto.RegisterFile` | names only (the package fails goose); one map assignment | **Go model** (verbatim) | (in 9) |
| 12 | `google.uuid.New.wp_proof` | `uuid.New` (v1.3.1) | `crypto/rand.Reader` + `io.ReadFull` (Perennial's `crypto/rand` is names only, `Reader` trusted) | **Go model, existing**: `models/uuid` (`NewRandom` over `primitive.RandomUint64`); premise: the program never assigns `crypto/rand.Reader` | 1 day for 12–13 with the init |
| 13 | `google.uuid.UUID.ID.wp_proof` | `UUID.ID` = `binary.BigEndian.Uint32(uuid[0:4])` | names only: only because uuid is | **translate** (the model's `dce.go` is v1.3.1's; Perennial translates `BigEndian`) | (in 12) |
| 14 | `math.rand.NewSource.wp_proof` | `rand.NewSource` → `newSource` → `(*rngSource).Seed` (rng.go) | not done: Perennial's `math/rand.toml` translates only the global `Int63`…`Intn` paths | **translate**: rng.go is plain Go (`seedrand`, the 607-entry `rngCooked`, index arithmetic); goose fails on the package only for `goto` in `Float64`/`Float32` and the external `runtime_rand`, both outside this path. A Perennial change | 1–2 days for 14–16 (Perennial) |
| 15 | `math.rand.New.wp_proof` | `rand.New` (`s64, _ := src.(Source64)`; an allocation) | not done | **translate** (Perennial) | (in 14) |
| 16 | `math.rand.rngSource.Int63.wp_proof` | `(*rngSource).Int63` / `Uint64` | not done | **translate** (Perennial); `rngTok` becomes the source's points-to | (in 14) |
| 17 | `math.rand.Seed.wp_proof` | `rand.Seed` (go1.27.3: returns at once unless `randseednop.Value() == "0"`) | `randseednop` is an `internal/godebug` setting Perennial skips; the axiom's content is an environment claim | **translate**, with the godebug read as Perennial already does for `crypto/fips140` (`TrustedCode/crypto/fips140.lean`): the claim becomes a premise "GODEBUG randseednop at its default" beside `GodebugFips140Off` (environment claim 1) | 1 day (Perennial) |
| 18 | `os.signal.Notify.wp_proofQuietSigs` | `signal.Notify(c, SIGINT, SIGTERM)` | names only; the claim is that no such signal arrives | **translate** `Notify` and its helpers (signal.go: mutex, map, `Once`, a goroutine; goose-clean but the runtime hooks), with `signal_enable/disable/ignore/recv` as trusted code (they are `//go:linkname` runtime functions); the claim becomes a premise on `signal_recv`'s model, "none of these signals is delivered" (environment claim 2) | 2–3 days for 18–19 |
| 19 | `os.signal.Notify.wp_proofUsr1Sigs` | `signal.Notify(c, SIGUSR1)` | same | same | (in 18) |
| 20 | `raxos.hyp.sort.Ints.wp_proof` | `sort.Ints` = `slices.Sort(x)` (go1.27.3, sort.go:170) | not done: Perennial's `sort.toml` lacks `Ints` | **translate**: add `Ints` in Perennial; proof over Perennial's `slices.wp_Sort` (as gryff's ShortCircuit uses since dsv-fix4) | ¼ day |
| 21 | `raxos.hyp.time.Time.UTC.wp_proof` | `Time.UTC` = `t.setLoc(&utcLoc); return t` | not done: Perennial translates `Time.sec`, `stripMono`, `utcLoc`, but not `UTC`, `setLoc` | **translate**: add two names to Perennial's `time.toml` | ¼ day |

Counts: translate 10 (8, 13–21), Go model 11 (1–7 new gob model, 9–11 new gogo model, 12 existing uuid
model), axiom 0. The fix-4 axioms reviewed on that branch but not among the 21 (`log.Default`/`Printf`/`Println`,
`zerolog`'s 16, QuePaxa's protobuf-go `Marshal`/`Unmarshal`) are already on `lean`. zerolog's are covered by
the zerolog translation above. The other two families are out of scope here.

## 3. go-redis v8.11.5: the initializer's import closure (item 1)

`go list -deps github.com/go-redis/redis/v8` (rabia's module, linux/amd64): **178 packages, 298,161 Go
lines**. Most of them do not need work. Go initializes the whole closure, but a translation's
initializer calls only the imports its config keeps, and the packages go-redis reaches first
(`crypto/tls`, `net`, `os`, `reflect`, `fmt`, `runtime`, …) already have translations with proved
initializers whose `imports` stop there. That is what fixes the real closure:

| status in the closure | packages | Go lines |
|---|---|---|
| translated, initializer proved (Perennial, or the main tree: `crypto/tls`, `net`, `net/url`, `bufio`, `encoding/hex`, `runtime`, `os`, …) | 60 (+ `internal/nettrace`, names only) | ~195,000 (runtime 80k) |
| behind those (all of `crypto/internal/*`, `crypto/x509`, `vendor/…`, `unicode`, `internal/godebug`, …): not translated, **not reached** | 106 (`log/internal` among them) | ~87,000 |
| **to do**, below | 11 + 3 Perennial gaps | ~16,000 (of which go-redis's root 13,201, nearly all function bodies init never runs) |

The packages to do (all with goose's verdict from running it):

| package | lines | translated already? | goose | what its initializer needs |
|---|---|---|---|---|
| `github.com/go-redis/redis/v8` | 13,201 | names only (`Dsverify/`, `InitHyp` premise) | clean, with bodies | `errClusterNoNodes = fmt.Errorf(<constant>)` (Perennial's trusted `Errorf`), `errRingShardsDown = errors.New`, `ErrClosed = pool.ErrClosed`, 47 `var _ I = (*T)(nil)` |
| `…/v8/internal` | 238 | no | clean | `Logger = &logger{log: log.New(os.Stderr, "redis: ", …)}`: **needs Perennial's `log.New` translated** (a body of 5 lines) **and `os.Stderr`**, which Perennial leaves unallocated (perennial#663). Until then: keep go-redis's functions names only and `[[skip]]` `Logger` |
| `…/v8/internal/pool` | 937 | no | clean | 2 `errors.New`, `timers = sync.Pool{New: …}` (closure not run), 4 `var _` |
| `…/v8/internal/proto` | 667 | names only (`Dsverify/`) | clean | nothing (constants) |
| `…/v8/internal/hscan` | 294 | no | clean | `decoders` (a slice literal of function values at `reflect.Kind` constants), `globalStructMap = new(structMap)` (a zero `sync.Map`) |
| `…/v8/internal/hashtag` | 78 | no | clean | `crc16tab`, a `[256]uint16` literal |
| `…/v8/internal/rand` | 50 | no | clean | `pseudo = rand.New(&source{src: rand.NewSource(1)})`: **needs math/rand's `NewSource`/`New` translated**: fix 4's rows 14–16, the same Perennial change; the init proof runs `rngSource.Seed`'s loop |
| `…/v8/internal/util` | 42 | no | clean | nothing |
| `github.com/cespare/xxhash/v2` v2.1.2 | 305 | no | clean with `-tags purego`; without it `Sum64` is assembly (xxhash_amd64.s), so it is trusted or a name | five `uint64` constants copied to variables |
| `github.com/dgryski/go-rendezvous` | 79 | no | clean | nothing |
| `encoding` (std) | 78 | no | clean | nothing (interfaces) |
| Perennial gaps | | | | `log.New` (+ `SetOutput`/`SetPrefix`/`SetFlags`), math/rand's rng.go, `os.Stderr` (or the skip) |

`crypto/sha1` (Perennial, init proved) is in go-redis's own import list, and its kept imports reach
`crypto/fips140`. So with go-redis's imports kept, `GodebugFips140Off` enters as coordinator-E says:
the `fips140` panic stays in Perennial's model. The main tree's `crypto/tls` itself has `imports = ["!*"]`.

**Size verdict: small.** About 11 short packages and two Perennial additions, which fix 4 needs anyway.
Estimate 3–4 days: go-redis and its internals ½–1 day (config, retranslate, init proofs of literals); xxhash,
rendezvous and `encoding` ¼ day; Perennial `log.New` ½ day; math/rand shared with fix 4.

## How this was checked

- The axioms: `grep '^axiom.*wp_initialize'` under `Dsverify/` on `lean` (nine); `git diff
  lean...dsv-fix4 -- '*.lean' | grep '^+axiom'` (21: `sort.Slice`'s was added and retired within the
  branch).
- Go sources: go1.27.3's standard library (`/usr/local/go/src` at go1.27.1 where identical), modules from
  `~/go/pkg/mod` at the versions the kits' `go.mod` pin.
- goose: Perennial `fce59af75`'s `goose` built locally and run with an empty config (translate everything,
  keep every import) from `examples/dsverify/{rabia,quepaxa,swiftpaxos}`. The verdicts above are its output.
  A clean run means the translation is produced. It does not mean the bodies are provable.
- The closure: `go list -deps -json`, with each package checked for a `.lean` translation in Perennial,
  `Code/`, `Net/Code/` and `Dsverify/Code/`, and for an initializer proof (Perennial's `initialize.lean`,
  this repository's `Init.lean` with no axiom or `InitHyp`).

## Step 2 handoff (dsv-retire-2, 2026-11-25)

Branch `dsv-retire-2` (worktree `/shared/etcd-grove-dsvretire2`; fk-lean2 worktree `wt/dsv-retire-2`, built
incrementally there, 4761 jobs green at `1c7a88da48`). Base: `dsv-retire-1` @ `60e754019a` + lean `2926d09437`
(merge `a4f37b7acf`, pin `83ba7951a`).

**Done.**
- `google_golang_org.grpc.codes.wp_initialize'` retired (`d64ea0bfdb`): codes (`strToCode`, `init.0`) and grpc
  `internal`'s `CanonicalString` translated into the part; the hook-cell machinery moved to the generic
  `Proof/runtime/InitInv.lean` (main tree's `cache/v3/Base`, `grpc/internal/Hooks` import it); gen-init's
  `DSV_OWN_CFG` lets a kit configure its own translation of a main-tree package.
- `github_com.google.uuid.wp_initialize'` retired (`dab1a9f556`, `1c7a88da48`): uuid translated from
  `models/uuid` (swiftpaxos `module_models`).
- Perennial (`/shared/tmp/perennial-retire2`, branch `retire2-codes-uuid-rand`, head **`8fb3c9fd5`**, merged with
  Perennial `origin/lean` `5e79daf22`; `etc/land.sh prepare` passed; not reviewed, not pushed): math/rand's
  `NewSource`, `newSource`, `New`, `rngSource.{Seed,Int63,Uint64}`, `seedrand`, `rngCooked` translated and proved
  (`e609d80e7`). Token `math.rand.ownRngSource p`; linked `math.rand.wp_NewSource`, `wp_New`,
  `rngSource.wp_Uint64`/`wp_Int63`/`wp_Seed`. The client statements prove with `iintro`/`iapply` (not
  `wp_start`). `rngCooked`'s init needs `LetChain.lean` (see `notes/perennial-changes.md`, negative constants).
  Next on it: `/review-trusted --fix`, `etc/land.sh mark-reviewed`; the user pushes.

**Left, in order.**
1. Merge `dsv-retire-1`'s new head (re-merged with lean, pin `5e79daf22`); then bump the pin to Perennial
   `8fb3c9fd5` (`lakefile.toml`, `lake-manifest.json`); build it on fk-lean2 (`/home/ubuntu/eg/perennial-8fb3c9fd5`,
   as `pbuild-83ba7951a.sh` there: push the commit to `/home/ubuntu/eg/perennial.git` first).
2. math/rand client: `Dsverify/Proof/math/rand/RngDefs.lean`: `rngTok p := math.rand.ownRngSource p` (drop the
   opaque); `NewSource.lean`, `New.lean`, `rngSource__Int63.lean`: theorems from the linked results, axioms
   deleted. `Seed.wp_proof` stays an axiom (its proof needs either the randseednop environment premise or the
   reseed path with a lockedSource global generator; both out of this step's rules).
3. uuid `New` and `UUID.ID` (coordinator's decision, 2026-11-25): `New.spec` gains `[github_com.google.uuid.Assumptions]`,
   `UUID.ID.spec` gains `isPkgInit uuid` in its precondition (`LibSpecs.lean`); their one caller
   `client.NewClientLog.wp_proof` has both; no top-level statement changes. Ledger entry in
   `notes/specs-only/ledger.md` (spec gains premise; reason: the translation's unfolding/initialization;
   decision: approved by the coordinator), then prove both from the translation and delete the axioms.
4. For each retired axiom: `etc/tcb-baseline.txt`, `etc/tcb-collections/dsv-{quepaxa,swiftpaxos,rabia,gryff}.txt`
   (grep the names; removals only), `notes/axiom-review/README.md` (retired). Check that agent B already did this
   for the two init axioms.
5. Use `PERENNIAL_DIR=/shared/tmp/perennial-83ba-clean` (or a clean checkout at the new pin) for
   `etc/gen-init.py --check`; `etc/gates.sh` on fk-lean2 (`FKLEAN1_GATES=1 FKLEAN_HOST=fk-lean2
   /shared/tmp/fklean1-check.sh /shared/etcd-grove-dsvretire2 dsv-retire-2 -`); push `dsv-retire-2` over https;
   STATUS.md "Last updated" entry.

## Step 3, zerolog (branch `dsv-retire-3`, 2026-11-26): state and handoff

**Done.** zerolog v1.23.0 is translated with bodies, with `internal/json` (`Dsverify/Code/github_com/rs/zerolog.toml`:
everything but `Context.Caller`, which stays a name, and the `[[skip]]`ped initializer `ch`; goose refuses a
skipped variable read by translated code, so `Context.Caller` has to go too). Project `dsv-rabia`
(`etc/dsv/rabia.py`) gained the package `internal/json`, the roots `io/ioutil=Dsverify`, `encoding/json=`,
`path/filepath=`, `internal/filepathlite=` (zerolog's imports, each with a proved initializer: Perennial's, the
main tree's, or `Dsverify`'s `io/ioutil`), `std_models=["encoding/json"]` (`InterfaceMarshalFunc = json.Marshal`
names the model's `Marshal`) and, in gen-init's `MAIN`, `path.filepath`, `internal.filepathlite`,
`encoding.json`. `etc/gen-init.py` regenerated the rabia `PkgTable`s (zerolog's imports now in them).
zerolog is still in `HYP_INITS` (its `wp_initialize'` still the axiom).

**Not done: the tree does not build yet.** `internal/json` has no `Base.lean` (no `isPkgInit` instance), which
the regenerated `PkgTable`s name. Next steps, in order:

1. `Dsverify/Proof/github_com/rs/zerolog/internal/json/Base.lean`: the fact. `init.0` (string.go) fills
   `noEscapeTable` in a loop over `0..0x7e`; zerolog's `init.1` **stores into `json.JSONMarshalFunc`**, another
   package's variable, so `internal/json`'s fact must hand out a writable cell: `inv (∃ f, JSONMarshalFunc ↦ f)`
   (or a full points-to through gen-init's `newvars`, as the main tree does for cross-package stores: grep
   gen-init for an example). `AppendString` indexes `noEscapeTable[s[i]]` (a `[256]bool` by a byte: in
   bounds) and `hex[b>>4]`: the fact needs only `noEscapeTable ↦□ some array`, not its contents.
2. Move `github_com.rs.zerolog.internal.json` and `github_com.rs.zerolog` from `HYP_INITS` to `PKGS` (rabia.py)
   with `SPECIAL` configs (gen-init cannot step the loop of `internal/json`'s `init.0`, nor the calls in
   zerolog's `init.0`: `SetGlobalLevel(TraceLevel)` (an atomic store to `*gLevel`, held at init) and
   `disabledLogger = &Nop()` = `New(nil).Level(Disabled)`, which reads `ioutil.Discard`: `io/ioutil`'s fact
   (`Dsverify/Proof/io/ioutil/Base.lean`, `True` today) must keep `∃ w, Discard ↦□ w`, which its init has from
   `io.isInit`). The three `sync.Pool` literals (`eventPool`, `arrayPool`, console's buffer pool): Perennial's
   `init_Pool` (`Perennial/Proof/sync/PoolDefs.lean`). Delete zerolog's `Init.lean` axiom.
3. zerolog's fact (`Base.lean`, `True` today), for the function proofs: `gLevel ↦□ p ∗ inv (∃ v, p ↦ v)`,
   `LevelFieldName ↦□ "level"`, `LevelFieldMarshalFunc ↦□ f` with `f`'s spec (`Level.String`),
   `enc ↦□ Encoder{}`, `eventPool`'s `isPool` with `P` = "a `*Event` with its buffer owned"; persistent
   (`↦□`), so no client can write zerolog's variables (the dsv-fix6 review's condition 1).
4. Define the tokens, opaque today: `loggerMade lg` := "`lg` is `New(nil)`'s logger" (`∃ w, ioutil.Discard ↦□ w`
   and `lg` = `Logger{w := (w as a LevelWriter, or levelWriterAdapter{w}), level := TraceLevel}`, other fields
   zero); `eventTok e` := `e = null ∨` "`e ↦` an `Event` whose buffer is owned, non-empty (`AppendKey` reads
   `dst[len(dst)-1]`), `w` a logger's, `done`/`ch` nil, level one of the five". As retire-2's `rngTok :=
   ownRngSource`: the axioms' statements are unchanged, their vocabulary gets its meaning.
5. Prove, riskiest first: `Logger.{Trace,..,Error}` (`should`, `GlobalLevel`, `eventPool.Get`, `.(*Event)`,
   `e.Str(LevelFieldName, LevelFieldMarshalFunc(level))`), `Event.Str` (`AppendKey`, `AppendString` and its
   `appendStringComplex` loop over Perennial's `utf8.DecodeRuneInString`), `New`, `ParseLevel` (`"warn"`),
   `SetGlobalLevel`.

**Session 2 (2026-11-26), WIP handoff (stopped at the context limit; nothing built yet).** Pushed, not built:
- `Dsverify/Proof/github_com/rs/zerolog/internal/json/Base.lean`: fact `jsonInit` = `hookCell GoFunc
  (globalAddr JSONMarshalFunc) ∗ ∃ a : GoArray Bool 256, globalAddr noEscapeTable ↦□ a`.
- `.../internal/json/InitLoop.lean`: `wp_init0` (`init.«0»`'s loop: table owned before and after).
  **DRAFT with two `sorry`s** (the loop body: `array_acc` on `arrayIndexRef Bool (sint.Z k)`, store,
  `wp_for_post`, re-establish `0 ≤ k ≤ 127`; `hb` from the array points-to's length). Must be finished
  before anything lands; never in a landed commit.
- `etc/gen-init.py`: new config key `initfn_apply` (a translated `init` applied by its own spec instead
  of stepped into).
- `etc/dsv/rabia.py`: zerolog and `internal/json` moved from `HYP_INITS` to `PKGS`, with `SPECIAL`
  configs (allocs, `initfn_apply` for json's `init.«0»`, the hook-cell store in zerolog's `init.«1»`,
  json's `finish`). zerolog's fact still `True`. **Not yet written**: zerolog `init.«0»`'s steps
  (`SetGlobalLevel(TraceLevel)`: probably `wp_func_call; wp_call; wp_auto` and the atomic store on the
  `new(int32)` cell; `Nop()` = `New(nil).Level(Disabled)`: reads `ioutil.Discard` via io/ioutil's new
  fact, then a type assertion `w.(LevelWriter)` on an unknown `w`: expect a case split), and whatever the
  translated variable initializers need (the three `sync.Pool` literals, `new(int32)`s). Iterate on the
  generated `Init.lean`, then move the steps into `rabia.py` and rerun gen-init.
- `etc/dsv/quepaxa.py` + `Dsverify/Proof/io/ioutil/Base.lean`: io/ioutil's fact is now
  `∃ w, Discard ↦□ w` (its `finish` makes it).
- Regenerated by `PERENNIAL_DIR=/shared/perennial-a706aeb9a etc/gen-init.py`: zerolog's `Init.lean` (the
  axiom gone, the proof draft), json's `Init.lean`, io/ioutil's, `PkgInitDsv`, rabia's `Init`/`PkgTable`s.

Build: the remote worktree `~/eg/wt/dsv-retire-3` on fk-lean1 was being seeded (from `wt/lean-warm`) by
`/shared/tmp/fklean1-check.sh /shared/etcd-grove-dsvr3 dsv-retire-3` with targets
`Dsverify.GeneratedProof.github_com.rs.zerolog Dsverify.GeneratedProof.github_com.rs.zerolog.internal.json
Dsverify.Proof.github_com.rs.zerolog.Spec` at `04c16d3753` (log `/shared/tmp/dsvr3-seed.log`; remote log
`~/eg/logs/dsv-retire-3-*.log`). For iteration after it: `/shared/tmp/dsvr3-rb.sh <targets>`
(The seed finished: the worktree exists; its build at `04c16d3753` failed, as expected, in zerolog's `Base.lean` (`failed to synthesize`, lines 27/29: no `internal/json` instance at that commit, which `ca1e516109` adds).) It tars the local changed files into the remote worktree and runs `lake build` there under the
build lock and `MemoryMax=50G`.

Next, in order: build `...internal.json.InitLoop` and finish `wp_init0`; build json's and zerolog's
`Init` (fix steps, back into `rabia.py`, regenerate); build the rabia roots; then steps 3-6 of the list
above (zerolog's fact, `eventTok`/`loggerMade` definitions, the nine proofs, the remaining-axioms note
`notes/axiom-review/dsv-zerolog-remaining.md`, the checks, gates).

**Session 3 (2026-11-26), WIP handoff (stopped at the context limit).** Committed (`150c26d79a`, no `sorry`):
- `internal/json/InitLoop.lean`: `wp_init0` finished (no `sorry`; helper `wp_store_arrBool`); json's `Base.lean`
  imports its imports' `Base`s. json's `Init.lean` checks (`initfn_apply` now `$$ HnoEscapeTable`, no brackets).
- `zerolog/NewNil.lean` (new, defs tier): `newLevelWriter`, `newLogger w` (the logger `New` builds from
  `Discard`'s value `w`), `wp_New_nil w` (`{{ Discard ↦□ w }} New(nil) {{ RET #(newLogger w); True }}`, by cases on
  `w` and `typeSetContains`), `wp_Nop`. Both check with `etc/lean-check.py`.
- `rabia.py` zerolog `SPECIAL`: `before` (`arrayPool`: one `repeat (first | rw recv_eq_func_mk | wp_func_lits | wp_auto)`
  over all the variable initializers; `$inits`: `rename_i`/`irename` of `gLevel`'s cell to `HgCell`), `after`
  `init.«0»` (`SetGlobalLevel`'s `StoreInt32` through `wp_apply_core`, then `wp_Nop`), import `NewNil`.
  zerolog's `Base.lean` imports its imports' `Base`s (fact still `True`). Regenerated `Init.lean` checks
  (`lean-check -a`, 0 errors); zerolog's `Init.lean` axiom is gone.
- `quepaxa.py` io/ioutil `finish`: `try iexists _`, `try iexact HDiscard` (`is_pkg_init_finish` already closes it).

**Built green** (fk-lean1, at `150c26d79a`, 3811 jobs): `Dsverify.Proof.rabia.examples.rabianet.TopLevelRobustness
Dsverify.Proof.rabia.roles.server.Link Dsverify.Proof.raxos.examples.quepaxanet.TopLevelRobustness
Dsverify.Proof.raxos.{Proposer,Proxy,Replica}.Results` (step 3 of the brief done). Tools:
`/shared/tmp/dsvr3-rb.sh <targets>` (lake build there; now syncs every file changed since the remote's base
`04c16d3753`, committed or not), `/shared/tmp/dsvr3-lc.sh [-a|-q|--goal L] FILE` (`etc/lean-check.py` there;
use `-a`: the incremental report can show a stale error).

**Next, in order**: step 3's list above from item 3 (zerolog's fact: `gLevel ↦□ p ∗
inv (∃ v, p ↦ v)` from `HgCell` in `finish`, the level strings and `LevelFieldMarshalFunc` `↦□`, `eventPool`'s
`isPool`); `loggerMade lg := ∃ w, Discard ↦□ w ∗ ⌜lg = newLogger w⌝` (needs the defs' instance context in
`Spec.lean`); `New.wp_proof` from `wp_New_nil`; `SetGlobalLevel`; `ParseLevel("warn")` (it calls
`fmt.Errorf` with `%s` before the switch, and compares with `LevelFieldMarshalFunc(l)`: needs `Errorf`'s spec
and the fact's marshal function); the level methods and `Str`; the remaining-axioms note; checks; gates.

**Blocked by Perennial (recorded in `notes/perennial-changes.md`, 2026-11-26)**: `Event.{Int,Ints,Int64,Uint32,
Bool,Float64}` call `strconv.AppendInt`/`AppendUint`/`AppendBool`/`AppendFloat`, names only in Perennial;
`Event.Msg` writes to `ioutil.Discard`, whose value `io.isInit` hides. These seven stay axioms; once `eventTok`
and `loggerMade` are concrete (step 4) their preconditions narrow but their posts become concrete too (a field
method gives back `e ↦` an event with its buffer), so they must be re-reviewed with the `axiom` skill over the
concrete tokens before that lands. So at most 9 of the 16 function axioms
plus the initializer retire on this route.

**Session 4 (2026-11-26).** The rabia/quepaxa roots built green at `150c26d79a` (session 3's build). Done since:
- zerolog's fact `zerologInit` (`Base.lean`; `zerologInit_access`): `gLevel ↦□ p ∗ inv gLevelN (∃ v, p ↦ v)`,
  `LevelFieldName ↦□ "level"`, `LevelFieldMarshalFunc ↦□ f ∗ marshalSpec f` (on `fiveLevels`, `f lv` returns
  `levelString lv`), `enc ↦□ Encoder{}`, `eventPool ↦□ ep ∗ sync.isPool ep f True eventElem` (`f ≠ nil`),
  `ioutil.Discard ↦□ w`. Proved by the generated `Init.lean` (`rabia.py`: `ZL_FACT` at the end of `init.«0»`'s
  `after`, while the goal is still a WP; `ZL_FIN` after `FIN_PRE[:6]`). `Level.String` needs a local
  `go.NotInterface go.int8` (`haveI`, as Perennial's `time.Duration` proofs do for `int64`).
- `loggerMade lg := ∃ w, Discard ↦□ w ∗ ⌜lg = newLogger w⌝` (`Spec.lean` now imports `NewNil`).
- Proved, axioms gone: `New.wp_proof` (`wp_New_nil`), `SetGlobalLevel.wp_proof` (the invariant),
  `ParseLevel.wp_proofWarn` (`marshalSpec`; the switch comes first, `fmt.Errorf` is not reached).
- `notes/axiom-review/dsv-zerolog-remaining.md`: the 13 left, for a fresh review.

**Not done: `eventTok` is still opaque**, deliberately: a definition changes what all 13 remaining axioms claim,
so it goes in with the proofs of the level methods and `Str` (and the review redone over it). Next, in order:
1. `Event.Str` (riskiest): `AppendKey` (`dst[len(dst)-1]`) and `internal/json.AppendString` with
   `appendStringComplex`'s loop over `utf8.DecodeRuneInString`; `internal/json`'s fact has `noEscapeTable ↦□`.
2. Define `eventTok e := ⌜e = null⌝ ∨ ∃ v bs, e ↦ v ∗ v.buf' ↦* bs ∗ ownSliceCap ∗ ⌜bs ≠ []⌝ ∗ (∃ w, Discard ↦□ w ∗
   ⌜v.w' = newLevelWriter w⌝) ∗ ⌜v.done' = func.nil ∧ v.ch' = slice.nil ∧ v.stack' = false ∧ v.level' ∈ fiveLevels⌝`
   (`Msg`'s axiom needs all of it; check its body). The pool gives `eventElem` (buffer owned, any contents):
   `newEvent` truncates it and appends `{`.
3. `Logger.{Trace,..,Error}`: `should` (`l.level` is Trace, `GlobalLevel()` through the invariant; disabled →
   `nil`), `newEvent` (`eventPool.Get`: `isPool`; `.(*Event)` from `eventElem`), `e.Str(LevelFieldName,
   LevelFieldMarshalFunc(level))` (`marshalSpec`).
4. Re-review the 7 blocked event axioms over the defined `eventTok`; tcb baselines; gates.

**Session 4 stopped at the context limit (checks pending).** Done: tier-check ok (zerolog `Base` now imports
`Proof.path.filepath.PkgInit`, not the proof module `Proof.path.filepath.Base`); `etc/gen-init.py --check` ok;
`etc/goose.py --check --project dsv-rabia` ok; the six rabia/quepaxa targets built green (before the tier fix,
which changes only that import). **Running when stopped**: a full `lake build` on fk-lean1
(`/shared/tmp/dsvr3-rb.sh` with no targets, log `/shared/tmp/dsvr3-buildall.log`), started because
`etc/tcb-report.py` refused (560 modules out of date there). Next: once it is green (rerun `dsvr3-rb.sh`
incrementally first: the tier fix was synced mid-build), on fk-lean1 run `etc/tcb-report.py --check --update`, then
`--collection etc/tcb-collections/dsv-rabia.txt --check --update` (and `dsv-quepaxa.txt`); expected removals only:
`zerolog.wp_initialize'`, `New.wp_proof`, `SetGlobalLevel.wp_proof`, `ParseLevel.wp_proofWarn` (and
`internal.json`'s initializer if listed); commit those; then `etc/gates.sh` once, logged, in the background.
