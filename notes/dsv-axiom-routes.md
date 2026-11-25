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
