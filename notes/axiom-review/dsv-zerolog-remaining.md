# zerolog's remaining axioms after dsv-retire-3 (for a fresh review)

Written 2026-11-26 (branch `dsv-retire-3`, mit-pdos/etcd-grove#49 step 3), for an independent `axiom`
review of what is left. zerolog v1.23.0 (`/root/go/pkg/mod/github.com/rs/zerolog@v1.23.0`) is now
translated **with bodies** into the part (`Dsverify/Code/github_com/rs/zerolog.lean`, with
`internal/json`); the earlier reviews (`dsv-fix4/zerolog.md`, `dsv-fix6/zerolog.md`) were of the
names-only version, where the package fact was `True`.

## What changed under the remaining axioms

- **The package fact** (`Base.lean`, `zerologInit`), proved by zerolog's initializer (`Init.lean`,
  generated; no axiom): `gLevel ↦□ p` with `inv (∃ v : w32, p ↦ v)`; `LevelFieldName ↦□ "level"`;
  `LevelFieldMarshalFunc ↦□ f` with `marshalSpec f` (on the five levels `Trace`..`Error`, `f lv` returns
  `levelString lv`); `enc ↦□ Encoder{}`; `eventPool ↦□ ep` with `sync.isPool ep f True eventElem` (an
  `*Event` with its buffer owned; `f` the pool's non-nil `New`); `ioutil.Discard ↦□ w`. Every variable
  the fact names is read-only for good (`↦□`), so no client can write zerolog's variables (the dsv-fix6
  review's condition 1 now holds by construction, for those variables).
- **`loggerMade lg`** (`Spec.lean`) is defined: `∃ w, ioutil.Discard ↦□ w ∗ ⌜lg = newLogger w⌝`, with
  `newLogger w` (`NewNil.lean`) the struct `New(nil)` builds: writer `w` as a `LevelWriter` (itself if
  its dynamic type is one, else `levelWriterAdapter{w}`), level `TraceLevel` (-1), sampler, context
  and hooks nil, `stack` false. `loggerOk lg = □ loggerMade lg`, as before. Unlike the opaque version,
  it is no longer produced only by `New`'s axiom: any `lg` equal to `newLogger w` has it (a logger value
  with the same fields behaves the same).
- **`eventTok`** (`EventTok.lean`) is **defined** (session 6, 2026-11-26): `e = null`, or `e ↦ v` with
  `v.buf' ↦* bs`, its `ownSliceCap`, `bs ≠ []`, `ioutil.Discard ↦□ w` and `v.w' = newLevelWriter w`,
  `v.done' = nil`, `v.ch' = nil`, `v.stack' = false`, `v.level' ∈ fiveLevels`. This changes what the
  remaining axioms claim: the review must be done over this definition (rabia's statement premise
  `Hyps` quantifies the token existentially, so its text is unchanged).

## Retired (proved from the translation; statements unchanged)

- `New.wp_proof` (`New.lean`), from `wp_New_nil` and the fact's `Discard`.
- `SetGlobalLevel.wp_proof` (`SetGlobalLevel.lean`): the atomic store through the fact's invariant.
- `ParseLevel.wp_proofWarn` (`ParseLevel.lean`): the switch through `marshalSpec`; `fmt.Errorf` (after
  the switch) is not reached on `"warn"`.
- (session 3) zerolog's and `internal/json`'s `wp_initialize'`.
- (session 6) `Event.Str.wp_proof` (`Event__Str.lean`), over the defined `eventTok`, from
  `internal/json`'s `AppendKey`/`AppendString`/`appendStringComplex` lemmas
  (`internal/json/AppendString.lean`) and Perennial's `utf8.DecodeRuneInString` spec.
- (session 7) `Logger.{Trace,Debug,Info,Warn,Error}.wp_proof` (`Logger__*.lean`), from the lemma
  `wp_Logger_newEvent` (`LoggerNewEvent.lean`): `should` (the logger's level is Trace; `GlobalLevel()`
  through the fact's invariant, either outcome: disabled returns `nil`), `newEvent` (`eventPool.Get` by
  `isPool`, the buffer truncated with `ownSlice_slice_with_cap`, `{` appended), the fields set, then
  `e.Str(LevelFieldName, LevelFieldMarshalFunc(level))` (`marshalSpec`; `Str` through its statement,
  passed by `HypsHoldLinked.lean` from `Event.Str.wp_proof`). The level methods' statements are unchanged;
  each takes `Event.Str.spec eventTok` as a callee hypothesis.

## Remaining (7), statements unchanged

- `Event.{Int,Ints,Int64,Uint32,Bool,Float64}.wp_proof`: blocked by Perennial (`strconv.AppendInt`,
  `AppendUint`, `AppendBool`, `AppendFloat` are names only; `notes/perennial-changes.md`, 2026-11-26).
- `Event.Msg.wp_proof`: blocked by Perennial (writes to `ioutil.Discard`, whose `Write` `io.isInit` hides).

What to attack: whether the seven event axioms are true real-zerolog facts **over the defined
`eventTok`** — in particular that no field method or `Msg` needs more of the event than the definition
holds (the level methods' proofs show the definition is what a `New(nil)` logger's events satisfy, so a
too-strong token would have failed there), and that a client cannot build the token for an event the real
methods mishandle (the definition is now public: any owned `Event` with those fields has it), and that a `nil` event (a disabled
level: `GlobalLevel()` above the level, which `SetGlobalLevel` can now set to anything) is handled by
every method (`Str`..`Msg` return at once on `nil`).
