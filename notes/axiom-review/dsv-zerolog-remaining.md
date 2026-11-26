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
- **`eventTok`** (`EventTok.lean`) is still **opaque** (no law). Defining it changes what all thirteen
  remaining axioms claim, so it is left for the session that proves the level methods and `Str` over a
  definition (the planned one: `e = null`, or `e ↦` an `Event` whose buffer is owned and non-empty, its
  writer `newLevelWriter w` of `Discard`'s value, `done`/`ch` nil, `stack` false, level one of the five);
  this review must then be redone over it.

## Retired (proved from the translation; statements unchanged)

- `New.wp_proof` (`New.lean`), from `wp_New_nil` and the fact's `Discard`.
- `SetGlobalLevel.wp_proof` (`SetGlobalLevel.lean`): the atomic store through the fact's invariant.
- `ParseLevel.wp_proofWarn` (`ParseLevel.lean`): the switch through `marshalSpec`; `fmt.Errorf` (after
  the switch) is not reached on `"warn"`.
- (session 3) zerolog's and `internal/json`'s `wp_initialize'`.

## Remaining (13), statements unchanged

- `Logger.{Trace,Debug,Info,Warn,Error}.wp_proof` (`Logger__*.lean`):
  `{{ isPkgInit zerolog ∗ l ↦{dq} lg ∗ loggerOk lg }} l.M() {{ (e : Loc), RET #e; l ↦{dq} lg ∗ eventTok e }}`.
  The precondition is now concrete and narrower (`lg = newLogger w`: level Trace, no sampler, no context,
  no stack, so `newEvent` reads `GlobalLevel()`, takes an event from `eventPool` and calls
  `e.Str(LevelFieldName, LevelFieldMarshalFunc(level))`); the post is over the opaque `eventTok`.
  Provable over a defined `eventTok` once `Event.Str` is (next step).
- `Event.Str.wp_proof`: `{{ isPkgInit ∗ eventTok e }} e.Str(k, x) {{ RET #e; eventTok e }}`. Provable:
  `AppendKey` (reads `dst[len(dst)-1]`: needs the buffer non-empty, the `eventTok` definition's job) and
  `internal/json`'s `AppendString` (`noEscapeTable`, the fact's `↦□`; `appendStringComplex`'s loop over
  Perennial's `utf8.DecodeRuneInString`).
- `Event.{Int,Ints,Int64,Uint32,Bool,Float64}.wp_proof`: blocked by Perennial (`strconv.AppendInt`,
  `AppendUint`, `AppendBool`, `AppendFloat` are names only; `notes/perennial-changes.md`, 2026-11-26).
- `Event.Msg.wp_proof`: blocked by Perennial (writes to `ioutil.Discard`, whose `Write` `io.isInit` hides).

What to attack: whether the five level axioms and the eight event axioms are still true real-zerolog
facts **for every `eventTok` a later definition could give** — in particular that no field method
or `Msg` needs more of the event than the planned definition holds, and that a `nil` event (a disabled
level: `GlobalLevel()` above the level, which `SetGlobalLevel` can now set to anything) is handled by
every method (`Str`..`Msg` return at once on `nil`).
