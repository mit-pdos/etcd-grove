# `time.Time.Format.wp_proofBroken`: the WAL's timestamp (2026-11-22)

The `axiom` skill, run by the author of the axiom (wal-safe session 11), at the user's request; then an
independent review (2026-11-22, "Independent review" below), whose recommendation strengthened the
precondition. The statement below is the current one; the author's review was of the first, with
precondition `True`.

## The axiom

`Proof/time/Time__FormatBroken.lean`, `axiom time.Time.Format.wp_proofBroken : time.Time.Format.specBroken`
(`Spec/time/Time__FormatBroken.lean`), branch `wal-safe`:

    def timeStampOk (s : GoString) : Prop := (47 : w8) ∉ s ∧ (0 : w8) ∉ s

    abbrev time.Time.Format.specBroken : Prop :=
      ∀ (t : time.Time) (l : Loc),
      {{ globalAddr time.Local ↦□ l ∗ ⌜t.loc' = Loc.null ∨ t.loc' = l⌝ }}
        (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #(go!"20060102.150405.999999")))
      {{ (s : GoString), RET #s; ⌜timeStampOk s⌝ }}

Claims, in plain words: at that one layout, for every `Time` value whose location is `nil` (UTC) or the
value of the read-only global `time.Local`, `Format` (1) does not panic, (2) returns a string, (3) with no `/`
byte and no NUL byte, (4) owns and changes nothing the program sees (the frame kept). (Until the independent
review, for every `Time`, precondition `True`.) `cleanupWAL` calls it on `time.Now()`'s `Time`, whose location
is `Local`'s value (`time.Now.specLoc`, `Spec/time/NowLoc.lean`, proved over Perennial's translation of `Now`).

Until 2026-11-22 the same triple with a stronger post (every byte a digit, `.` or `-`) was a hypothesis of
`cleanupWAL`'s proof and of the WAL and tester Links (`time.Time.Format.specBroken`; ledger 2026-11-14). The
user approved replacing it with a minimal axiom. What the WAL uses of the result is exactly (3):
`brokenName_nameOk` (`Proof/.../storage/wal/BrokenName.lean`) needs `w.dir + ".broken." + s` to be a name in
the WAL's area (`NameOk`: no `/`, no NUL, not empty, `.` or `..`, the last three from the prefix), so that the
cleanup's `os.Rename` is a rename within one directory. The statement was weakened to that (ledger
2026-11-22). Its only caller is `wal.WAL.cleanupWAL` (S/wal.go, fork `goose-lean-walfs2`):
`fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format("20060102.150405.999999"))`.

## Verdict: survives (the author's); sound with a caveat (the independent review), fixed

## The Go code (go1.27.3, `time/format.go`)

`Format` is `appendFormat` on a 64-byte buffer. At this layout the chunks are `stdLongYear`
(`appendInt(b, year, 4)`), `stdZeroMonth`, `stdZeroDay`, the literal `.`, `stdHour` (`15`,
`appendInt(b, hour, 2)`), `stdZeroMinute`, `stdZeroSecond`, then `.999999`, `stdFracSecond9`
(`appendNano`: a `.` and up to six digits, trailing zeros and then the `.` dropped). `appendInt`
(`format.go:418`) appends `-` for a negative value, then decimal digits only (also at `MinInt`: `uint(-x)` is
`2^63`). No zone name or offset chunk is in the layout, so a `Location`'s names never reach the output. The
calendar fields come from `t.locabs()` and `absSeconds.days/clock`, total functions (division by constants,
no indexing by unbounded values). `t.loc` of `time.Now()` is `Local`; its first use runs `initLocal` under a
`sync.Once`, which reads `TZ`/`/etc/localtime` and falls back to UTC on any error.

## Attacks tried

All in `time-format-broken/fmtatk_test.go.txt` (run with `go test -race -v`, go1.27.3; output
`time-format-broken/gotest.log`). Every case returned a string of digits, `.` and `-` only; none panicked.

| # | Claim attacked | Attack | Result |
|---|---|---|---|
| 1 | (3) no `/` | A zone whose name holds `/` and NUL (`FixedZone("a/b\x00c", …)`) | The layout prints no zone: `20261122.002329.886158` |
| 2 | (1), (3) at extreme years | `Unix(MaxInt64, 999999999)`, `Unix(MinInt64, 0)`, `UnixMicro(MinInt64)`, `Date(-123456, …)`, `Date(1e9, …)`, `Add(MaxInt64)` | Digits only (`2922770265961204.153007.999999`), a leading `-` for negative years (`-00010101.000000.000001`); the year wraps at the extremes, no panic |
| 3 | (1) offsets | `FixedZone` at `MaxInt32`/`MinInt32` seconds on the extreme instants | Digits; no overflow panic |
| 4 | (1) `Location`s | the zero `&time.Location{}`, a loaded zone (`Asia/Kathmandu`), `Local` | Fine (the zero `Location` reads as UTC) |
| 5 | (1), (4) `Local`'s lazy initialization | `TZ` = `""`, `:`, `/nonexistent`, `:/etc/passwd`, `../../../../etc/passwd`, `UTC-99:99/x`, `a/b`, `\x01`, a POSIX rule, `<+0330>-3:30`, 100000 bytes, `Europe/Paris` (a child process each) | `initLocal` falls back to UTC or parses; no panic; output digits |
| 6 | (1) a malformed zone file | `ZONEINFO` pointing at a garbage and an empty `TZif` file | Fallback to UTC, no panic |
| 7 | (4) hidden effects | Code reading: `initLocal` writes `localLoc` (private to `time`, under its `Once`) and opens a zone file read-only | Nothing a translated program can observe: `time`'s state is not modelled, and the file is read-only (no `fsExt` tree change) |
| 8 | the arbitrary `t` | Could a `Time` value the model allows be one Go cannot make? | Yes, and harmless. `Time`'s fields are unexported; a Go program outside `time` gets a `Time` only from `time`'s API, and in the model only from the sources with specs: the zero value, `Now`, `Unix` and arithmetic (`Add`, ...); `Date` and `In` are not sources in the model (no spec). But the model's `Now` is over `runtimeNow`'s trusted model, which returns an arbitrary `int32` `nsec`, so it builds `wall` bit patterns Go's `Now` never makes (an `nsec` field of `1e9` or more). `Format` handles all of them: the independent review's `TestArbitraryBits` formats every `(wall, ext)` edge pattern and 200000 random ones, at `loc` `nil`, `Local`, `UTC`, a fixed zone and a real zone, digits, `.` and `-` only. |
| 9 | cross-world | The axiom is a triple with a pure post about the returned string only; no entailment, no persistent cell | Not applicable |

Not tried by the author: a data race on the `Location` `Format` reads. The first version of this note said a
race on `*time.Local` is "a race Go reports, not a panic" and that `time.Local` is names-only in Perennial; both
were wrong (the independent review, below):

- **The race panics.** `TestRacyLocal` (a goroutine assigning `*time.Local = *ny` and `*time.Local = *fz` in a loop
  while `time.Unix(-600000000, 0).Format(layout)` runs) panics, `index out of range [2] with length 1` in
  `time.(*Location).lookup` (`zoneinfo.go:200`): the `Location` is torn, a `tx` slice from one value and a `zone`
  slice from the other. `TestRacyLocation` does the same with a `Location` of the program's own
  (`time.Date(1950, ..., loc)`). Both rerun 2026-11-22, go1.27.3, without `-race`: both panic.
- **`time.Local` is translated.** `time.Local`, `localLoc`, `UTC` and `utcLoc` are translated in Perennial
  (`Code/time.toml`'s `translate` list), with bodies, not names-only. No program can write the `Location` they point
  to because `time`'s initializer (`time.initialize'.wp_proof`) makes `Local` and `UTC` read-only (`ipersist`: `isInit`
  holds `globalAddr time.Local ↦□ l`) and discards the points-to of `localLoc` and `utcLoc`.

So with precondition `True` the axiom was sound only because no model program could reach a `Time` whose
`Location` it can write: true today (the only sources, `Now`, `Unix`, the zero value, give `Local` or `nil`), but
a fact outside the statement, which a future spec of `In`, `Date`, `FixedZone` or `LoadLocation` would break
silently. The precondition now states it (the spec's header; ledger 2026-11-22).

## Reach

`etc/tcb-collections/wal-fsext.txt` (the WAL `Link`'s results through `wal.Create`/`cleanupWAL`) and the
tester's `etcd_wal_crash_safety_bounded`; `etc/tcb-baseline.txt` (edited by hand, 2026-11-22: no
`etc/tcb-report.py --check --update` run in the session).

## Independent review (2026-11-22)

Reviewer: an independent agent of the coordinator's session (coord-03), not the axiom's author, 2026-11-22.
Report and tests: `/shared/tmp/coord-03/review-timefmt/`, copied here as
`time-format-broken/review_fmt_test.go.txt` (`TestArbitraryBits`, `TestModelConstructors`, `TestTZ`,
`TestRacyLocation`), `time-format-broken/review_local_test.go.txt` (`TestRacyLocal`) and
`time-format-broken/review-run-tz.sh.txt` (`TestTZ` under assorted `TZ`, and every zone file).

**Verdict: sound, with a caveat.** No model program could make the axiom's triple false: every `Time` a
model program can build points to `Local`'s or `UTC`'s `Location` (or `nil`), which nothing can write, and
`Format` handles every `wall`/`ext` bit pattern (row 8) and every `TZ` (row 5). The caveat: the
precondition `True` claims more, for any `t`; in real Go a racing write to the `Location` makes `Format`
panic (`TestRacyLocal`, `TestRacyLocation`), so the axiom's soundness rested on a fact the statement did not
state. Recommendation: require the read-only `Local` in the precondition.

**Done** (wal-safe, 2026-11-22): precondition `globalAddr time.Local ↦□ l ∗ ⌜t.loc' = Loc.null ∨ t.loc' = l⌝`;
`cleanupWAL` discharges it with `time.Now.specLoc` (proved); the spec's header says why the `Location` must be
read-only; this note corrected (rows 8, "Not tried").
