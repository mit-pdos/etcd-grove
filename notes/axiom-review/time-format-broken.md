# `time.Time.Format.wp_proofBroken`: the WAL's timestamp (2026-11-22)

The `axiom` skill, run by the author of the axiom (wal-safe session 11), at the user's request. Not an
independent review: a second reader should look again.

## The axiom

`Proof/time/Time__FormatBroken.lean`, `axiom time.Time.Format.wp_proofBroken : time.Time.Format.specBroken`
(`Spec/time/Time__FormatBroken.lean`), branch `wal-safe`:

    def timeStampOk (s : GoString) : Prop := (47 : w8) ∉ s ∧ (0 : w8) ∉ s

    abbrev time.Time.Format.specBroken : Prop :=
      ∀ (t : time.Time),
      {{ True }}
        (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #(go!"20060102.150405.999999")))
      {{ (s : GoString), RET #s; ⌜timeStampOk s⌝ }}

Claims, in plain words: at that one layout, for every `Time` value, `Format` (1) does not panic, (2) returns
a string, (3) with no `/` byte and no NUL byte, (4) owns and changes nothing the program sees (pre `True`, the
frame kept).

Until 2026-11-22 the same triple with a stronger post (every byte a digit, `.` or `-`) was a hypothesis of
`cleanupWAL`'s proof and of the WAL and tester Links (`time.Time.Format.specBroken`; ledger 2026-11-14). The
user approved replacing it with a minimal axiom. What the WAL uses of the result is exactly (3):
`brokenName_nameOk` (`Proof/.../storage/wal/BrokenName.lean`) needs `w.dir + ".broken." + s` to be a name in
the WAL's area (`NameOk`: no `/`, no NUL, not empty, `.` or `..`, the last three from the prefix), so that the
cleanup's `os.Rename` is a rename within one directory. The statement was weakened to that (ledger
2026-11-22). Its only caller is `wal.WAL.cleanupWAL` (S/wal.go, fork `goose-lean-walfs2`):
`fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format("20060102.150405.999999"))`.

## Verdict: survives

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
| 8 | the arbitrary `t` | Could a `Time` value the model allows be one Go cannot make? | `Time`'s fields are unexported; a Go program outside `time` gets a `Time` only from `time`'s API (zero value, `Now`, `Unix`, `Date`, `In`, arithmetic), each a well-formed `Time`. With `unsafe`, out of scope (Goose does not translate it). |
| 9 | cross-world | The axiom is a triple with a pure post about the returned string only; no entailment, no persistent cell | Not applicable |

Not tried: a data race on `*time.Local` (a program assigning `*time.Local = …` while `Format` reads it: a race
Go reports, not a panic; and `time.Local` is names-only in Perennial, so no translated program can write it).

## Reach

`etc/tcb-collections/wal-fsext.txt` (the WAL `Link`'s results through `wal.Create`/`cleanupWAL`) and the
tester's `etcd_wal_crash_safety_bounded`; `etc/tcb-baseline.txt` (edited by hand, 2026-11-22: no
`etc/tcb-report.py --check --update` run in the session).
