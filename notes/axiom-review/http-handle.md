# `http.Handle_ok` with `http.NewServeMux_ok` (axiom review, 2026-11-07)

**Reviewed** (branch `sweep-atkC` at lean `ad87892323`): the axioms `http.NewServeMux_ok` and
`http.Handle_ok` (`Proof/net/http/Axioms.lean:148-152`), their statements `NewServeMux_spec` and
`Handle_spec` (`Proof/net/http/Boundary.lean:884-896`):

    NewServeMux_spec : ⊢ {{ True }} @! http.NewServeMux #() {{ (m : Loc), RET #m; muxOwn m [] }}
    Handle_spec : ∀ m regs pat h,
      ⊢ {{ muxOwn m regs ∗ ⌜pat ∉ regs.map Prod.fst⌝ }}
          (m @!! *ServeMux @!! "Handle") #pat #h
        {{ RET #(); muxOwn m (regs ++ [(pat, h)]) }}

Used by `rafthttp.Transport.Handler` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/
TransportHandler.lean:349-372`); reach per the sweep-plan review: 6 `_safe` roots, 26 roots in all
(not re-measured: this worktree has no build).

Go: `net/http` of `GOTOOLCHAIN=go1.27.3` (`src/net/http/server.go:2975-3020`).

## Verdict

**Refuted (Go side); Lean side not yet built.** `Handle_spec`'s only premise is that `pat` is not
a registered pattern string; it constrains neither the pattern's form nor the handler, and it
treats distinct strings as non-conflicting. Go's `ServeMux.register` panics
(`server.go:2976-2977`, on any `registerErr`):

- on the empty pattern (`:2982-2983`, "http: invalid pattern");
- on a nil handler, or a nil `HandlerFunc` (`:2985-2990`, "http: nil handler");
- on a pattern that does not parse (`:2992-2995`, e.g. `"b"`: "host/path missing /");
- on a pattern that conflicts with a registered one, though the strings differ (`:3009-3018`,
  `"/{x}"` then `"/{y}"`).

## The program

`examples/axiomcx/http-handle/http-handle.go`:

    func Main() {
        m := http.NewServeMux()
        m.Handle("", nil)
    }

with `NilHandler` (`"/a"`, nil), `Unparsable(h)` (`"b"`, non-nil `h`) and `Conflict(h)` (`"/{x}"`,
`"/{y}"`, non-nil `h`) as the other three cases.

Test (`go test ./axiomcx/http-handle/ -run . -count=1 -v`, go1.27.3):

    === RUN   TestMainPanics
        http-handle_test.go:21: Main panicked: http: invalid pattern
    --- PASS: TestMainPanics (0.00s)
    === RUN   TestNilHandlerPanics
        http-handle_test.go:21: NilHandler panicked: http: nil handler
    --- PASS: TestNilHandlerPanics (0.00s)
    === RUN   TestUnparsablePanics
        http-handle_test.go:21: Unparsable panicked: parsing "b": at offset 0: host/path missing /
    --- PASS: TestUnparsablePanics (0.00s)
    === RUN   TestConflictPanics
        http-handle_test.go:21: Conflict panicked: pattern "/{y}" (registered at .../http-handle.go:35) conflicts with pattern "/{x}" (registered at .../http-handle.go:34):
            /{y} matches the same requests as /{x}
    --- PASS: TestConflictPanics (0.00s)
    PASS

## Why the premises hold, and the proof (not yet built)

The theorem: `{{ isPkgInit pkg_id.<httphandle> }} @! httphandle.Main #() {{ RET #(); True }}`,
from `NewServeMux_spec` and `Handle_spec` as hypotheses.

- `NewServeMux_spec`'s precondition is `True`, and it asks no `isPkgInit` of `net/http`:
  `wp_apply hNSM as %m Hm` gives `muxOwn m []`.
- `Handle_spec` at `regs := []`, `pat := ""`, `h := ` the nil interface (Goose's conversion of
  `nil` to `http.Handler`): the premise `"" ∉ []` is `by simp`; `muxOwn m []` is framed. Its
  postcondition `muxOwn m [("", nil)]` is dropped (`True`).
- The call shape is the one `TransportHandler.lean:355-357` already applies `Handle_ok` to (`wp_apply
  hHdl $$ [$Hm]` after `wp_auto` on the method call), so the same steps apply here.
- `#print axioms` of the corollary should list `http.NewServeMux_ok`, `http.Handle_ok` and the
  generic ones; nothing else is called.

Where it could get stuck: only Goose's translation of the untyped `nil` argument (the value `h`
must be a literal the spec's `∀ h` instantiates with, which it is: the spec quantifies over every
`GoInterface`). If that ever needs care, `Conflict`'s two distinct patterns `"/{x}"`, `"/{y}"` with
any handler parameter refute the same axiom (`"/{y}" ∉ ["/{x}"]`).

## Proposed restatement (not applied)

Premises on `Handle`: `h = GoInterface.ok hi` with `hi` not a nil `HandlerFunc`; `pat` in the
form the callers use (a non-empty literal path starting with `/`, no `{`, `}`, space or method
prefix, which `parsePattern` accepts), and, for such literal patterns, distinct strings never
conflict, so `pat ∉ regs.map Prod.fst` then suffices. rafthttp's four patterns (`/raft`,
`/raft/stream/`, `/raft/snapshot`, `/raft/probing`) and its non-nil handlers meet it.
