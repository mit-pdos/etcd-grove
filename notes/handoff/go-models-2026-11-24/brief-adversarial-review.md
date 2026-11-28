# Adversarial review of Go models (go-model overlays S2–S7)

You are a fresh adversarial reviewer. You get a branch and a list of Go **models**: Go declarations spliced into a
real Go package in place of the real declarations (a `[model]` table in the package's goose `.toml`; model files under
`goose/model/overlay/<pkg>/` in Perennial, `models/<pkg>/` in etcd-grove), plus any **primitive stubs** (names in the
`.toml`'s `trusted` list whose Lean `.impl` in `TrustedCode/` is the model; their Go body only runs in gc builds).
Goose translates the models; they are verified like real code. The trust claim for each replaced declaration:

> every behaviour of the real declaration (gc, linux/amd64, the pinned Go), under every use by the rest of the
> program and of the real package, is a behaviour of the model's translation (model ⊇ Go). A stuck point
> (`gomodel.Stuck`, or a construct with no semantics rule) covers every behaviour. A model must never be more
> defined than Go: it must not return, or succeed, where Go panics, throws, blocks or does something else.

**Your job: find a Go program where the model and the real Go diverge in the unsafe direction** — a behaviour of the
real Go (a result value, a panic, a side effect such as a call of a user method, a write, a block, an error value or
its dynamic type, an ordering of package-variable initialization) that the model cannot produce. Also report
divergences in the other direction only if they look unintended. Treat each `MODEL:` comment's argument as a claim to
refute, not a fact.

How:
- For each model, read the model and the real source side by side (`go doc -u -src <pkg>.<Name>` with
  `PATH=/home/ubuntu/sdk/go1.26.11/bin:$PATH GOTOOLCHAIN=local` for Perennial, go1.27.3 for etcd-grove;
  `etc/trusted-delta.py` prints both for Perennial). Read the Lean `.impl` of every primitive stub it calls, and the
  GooseLang semantics where a construct's behaviour matters (Perennial/Golang/Defn, Perennial/GooseLang).
- Think about: inputs at the edges (nil, empty, huge, negative, NaN, invalid UTF-8), user types with methods
  (`String`, `Error`, `Unwrap`, `Is`), concurrency (races, a value copied while in use), panics and recover, aliasing,
  init order, what the gc body of a stub does vs its `.impl`, and every `gomodel.Choose`: does the choice really cover
  all of Go's outcomes?
- Where you suspect a divergence, demonstrate it: write a small Go program/test and run it under the real package and
  under the overlay (Perennial: `goose model-overlay -o DIR <pkgs>` then `go run/test -overlay DIR/overlay.json
  -tags goose,...`; see `etc/model-tests.sh` for the exact invocation; etcd-grove: `etc/model-tests.sh`), or argue it
  precisely from the semantics if gc can't show it (e.g. the model returns where Go's gc panics).
- Do not edit the branch. Work in /home/ubuntu/.claude-E/jobs/b20ef685/tmp/gmr-adv-<unit>/ (small files only; disk is
  tight). No GitHub comments, no pushes.

Report (final message, concise): per model, "no divergence found (what you tried)" or the divergence with the program,
the Go result vs the model's, and a suggested fix. Severity: UNSOUND (model misses a Go behaviour) / IMPRECISE (model
has extra behaviours; fine unless unintended) / DOC (comment wrong).
