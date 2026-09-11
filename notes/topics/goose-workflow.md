# Goose workflow: Go source → Rocq model

Accurate as of 2026-09-11.

## The pipeline

The Go code being verified is in separate repos. Goose translates it; the
output is **committed here** so that building the proofs needs neither Go nor
the etcd sources.

```
upamanyus/etcd-raft  (branch goose)  ──┐
upamanyus/etcd       (branch goose)  ──┤
goose-lang/std, goose-lang/primitive ──┼─→ new/etc/update-goose-new.py
upamanyus/marshal    (upamanyus-fixes)─┤       (runs goose/, proofgen)
mit-pdos/go-liveness                 ──┘                 │
                                                          ↓
                          new/code/go_etcd_io/...      (models)
                          new/generatedproof/...       (boilerplate proofs)
```

`new/etc/update-goose-new.py` holds the per-project package lists — exactly
which Go packages get translated, and which are only axiomatized. For etcd that
list is long and deliberate (look at the `create_proj(repo="upamanyus/etcd",
...)` entry: `apply`, `traceutil`, `backend`, `schema` and friends are marked
"Axiomatized for etcdserver").

`etc/ci-goose-check.py` clones every project at a pinned branch, re-runs the
translation, and does `git diff --exit-code`. That is the CI `check-goose` job:
**the committed output must match what the translator produces.**

## Changing the Go code being verified

1. Commit the Go change to the `goose` branch of `upamanyus/etcd-raft` or
   `upamanyus/etcd` and push it.
2. Here, re-run `new/etc/update-goose-new.py` (see `--help`; `etc/ci-goose-check.py`
   shows the flags CI passes, including `--compile`, `--std-lib`, `--models`
   and the per-project paths).
3. Commit the regenerated `new/code/` and `new/generatedproof/` diff.

Step 3 is not optional — skipping it fails `check-goose`.

## Adding a new etcd package to the translation

Add it to the relevant `pkgs` list in `new/etc/update-goose-new.py`,
regenerate, then add `IsPkgInit` instances in the corresponding `*_proof/base.v`
(for raft: `new/proof/go_etcd_io/raft/v3_proof/base.v`). Without the instance,
proofs about the package will not typecheck.

## Path mangling

Goose maps a Go import path to a directory by replacing `.` and `/` with `_`
and `/` respectively: `go.etcd.io/raft/v3` → `go_etcd_io/raft/v3`. The Rocq
logical name is `New.code.go_etcd_io.raft.v3`. So you can always find the model
of a Go package from its import path, and vice versa.

`goose/util/util.go` carries a small table of import-path overrides (e.g.
`github.com/mit-pdos/gokv/grove_ffi` → `grove`).
