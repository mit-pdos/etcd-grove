# Gotchas

Traps that have already cost time. Add to this whenever something
non-obvious bites you — one entry, what happened, what to do instead.

Keep entries short. If an entry grows past a paragraph it probably wants to be
its own topic file in `notes/`, with a pointer from here.

---

## `new/code/` and `new/generatedproof/` are generated

Editing them appears to work, then CI's `check-goose` job fails because
`etc/ci-goose-check.py` re-translates the Go sources and diffs the tree. A
change you want in `new/code/` has to be made in the Go fork
(`upamanyus/etcd-raft` or `upamanyus/etcd`, branch `goose`) and then
regenerated with `new/etc/update-goose-new.py`.

Corollary: don't copy proof style from `new/generatedproof/` — it is
machine-written and not idiomatic.

## A proof not reachable from `new/should_build.v` is not built

`make ci` builds `new/should_build.vo`. New files compile fine locally and then
silently rot, because nothing requires them. Add the `Require` when you add the
file.

## `rocq-warm` refuses a `vos`-only tree unless you pass `--allow-stale`

[rocq-warm](https://github.com/zeldovich/rocq-warm) keeps a `rocq repl` warm
and replays only from the edited sentence onward, which suits the inner loop
here: `readonly.v` is 98s cold and 0.0s on an unchanged re-check.

Its staleness check is make's rule over `.vo` files, but the normal loop in
this repo is `make vos`, which writes no `.vo` at all. So every dependency
reports "has not been built" and a plain check exits 2. Rocq itself is happy —
`Require` falls back to `.vos` — so the fix is to tell rocq-warm to proceed:

    rocq-warm check new/proof/go_etcd_io/raft/v3_proof/readonly.v --allow-stale

It reads `_RocqProject` (it looks for both names), so the load path is right
with no extra flags, and it uses whatever `rocq` your shell resolves — activate
the opam switch first, as for a raw `coqc`. `--allow-stale` is unnecessary
after a full `make`. It never writes a `.vo` unless you pass `--compile`, so it
checks one file; it does not replace `make` for anything that requires it.

## Go sources live in other repos

`go_etcd_io/...` paths in `new/code/` come from Goose translating the Go import
path; there is no etcd Go source in this repo. To read the code being verified,
look at the `goose` branch of `upamanyus/etcd-raft` / `upamanyus/etcd`, not at
upstream `etcd-io/etcd` — the forks carry Goose-compatibility changes.

## Editors need the flake or an opam switch

Dependencies are pinned via opam `pin-depends`; a plain `rocq` on `PATH` will
be the wrong version. Either `nix develop` (or `.envrc` with `use flake`) or
`opam pin add -n . && opam install --deps-only ./perennial.opam`. Re-run the
opam command after any `git pull` that touches `perennial.opam`.
