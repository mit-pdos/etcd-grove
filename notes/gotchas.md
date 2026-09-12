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

## `rocq-warm` needs `--allow-stale` if you build with `vos`

[rocq-warm](https://github.com/zeldovich/rocq-warm) keeps a `rocq repl` warm
so a tactic edit near the end of a big file re-checks only from the edit
onwards — seconds instead of minutes. But it decides staleness the way `make`
does, on `.vo` files, so against a `make vos` tree it refuses every check
("N dependencies are stale"). Pass `--allow-stale`; it then loads the `.vos`
files and works fine. Also raise `ROCQ_WARM_MAX_SESSION_GB` (the default
ceiling is small enough that a Perennial session gets evicted mid-edit), and
note that `--show-output` — which you need to see a `Show.` — discards the
warm session, so a goal inspection costs a cold check.

## `word` does not reliably close `W32 a ≠ W32 b`

It sometimes fails with "Cannot find witness" on goals as simple as
`W32 5 = W32 0 → False`, in contexts where the same shape works elsewhere.
Use instead:
`intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.`
(`w32_ne` in `new/proof/go_etcd_io/raft/v3_proof/election.v`.)

## `wp_slice_literal` leaves the slice length unreduced

After `wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hsl _]".`
the slice's `len`/`cap` are `W64 (go.array_literal_size [...])` and its
contents are `<[sint.nat (W64 0) := x]> [zero_val]`. `wp_auto` cannot step
past that, and `wp_slice_append` will not apply. Normalize first, exactly as
`readonly.v:580` does:

```coq
replace (sint.nat (W64 0)) with 0%nat by done.
rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
```
