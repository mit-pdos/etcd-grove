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

## `wp_apply (lem with "H") as "pat"` fails if `lem` has a pure premise

Any `Axiom`/`Lemma` written `P → {{{ ... }}} e {{{ ... }}}` leaves the `P`
goal *first*, and `as "pat"` is applied to that goal, so you get

    Error: Tactic failure: iIntro: nothing to introduce.

which looks nothing like the real cause. Two fixes: pass the premise
positionally, `wp_apply (lem _ _ Hpremise with "[$H]") as "pat"`, or drop the
`as` and discharge the premise in a `{ }` block (what the `wp_Logger__logf`
call sites in `election.v` do). Note `Local Ltac wp_log` in `election.v` uses
the broken form and has never been called; don't reach for it.

## `wp_apply ... as` already runs `wp_auto`, so a following `wp_auto` errors

After `wp_apply (lem with "[$H]") as "H"` the goal has been advanced past the
call *and* the straight-line code after it, so an explicit `wp_auto.` next
fails with `Failed to progress.` Only put `wp_auto` where something actually
blocked it — after `iDestruct`/`iAssert`, or after the
`wp_slice_literal; iSplitR; iIntros` dance.

## `iFrame "%"` closes pure goals by assumption, not by computation

Re-sealing `own_raft_phys` after a run of field writes leaves pure goals like
`(rv <| state' := W64 0 |>).(raft.raft.state') = StateFollower`. `iFrame "%"`
does not close those — it matches hypotheses, and there is no hypothesis to
match — so they are left over and `Qed.` reports "remaining open goals" with
no error pointing at the real line. Finish with
`iPureIntro. split_and!; done.` after the `iFrame`, which handles both the
by-computation and the by-assumption conjuncts. (This is also why a leftover
count of 1 vs 2 changes which tactic works: `iPureIntro; reflexivity` is
enough for one goal and wrong for two.)

## `make x.vos` does not check proof bodies

`.vos` compiles statements, signatures and module structure and **skips
opaque proofs**, so it will happily accept a proof script that does not run.
It is a fine 2-second inner loop; it is not a check. Use `make x.vok` for the
real one (~60s for one raft function).

Do not reach for `make x.vo` instead: nothing in this tree has `.vo`
dependencies, so that starts building all of Perennial. See
`CONTRIBUTING.md:57-63`.

Corollary: `Print Assumptions` over a `.vos` tree **under-reports**. It sees
axioms reachable from *statements*, but not what an opaque proof used, so
`Admitted` lemmas and `wp_*` axioms consumed inside proofs simply do not
appear. It is not a usable cross-check on the trust base; `./etc/tcb-view.py`
is, textually.

## `Collection W` is section-scoped but the `Set` naming it is not

`Set Default Proof Using "W"` survives `End <section>` while the collection
`W` itself does not, so the next lemma fails with `Unknown variable: W`. And
for a lemma whose type is *closed* (the `wp_<fn>_body` shape), forcing W's
variables in would add binders its signature does not have, so the module
ascription then fails with `Signature components for field ... do not match`.
Restore the prelude default with `Set Default Proof Using "Type".` after the
section — `new/proof/go_etcd_io/raft/v3_proof/election/proof_raft__Step.v`
does exactly this.
## Implicit arguments are not inferred through a folded `_body`

Rocq works out implicit arguments from the *syntactic* form of a constant's
declared type. When the type is a folded definition — the
`Parameter wp_<fn> : wp_<fn>_body` shape used throughout
`v3_proof/election/` — there are no visible binders, so **every** argument
comes out explicit, whatever the `_body` says. A call site then fails with
something that looks unrelated:

    The term "MsgVote" has type "w32" while it is expected to have
    type "ffi_syntax"

Fix: one line per `link_*.v`, after the functor application,

    Arguments <Fn>.wp_<fn> {_ _ _ _ _ _ _ _}.

using the short prefix form — it marks the eight context binders implicit and
leaves each function's own binders explicit, so it needs no adjusting per
function. Do not delete these lines; they are load-bearing.

Putting the `Arguments` inside the `Module Type` instead is *accepted* and
works for a directly-ascribed module, but does **not** survive functor
application, which is why it lives in the link file.
