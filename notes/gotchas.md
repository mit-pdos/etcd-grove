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

Use the **[upamanyus fork](https://github.com/upamanyus/rocq-warm)**, not
`zeldovich/rocq-warm` — see below for what it fixes. It keeps a `rocq repl`
warm so a tactic edit near the end of a big file re-checks only from the edit
onwards — seconds instead of minutes. But it decides staleness the way `make`
does, on `.vo` files, so against a `make vos` tree it refuses every check
("N dependencies are stale"). Pass `--allow-stale`; it then loads the `.vos`
files and works fine. Also raise `ROCQ_WARM_MAX_SESSION_GB` (the default
ceiling is small enough that a Perennial session gets evicted mid-edit).

Three things the fork fixes, all of which bit here:

- **A `Show.` no longer costs a cold check.** Upstream needed
  `--show-output` to print what a proof printed, and that flag discarded the
  warm session — so inspecting a goal cost a full cold replay. The fork
  prints whatever the sentences it executed printed, with no flag and no
  fresh session, so adding a `Show.` and re-checking is an ordinary replay.
  It also stopped reading a bare `Show.` as a syntax error.
- **Concurrent checks are safe.** One session slot per file: different files
  check in parallel (the case that matters when several agents or terminals
  share this checkout), and a second check of the *same* file is refused with
  exit 2 rather than racing two multi-GB sessions against one question.
- **`Time` and `idtac` output** is pinned against `coqc` per Rocq version.

Remember that **exit 2 is not a verdict** — it means the file could not be
checked (stale dependency, already being checked, no daemon, no `rocq`). Only
0 and 1 say anything about the proof.

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
## The ambient binders of a `wp_<fn>_body`

This is the single write-up of how `v3_proof/election/`'s closed-`_body` shape
handles the binders every spec opens with (`ext ffi ffi_interp0 Σ hG
ffi_semantics0 sem package_sem`). The files themselves do not repeat it.

**Implicit arguments.** Rocq works out implicits from the *syntactic* form of a
constant's declared type. When the type is a folded definition — the
`Parameter wp_<fn> : wp_<fn>_body` shape — there are no visible binders, so
every argument comes out explicit whatever the `_body` says, and a direct
application fails with something that looks unrelated:

    The term "MsgVote" has type "w32" while it is expected to have
    type "ffi_syntax"

Declare them **in the signature**, right after the `Parameter`:

    Arguments wp_<fn> {_ _ _ _ _ _ _ _}.

This propagates to every implementing module, **functor application
included** (verified against the real environment; an earlier note here
claimed otherwise and was wrong — it was a `grep` artifact, the
`Arguments …` line wraps across three lines). The short prefix form marks the
ambient binders implicit and leaves each function's own binders explicit, so
it needs no adjustment per function.

Scope note: nothing in the tree currently *needs* these lines. Every call site
goes through `wp_apply (P.wp_<fn> with "…")`, which unifies the arguments
itself and never passes them positionally; deleting an `Arguments` line does
not break the build. They are there so the specs behave like every other
Perennial spec for a caller that does apply them directly, and so `About` and
error messages stay readable.

**Introducing them in a proof.** Use `intros_ambient` (`election/defs.v`). It
is the one place the list is written; if the ambient set changes, that is the
line to fix. The obvious alternatives are all wrong:

- `intros ?????? sem package_sem …` — positional. This shipped as a bug
  twice: `Step` and `Step_MsgVote` had an extra `bytes_sem`, it was omitted,
  every later name shifted by one, and the failure surfaced ~20 lines later as
  `iIntro: could not introduce "Hpre", goal is not a wand or implication`.
- bare `intros` — does use the declared binder names, so nothing is *missed*,
  but it runs on past the function's own parameters into the premise
  (auto-named `H`) and `Φ`. `wp_start_folded`
  (`new/golang/theory/auto.v:40-58`) does `iIntros (Φ) "Hpre HΦ"`, so it needs
  the `∀ Φ` intact.
- `intros *` — stops at the first non-dependent product, which is right for a
  spec with a premise and swallows `Φ` for one without (`becomeFollower`).
- `intros until package_sem` — looks robust, **is not**. A binder that does not
  occur in the rest of the statement loses its name: Rocq degrades
  `∀ (x : T), body` to `T → body`. `package_sem` happens to occur in
  `becomeLeader`'s statement but not in `voteRespMsgType`'s, where the same
  tactic fails with `No quantified hypothesis named package_sem in current
  goal even after head-reduction`. Whether it works is per-spec accident.

Also rejected: making `_body` a `Notation` so it expands syntactically and the
implicits are inferred. It does not work — the generalized binders still come
out explicit.

**`bytes_sem` is not needed.** `raft.Assumptions` has
`#[global] import_bytes_Assumption :: bytes.Assumptions`
(`new/code/go_etcd_io/raft/v3.v`), so `bytes.Assumptions` resolves from
`package_sem` as `package_sem.(raft.import_bytes_Assumption)`. A separate
`bytes_sem` binder is redundant; `package_sem` is the last ambient binder in
every spec.

## stdpp renamed `elem_of_list_lookup_*` to `list_elem_of_lookup_*`

`eapply elem_of_list_lookup_2` fails with

    The variable elem_of_list_lookup_2 was not found in the current environment

which reads like a missing `Require` and is not. The current name is
`list_elem_of_lookup_2` (likewise `list_elem_of_lookup` and
`list_elem_of_lookup_1`). Grepping the stdpp sources for the old name finds
nothing, which is the confusing part.

To settle a name like this in about a minute, compile a scratch file with the
project's load path instead of guessing:

    $ cat /tmp/probe.v
    From stdpp Require Import list.
    Search (_ ∈ _) (_ !! _ = Some _).
    $ coqc -Q src Perennial -Q new New -w -unknown-warning /tmp/probe.v

(The `rocq` binaries are in the `perennial` opam switch: put
`$HOME/.opam/perennial/bin` on `PATH`.)

## `wp_apply … as` runs `wp_auto`, so don't re-seal around a call whose continuation reads fields

`wp_apply (lemma with "[$Hphys]") as "Hphys"` steps the program on *after* the
call returns. If you sealed `own_raft_phys` to make the call, `wp_auto` then
cannot step through it, because the field points-tos are hidden inside.

The symptom is not at the `wp_apply` — it is a *later* tactic failing, e.g.
`wp_apply wp_slice_literal` reporting `iApply: cannot apply (WP
CompositeLiteral …)`, which points at the wrong line entirely.

Unpack and step explicitly:

    wp_apply (wp_raft__appendEmptyEntry with "[$Hphys]") as "Hphys".
    iNamedSuffix "Hphys" "2".
    wp_auto.

See `proof_raft__becomeLeader.v`.

## `make x.vok` leaves no stamp file, so it never skips and never goes stale

`find . -name '*.vok'` comes back empty even right after a successful run: the
rule passes `-o $@` but `-vok` mode writes nothing. Two consequences, one good
and one to plan around:

- **It is always a real check.** `make x.vok` cannot report "up to date" on a
  stale result, unlike `.vos`. If it prints `ROCQ COMPILE -vok …` and exits
  quiet, the proof bodies ran.
- **It re-runs every time**, ~100s per function here. Don't put a broad `.vok`
  sweep in a tight loop; check the one file you touched, and do the full sweep
  once at the end.

## Getting one struct field out of `r ↦ rv`: use `access_strict`, and pin the load instance

`RecordVote`/`TallyVotes` want the tracker's *location*, which a caller
holding the whole raft struct has to split out. The generated `AccessStrict`
instances (`new/generatedproof/go_etcd_io/raft/v3.v`, e.g.
`raft_access_load_trk` / `raft_access_store_trk`) are the way:

```coq
iDestruct (access_strict
             (A := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
             (A' := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
             (P := r ↦ rv) (P' := r ↦ rv)
             with "Hr") as "[Htrkf Hrback]".
...
iDestruct ("Hrback" with "Htrkf") as "Hr".
```

**The `(P := …) (P' := …)` are load-bearing.** With `A = A'` the *store*
instance also unifies, and it hands back `r ↦ rv <| trk' := rv.(trk') |>` —
a no-op record update that is not syntactically `rv`, so re-sealing
`own_raft_phys` then fails with a leftover `"Hr" ∷ r ↦ rv` goal. Pinning `P'`
selects the load instance. For a call that genuinely *changes* the field
(`ResetVotes` replaces `Votes`), drop `P'` and give `A'` at the new value so
the store instance is chosen. (`proof_raft__poll.v`.)

## `iNamed` on an unsealed `typed_pointsto` needs the `⌜l ≠ null⌝` peeled off first

`iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr"` turns
`r ↦ rv` into `(the 33 field points-tos, named with ∷) ∗ ⌜r ≠ null⌝`. `iNamed
"Hr"` on *that* **silently does nothing** — the trailing conjunct has no name,
so the whole thing is not a named conjunction — and the failure surfaces much
later as `iSpecialize: hypotheses ["trk"] not found`. Split the pure conjunct
off first and it works:

```coq
iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".
```

Re-sealing is the mirror image: `iEval (rewrite typed_pointsto_unseal
/typed_pointsto_wrap /=)` on the *goal*, then `iFrame "∗%"`. (An earlier
version of this entry concluded the route was unusable and needed a positional
`iDestruct` naming every field; that was wrong. `proof_raft__reset.v`'s
`raft_split_trk` is the worked example.)

## The `AccessStrict` store instance cannot take a value the call has not produced yet

`raft_access_store_trk` fixes `A'` — the field's *new* value — at the moment
`access_strict` is invoked, but `trk.ResetVotes()` only names that value
(`votesRef`) in its own postcondition. Leaving `A'` as an evar therefore fails
with

    iSpecialize: cannot instantiate (…[trk] ↦ ?t -∗ r ↦ rv <|trk' := ?t|>)
    with (…[trk] ↦ tv <|Votes' := votesRef|>)

because `votesRef` is introduced *after* the evar and so is outside its
context. There is no ∀-quantified `AccessStrict`, so prove the quantified wand
yourself by unsealing — `raft_split_trk` in `proof_raft__reset.v`:

```coq
l ↦ rv -∗ l.[t,"trk"] ↦ rv.(trk') ∗
           (∀ tv, l.[t,"trk"] ↦ tv -∗ l ↦ (rv <|trk' := tv|>))
```

## `case_bool_decide` picks the first `bool_decide` it finds — including one in the Rocq context

Inside `reset`'s `Visit` closure the goal holds `#(bool_decide (i =
rv.(id')))`, but the Rocq context still holds `Hb : bool_decide (rv.(Term') =
term) = true` from the enclosing case split, and `case_bool_decide as H`
destructs *that* one — leaving the program `if` unresolved. `wp_apply` then
reports `iApply: cannot apply` at a line that looks fine. Be explicit:

```coq
assert (bool_decide (i = rv.(raft.raft.id')) = true) as Hbi
  by (apply bool_decide_eq_true_2; done).
rewrite Hbi /=. wp_auto.
```

The trailing `wp_auto` matters: the `rewrite` only turns the scrutinee into
`#true`, and `wp_apply` cannot bind a redex that is still inside an unreduced
`if`.

## Re-sealing `own_raft_phys`: frame `Hr` *before* `iFrame "∗#%"`

`iExists _, msgs, msgsAA, lok. simpl. iFrame "∗#%"` leaves the struct value an
evar, and `iFrame` cheerfully discharges `⌜?rv0.(preVote') = false⌝` from
`HnoPreVote : rv.(preVote') = false` by setting `?rv0 := rv` — the value
*before* the writes. What is left is an unprovable `"Hr" ∷ r ↦ rv`. Pin the
value first:

```coq
iExists _, msgs, msgsAA, lok. iFrame "Hr". simpl. iFrame "∗#%".
```

## The postcondition is a `∗`, so `iExists` on it fails

A spec like `poll`'s returns `own_raft_phys … ∗ ⌜_⌝ ∗ ⌜_⌝ ∗ ⌜_⌝`. After
`iApply ("HΦ" $! …)` the goal is that whole conjunction, so
`rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok` fails with
`Tactic failure: iExists: … not an existential` — and the error prints the
entire goal, which buries the one-line cause. Split first:

```coq
iSplitL "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
{ rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. simpl. iFrame "∗#%". }
iPureIntro. split_and!; done.
```

## A section-variable-carrying definition takes it explicitly *only from outside its own file*

Since `own_tracker` became a real definition mentioning `cfg`, it takes `cfg`
as a leading argument — so `inv_misc.v` writes `own_tracker cfg tv votes`.
But `own_raft_phys`, defined in `inv_raft_phys.v` with `cfg` a section
variable *of that file*, is written **without** `cfg` inside
`inv_raft_phys.v` and **with** it everywhere else (`own_raft_phys cfg r id s`).
Getting this backwards gives `The term "cfg" has type "gset w64" while it is
expected to have type "loc"` — which reads like a typo and is not.

## `step_lemmas.v` is not in scope from every `proof_*.v`

`apply step_drop` fails with "The variable step_drop was not found in the
current environment" from `proof_raft__hup.v`, because the require chain
`spec_raft__hup.v` → `inv_raft_phys.v` never reaches `step_lemmas.v`. The
`step` **constructors** (`step_refl`, `step_campaign`, …) are always
available, since they come in with `election_protocol.v` via `defs.v`; the
derived composition lemmas in `step_lemmas.v` are not. Either use the
constructor directly or check the chain first. (Found proving `hup`,
2026-09-16.)

## `apply bool_decide_eq_true_1` on the goal cannot infer its `Decision`

It fails with `Unable to find an instance for the variable Decision0`,
because the instance is unconstrained when `bool_decide` appears only in the
conclusion. Apply it to the hypothesis instead:

```coq
symmetry in Hb. apply bool_decide_eq_true_1 in Hb.
```

This is the idiom for turning `wp_raft__promotable`'s
`b = bool_decide (rv.(raft.raft.id') ∈ cfg)` into the `id ∈ cfg` that
`campaign` and `becomeLeader` require, so anything on the
`hup`/`campaign`/`stepCandidate` path needs it. (Found proving `hup`,
2026-09-16.)

## A `_POSTULATES` list can be wrong in both directions, and only one direction shows up

`postulates_stepCandidate_MsgVoteResp.v` included `SEND_VOTE`, which
`stepCandidate` never calls (its sends are inside `becomeLeader` /
`bcastAppend`, which carry their own specs), and omitted `BECOMEFOLLOWER`,
which the `quorum.VoteLost` arm needs for `r.becomeFollower(r.Term, None)`.
The missing one blocks a proof; the spurious one is silent. Corrected
2026-09-16.

To see what a functor actually has, ask rather than read the file:

```coq
Print Module Type STEPCANDIDATE_POSTULATES.
```

Adding `BECOMEFOLLOWER` there does **not** trip the "label already declared"
trap, because `postulates_raft__Step.v` includes `STEPCANDIDATE` (the spec
`Module Type`, one `Parameter`) rather than `STEPCANDIDATE_POSTULATES`.

## With several agents in one checkout, rocq-warm's stdout interleaves

Different files check in parallel (that is the point of the fork's
slot-per-file concurrency), and their output lands on one stream. Grep for
your own filename's `OK`/`FAILED` line; do not trust the tail of the output.
