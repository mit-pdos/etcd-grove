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
appear. It is not a usable cross-check on the trust base.

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

## A `Qed.` in the file is not a proof — only `make <file>.vok` is

On 2026-09-16 `proof_raft__Step.v`'s `wp_Step_MsgVote` sat in the tree ending
in `Qed.`, looking finished, while `make <file>.vok` failed inside it with
`Tactic failure: iApply: cannot apply`. It was reported as proved on the
strength of *reading* the file. It was not proved.

This is the `.vos` trap wearing a different hat: `.vos` skips opaque proofs,
so the file compiles at `.vos`, the `Qed.` is never executed, and nothing
objects. Grepping for `Admitted` therefore does **not** measure what is
proved — a broken script with `Qed.` at the end counts as clean.

Two rules:

- Never claim a lemma is proved without having seen `make <file>.vok` exit 0
  on that exact revision.
- When several agents share a checkout, a `.vok` run can race a live edit and
  fail on a transient state. Stop the writer first, then re-check, before
  concluding anything about the proof.

## `until ! pgrep -f "make -jN"` never terminates — it matches itself

A wait loop written to poll for a build finishing:

```sh
until ! pgrep -f "make -j4" >/dev/null; do sleep 20; done
```

spins forever, because the waiting shell's own command line *contains* the
string `make -j4`, so `pgrep -f` matches the poller itself. On 2026-09-16 this
left eighteen orphaned shells behind, each sleeping and re-matching.

Match on something that cannot appear in the poller, or check for the real
thing instead:

```sh
until [ -f .build-done ]; do sleep 20; done          # a sentinel file
until ! pgrep -x rocqc.py >/dev/null; do sleep 20; done   # -x, exact name
```

Better still, do not poll: run the build itself in the background and read
its exit status, rather than watching for its process to disappear.

## A `for … range` loop variable must be inside the `wp_for` invariant

`slice.for_range` desugars to a `for:` whose index *and* range variable are
allocated **outside** the loop, and the body assigns the range variable on
every iteration. `wp_for` freezes everything left in the ambient Iris context
into the loop frame with `iNamedAccu`, **at its value right then** — so
`campaign`'s range variable was pinned as `"cur" ∷ cur_ptr ↦ W64 0`, and no
branch of the body could restore it.

The symptom is not at `wp_for`: it is `iFrame` failing to close the invariant
at the *end* of every branch, with a leftover `cur_ptr ↦ W64 0`. Quantify it:

```coq
iAssert (∃ (n c : w64),
   "i" ∷ i_ptr ↦ n ∗ "cur" ∷ cur_ptr ↦ c ∗ … )%I
  with "[i cur Hphys]" as "IH".
```

(`proof_raft__campaign.v`, 2026-09-16.)

## A spec's postcondition about a *message variable* leaves projections `rewrite` cannot see

`wp_raft__send_vote` concludes
`own_raft_phys … (send_msgs s [msg.mk ty id m.(Message.To') m.(Message.Term')
m.(Message.Reject')])`. At a call site where `m` is a Goose composite literal,
the hypothesis you get back therefore contains `{| … |}.(Message.To')` and
friends, *unreduced*. Every `rewrite` and `iEval (rewrite …)` then fails to
find its subterm, and `simpl` is not safe here (it also unfolds
`own_raft_phys` and `send_msgs`).

State the folded form and close it by conversion instead — `iExact` unifies up
to iota, `rewrite` does not:

```coq
iAssert (own_raft_phys cfg r id (send_msgs s' (cmsg <$> take (i+1) xs)))
  with "[Hphys]" as "Hphys".
{ rewrite -Hstep. iExact "Hphys". }
```

Related and useful: ssreflect `rewrite Hpure` inside an Iris goal rewrites the
whole `envs_entails` term, **hypotheses included**, so a plain `rewrite` does
reach a named hypothesis whenever the equation matches it syntactically.

## `wp_if_destruct` at a loop's exit has already run the rest of the function

In the false branch of `wp_for`'s condition there is nothing left for
`wp_auto` to do, and it fails with `Failed to progress.` — which reads like
the program is stuck when in fact it has finished. Go straight to
`iApply "HΦ"`. (`proof_raft__campaign.v`'s send loop.)

## Reading a pure fact out of a definition without consuming it

`own_tracker` carries `⌜size cfg < 2^63⌝`, which `campaign` needs for
`make([]uint64, 0, len(idMap))`. A helper stated `own_tracker cfg tv votes -∗
⌜…⌝` is useless: `iDestruct (lem with "Htrk")` consumes `Htrk`. State it as a
pair and destruct both halves:

```coq
Lemma own_tracker_cfg_size tv votes :
  own_tracker cfg tv votes -∗ ⌜ Z.of_nat (size cfg) < 2 ^ 63 ⌝ ∗ own_tracker cfg tv votes.
…
iDestruct (own_tracker_cfg_size with "Htrk") as "[%Hcfg_fits Htrk]".
```

## With several agents in one checkout, rocq-warm's session gets evicted

Sessions are multi-GB and the daemon's total budget is shared, so two agents
checking two large files evict each other between checks: every replay comes
back `[cold, …, 250–460s]` instead of the seconds the fork exists to give.
`make <file>.vok` is ~100s, is the authoritative check, and prints `Show.`
output just the same — for a 400-line proof it is the better inner loop
whenever the warm session cannot be kept. Raise
`ROCQ_WARM_MAX_SESSION_GB` if you can, and prefer to fan out over *small*
files.

## `proof_raft__Step.v` exceeds rocq-warm's default session ceiling

A cold check of it reaches 4.2 GB and rocq-warm discards the session:

    rocq-warm: rocq reached 4.2 GB, over the 4.2 GB ceiling; session
    discarded (raise the ceiling with ROCQ_WARM_MAX_SESSION_GB)

The default is half the daemon budget, which is itself `min(half of RAM, 32
GB)` — so on a 15 GB box it lands just under what this file needs. Export
`ROCQ_WARM_MAX_SESSION_GB=9` (and `ROCQ_WARM_MAX_RSS_GB=11`) before checking
it. The file is the largest in the election development and a session for it
costs roughly twice what `coqc` peaks at.

**`make <file>.vok` swallows `Show.` output; `rocq compile -vok` does not.**
An earlier version of this entry blamed `-vok` itself. That was wrong — the
mode is fine, it is the `make` path (via `etc/rocqc.py`) that eats the
output. Invoking the compiler directly prints goals:

```sh
rocq compile -vok -Q src Perennial -Q new New /tmp/scratch/mvr.v
```

which gives **the best inner loop found so far for a lemma in a huge file**:
put the one lemma in a scratch module under `/tmp` that only `Require`s its
`postulates_*` file, and `-vok` loads the `.vos` closure rather than
rebuilding it — 3.7 s to load, ~56 s per iteration for a lemma whose
`wp_start`/`wp_auto` runs over `Step`'s body, 710 MB peak. That is a
batch-of-twenty-lines loop instead of the tens of minutes a cold rocq-warm
session on `proof_raft__Step.v` costs, and it keeps the source tree clean.
(Found 2026-09-16 while proving `Step`'s `MsgVoteResp`.)

## Backticks in a `git commit -m "..."` can start a full Perennial build

Writing a commit message with `git commit -m "... `rocq compile ...` ..."`
lets the shell run whatever is inside the backticks. On 2026-09-16 that
substituted away two words of a message and, worse, **invoked `make`**, which
went straight for `src/base.vo` — i.e. it started building all of Perennial.
It happened to die immediately (no `rocq` on that subshell's `PATH`), but on
a machine with the switch activated it would have run for an hour.

Use a heredoc with a **quoted** delimiter, which does no substitution at all:

```sh
git commit -F - <<'EOF'
... message with `backticks` and $dollars, safely ...
EOF
```

This matters more here than in most repos because a stray `make` with no
target is the one command the project most wants you not to run — see
`CONTRIBUTING.md` and the `.vo` warning above.

## `proof_raft__Step.v` costs ~8 GB and ~30 min to check — this is what OOM-kills sessions

**Superseded 2026-09-17** — see the next entry and `STATUS.md` for the
current cost; it is several times lower after the framework changes made
that day. The discipline below is still right, only the budget moved.

Measured 2026-09-16: a single `rocqworker` checking that one file reached
**8.1 GB RSS** and ran over 26 minutes. On a 15 GB box that leaves room for
essentially nothing else.

Consequences, all learned the hard way:

- **`make -j1`, always.** Three sessions died to `-j6`, and several more to
  two or three agents each running their own build. One `rocqc` at a time is
  not a preference here, it is the budget.
- **Never leave overlapping checks running.** It is easy to launch a check,
  poll it, get impatient and launch another; two of these together is 16 GB
  and the machine dies. Check for a live `rocqworker` before starting one:

      ps -eo pid,etime,rss,comm --sort=-rss | head -3

- **Do not run a second agent while this file is being checked.**
- It also exceeds rocq-warm's default session ceiling; see the entry above.

The file is the largest in the election development (three branch lemmas plus
the top-level dispatch, each stepping through `Step`'s whole body). If it
grows much further it is worth splitting the branch lemmas into their own
files, notwithstanding the one-spec-per-function rule — that rule is about
*specs*, and these are internal lemmas.

## A translated body can be *stuck*: check that it steps before proving about it

Found 2026-09-16 on `wp_campaign_peer_ids`, and then twice more. Goose emitted
array operations against a **loaded array value** where the model's rules
need the address, and `len` of an array had no rule at all — so the
translated body could not step, and no Hoare triple about it was provable.
**Fixed 2026-09-17** (`goose/goose.go` and `new/golang/defn/array.v`); the
bug file is gone, see the 2026-09-17 entry in [journal.md](journal.md).

The same shape of finding is still open for `len` of a **nil map**:
[../bugs/golang-len-of-nil-map-is-stuck.md](../bugs/golang-len-of-nil-map-is-stuck.md).

The transferable part is the habit, not the defect:

**Reading a callee's translated body is not enough — check that it can
actually step.** `wp_start; iNamed; wp_auto` to the first stuck point costs
one scratch run and is the cheapest possible test of whether a `wp_*` lemma
is dischargeable *at all*. Doing it first converts "this proof is hard" into
"this proof is impossible", which is a completely different report and a
completely different next action.

A one-line probe isolates a suspect operator in about six seconds
(`iStartProof` first, or `wp_auto` fails for the wrong reason and you
misread it):

    ⊢ WP (IndexRef quorum.JointConfig (#(l : loc), #(W64 0)))%E {{ Φ }}   (* steps *)
    ⊢ WP (IndexRef quorum.JointConfig (#(a : array.t loc 2), #(W64 0)))%E (* stuck *)

## A method on `*T` where `T` is a named non-struct needs **two** `wp_call`s

`JointConfig'ptr_IDs_unfold` is `λ: "$r", MethodResolve JointConfig "IDs"
(![JointConfig] "$r")` — a wrapper that loads the receiver and calls the
*value* method. So `wp_method_call. wp_call.` lands on
`WP quorum.JointConfig__IDsⁱᵐᵖˡ #recv #()`, and the next `wp_auto` reports
`Failed to progress` — which looks exactly like a stuck program and is not.
A second `wp_call` enters the body. (`wp_start` does `wp_method_call; try
wp_call; try wp_call` for its own goal, which is why this only bites when you
step a call from inside another lemma.)

## Converting an `Axiom` to an `Admitted` `Lemma` changes the constant's type

Under this tree's `Set Default Proof Using "W"` (`W := sem + package_sem`) a
`Lemma … Admitted.` discharges **W's variables as well as the ones the
statement mentions**. An `Axiom` discharges only the latter. For
`wp_campaign_peer_ids` that added a `raft.Assumptions` binder the axiom did
not have, silently changing the arity every call site sees. Write
`Proof using Type.` on the converted lemma and the type comes out
syntactically identical to the axiom's.

To check this rather than guess, put the `Axiom` and the `Lemma` side by side
in one scratch section, then after `End proof.` do
`Set Printing All. Check @as_axiom. Check @as_lemma.` and diff the two.

**Since 2026-09-18 this does not arise for a Go function's spec**, and that
is a reason the `_body` form is worth the verbosity: a
`Definition wp_<fn>_body := ∀ <ambient> …` names every binder itself, in no
section, so there is nothing for `Proof using` to discharge and an `Axiom`
and a `Lemma` against the same `_body` have the *same* type by construction.
It still arises for anything stated inside a `Section`, which is every
predicate and pure lemma in the `inv_*.v` files.

## `len` of a *named* map type cannot be stepped; `go.len_underlying` is the way out

`new/golang/defn/map.v` declares its `FuncUnfold` instances at the literal
`go.MapType key_type elem_type`. `new/golang/defn/slice.v` declares the
corresponding slice ones at any `st ↓u go.SliceType elem_type`. So
`len(p.Progress)`, whose static type is the *named* `tracker.ProgressMap`,
leaves `wp_auto` parked on a bare

    #(sem.(go.sem_fn).(functions) go.len [tracker.ProgressMap])

with no error and no hint. The escape hatch is the predeclared-semantics
axiom `go.len_underlying` (`new/golang/defn/predeclared.v:553`,
`functions len [t] = functions len [underlying t]`), plus `go.is_underlying`
to compute the underlying type:

```coq
rewrite (go.len_underlying tracker.ProgressMap).
rewrite (go.is_underlying (t := tracker.ProgressMap)
           (tunder := go.MapType go.uint64 (go.PointerType tracker.Progress))).
wp_func_call. wp_call.   (* wp_start's wp_func_call already ran, before the rewrite *)
```

There are siblings for `cap`, `clear`, `copy`, `delete`, `make1/2/3`. Worked
example: `wp_ProgressMap_len` in
`new/proof/go_etcd_io/raft/v3_proof/election/inv_tracker.v`.

**`len` of an *array* type has no instance at all** — neither literal nor
underlying-based; `new/golang/defn/array.v` declares none, and
`go.len_underlying` cannot help because an array type is already its own
underlying type. So `var sl [7]uint64; if len(sl) >= n` is simply unsteppable.
That is one of the two things blocking `ProgressTracker.Visit`.

## `wp_auto` parks on an *anonymous* `GoAlloc`; `wp_alloc x as "H"` gets past it

Go's named-return declaration (`func … (…, r VoteResult)`) and a `var _ T`
translate to `let: <> := GoAlloc T (GoZeroVal T #()) in …`. `wp_auto` reports
`Failed to progress.` in front of it — which reads as if the *first real
statement* were stuck, and sends you looking at the wrong thing.
`TallyVotes` opens with one. Fix:

```coq
wp_start as "…". wp_alloc res0 as "Hres0". wp_auto.
```

(`wp_tracker_NewInflights` in `inv_tracker.v` hits the same thing for a
`GoAlloc` in `return:` position and uses `wp_apply wp_alloc` instead.)

## A pointer-receiver method's spec has to own the receiver's *fields*

`own_tracker tv votes` is indexed by the tracker *value* and owns what that
value points at — the vote map, the progress map, the id sets. It owns
nothing of the struct `trk` itself. So a spec for a `func (p *T) M()` whose
body reads `p.Field` needs `trk ↦ tv` (or that field's points-to) *as well*,
or the triple is not derivable — it asserts safety of a load from a location
it does not own.

`wp_ProgressTracker__Visit` was written without it and is false for exactly
this reason (found 2026-09-16; `ResetVotes`/`RecordVote`/`TallyVotes` all have
it). The tell: the spec's own comment argued the method "does not mutate the
tracker, so it does not need the location". Mutation is not the question —
**any** read through the receiver is. Grep a pointer-receiver spec for
`↦ tv` before believing it.

The cheap check is two probes: `wp_start; iNamed "Hown"; wp_auto` with and
without the field points-to, and see whether `wp_auto` moves.

## `split_and!` breaks when `iFrame` gets better at discharging pure goals

`iPureIntro. split_and!; reflexivity.` is a common ending for a re-seal, and
it is **brittle**: how many pure conjuncts survive the preceding `iFrame`
depends on which of them `iFrame` can discharge by itself, and that changes
whenever a predicate in the goal stops being opaque.

Concretely, 2026-09-16: `proof_raft__becomeCandidate.v` had been `Qed` for
days, and broke the moment `own_raftLog` went from `Axiom` to `Definition`
— `iFrame "Hr1 ∗#%"` then closed all but one pure goal, leaving a single
equation, and `split_and!` (which insists on splitting *at least once*)
failed with the unhelpful

    Error: No matching clauses for match.

**Use `split_and?`**, the non-failing repeat, or just `done`. Nothing about
the proof was wrong; only the arity of what was left.

The wider point: **a predicate that stops being opaque is not a
backwards-compatible change**, even when its type is identical. Re-verify
every `proof_*.v` downstream of an `inv_*.v` you touched, not only the file
you edited. The same sweep caught this one, and it would otherwise have
shipped green-looking.

## Strengthening a predicate is free only where it is passed through

Adding a conjunct to an `own_*` definition costs nothing at the call sites
that hold it opaquely and re-frame it with `iFrame "∗#%"`. It costs
something at every site that **destructs and rebuilds** it — and the failure
is silent on the way in.

`own_progress` gained `⌜pv.(IsLearner') = false⌝`. `proof_raft__reset.v`'s
`Visit` closure opens it with

    iDestruct "Hpr" as (pv) "[Hpv Hinfl]".

A two-element pattern against a three-element definition **does not fail** —
it drops the third — and the proof then dies much later, at the `}` that
should have closed the re-seal, on a goal (`⌜… = false⌝`) with no visible
connection to the `iDestruct`. Name the new conjunct on the way in
(`"(Hpv & Hinfl & %Hnolearner)"`, or `iNamed`) and hand it back.

## Every proof-mode tactic on a `WP` goal is linear in the *program text*; hide it

Found 2026-09-17 while profiling `proof_raft__Step.v` (then ~45 min). The
translated `Step` body is a ~500KB term once notations are off (string
literals are `list w8`, variable names are `String (Ascii …)` chains), and it
sits in the goal for the whole proof. Anything that traverses or unifies
against the goal pays for it:

| on the `Step` goal | program visible | program let-bound |
|---|---|---|
| a *failing* `iPureIntro` / `iExists _` / `iSplitR` | ~2.5 s each | ~0.01 s |
| `rewrite Hx //` (the `//` fails on the `WP`, trying each Iris `Hint Extern`) | ~7 s | ~1 s |
| `iNamed "Hphys"` (25 conjuncts) | ~12 s | ~1 s |
| `wp_apply (wp_traceReceiveMessage …)` | ~4.7 s | ~0.8 s |

"Let-bound" means the program is a `set` variable in the context: the goal is
convertible to the original, but unification sees a variable. That is what
`new/golang/theory/proofmode.v` now does inside the tactics (`wp_apply`
binds the evaluation context around its `iApply`; `done` binds the body
before running stdpp's `done`). The program is always visible again when a
tactic returns, so `rewrite Hb` on the program text keeps working.

What this means for writing a proof against a big function:

- **Destructure the precondition before the body is unfolded.**
  `wp_start_folded as "@". iNamed "Hphys". wp_start_unfold.` instead of
  `wp_start as "@". iNamed "Hphys".` — 12 s → 1 s per lemma.
- **Wrap an `iNamed`/`iNamedSuffix`/`iDestruct` that runs mid-body in
  `wp_hidden (…)`.** `wp_hidden (iNamedSuffix "Hphys" "1")`. It hides,
  runs the tactic, unhides.
- **Do not re-seal a 25-conjunct predicate with `iFrame "∗#%"`.** That costs
  ~17 s per use — `iFrame "%"` alone tries every pure fact in the Coq context
  against every conjunct — and it is what every re-seal of `own_raft_phys`
  did. Write an intro lemma once (`own_raft_phys_intro` in
  `inv_raft_phys.v`) and re-seal with
  `iApply (own_raft_phys_intro with "Hlogger Hr Htrk …"); done.` (~0.1 s).
  This has nothing to do with program size; it is `iFrame` on a big goal.

The other half of the 2026-09-17 speedup is in the stepping tactics
themselves: a pure step used to run `MaybeIntoLaterNEnvs` over the whole
context, which unfolds every hypothesis (`own_tracker`, `own_raft_misc`, …)
through its definition looking for a `▷`. With no `▷` in the context that
search is skipped (`tac_wp_pure_wp_no_later`). If a proof *relies* on a later
being stripped from inside a definition on a pure step, it will now have to
unfold that definition first — none in this tree did.

Two more, found the same day in the same file, that are not about program
size but hit the same proofs:

- **`set_solver` on a list-membership goal can run for minutes.** It is
  `try fast_done; intros; setoid_subst; set_unfold; …; naive_solver eauto`,
  and with the `Step` proof's Coq context in scope the same goal took 4s in
  one lemma, 150s in another and timed out at 400s in a third
  (`m' ∈ [a] ++ [a] → m' = a`; `set_unfold; naive_solver` alone is 1s).
  Rewrite the membership away instead: `solve_log_method` in
  `inv_logger.v` for `meth ∈ log_methods`, and `recv_elem` in
  `proof_raft__Step.v` for the `recv` lists. Reach for `set_solver` on a
  goal with a big context only after timing it once.
- **`rewrite … // in H1 H2` runs `done` on the *reverted* goal
  `H1 → H2 → WP …`.** ssreflect's `in` clause reverts the hypotheses first,
  so the `//` is not looking at a `WP` goal and the guard in `done` did not
  fire; stdpp's `done` then `intros` and cascades against the visible
  program — 36s for one rewrite. `done` now also catches goals with a `WP`
  under binders. If in doubt, write `rewrite … in H1 H2; [|exact Hne]`,
  which is 0.03s and says which side goal you meant.

One more, inside the framework rather than a proof, found in the second
round of profiling the same day:

- **An Ltac2 `constr:(… $e …)` quotation re-elaborates its antiquoted
  arguments.** `walk_expr` built the evaluation context with
  `constr:(@AppRCtx _ $e1 :: $k)` at every level of the walk, and with a
  100k-node body each level re-typed a large subterm: 16–35 ms per walk,
  several walks per step. `Constr.Unsafe.make` builds the same term in under
  a millisecond and the term is type-checked once, by the `refine` that uses
  it. In Ltac2 that runs per step over a big goal, never `constr:` a term
  containing a big antiquotation in a loop.

How to see where the time goes, in about two minutes: put one lemma in a
scratch file that `Require`s its `postulates_*` file, add
`Set Ltac Profiling.` before it and `Show Ltac Profile.` after `Qed`, and
compile with `rocq compile -time -vok`. `-time` gives per-command seconds,
the profile gives the tactic tree. `tc_solve` at the top with hundreds of
calls means a typeclass search is unfolding something it should not.


## An `Ltac` inside `Section proof` is not visible to files that import it

`inv_raftlog.v`'s `split_unstable` was `Local Ltac` inside `Section proof`.
When the three `raftLog` proofs that used it moved into their own
`proof_*.v` files (2026-09-18), dropping the `Local` was not enough: the
importing file still failed with

    Error: The reference split_unstable was not found in the current environment.

An `Ltac` declared inside a `Section` goes out of scope when the section
closes, `Local` or not. Put it **above** `Section proof`, which is where the
two that already worked live — `intros_ambient` (`election/defs.v:12`) and
`wp_log` (`inv_raft_phys.v:10`) are both above their sections. A tactic body
that mentions no section variable, which is the usual case, needs nothing
else.

## `Import P.` inside a functor, so a moved callee does not need re-qualifying

When a callee's spec moves out of a globally-`Require Export`ed `inv_*.v` and
into a `Module Type` that the caller postulates, every use in the caller
becomes `P.wp_<callee>`. Rather than rewriting the call sites, open the
parameter once:

    Module ResetProof (P : RESET_POSTULATES) : RESET.
    Import P.
      (* wp_apply (wp_newReadOnly with "…")  still resolves *)

`Import` of a functor parameter is legal and the existing `P.wp_…` uses keep
working, so the two styles coexist. This is worth the two characters on the
expensive proofs specifically: `proof_raft__Step_MsgVote_gt.v` takes 2:39 and
2.3 GB to check, so an edit to it that is not the point of the change is an
edit worth not making.

## Do not slice a Rocq doc comment with a non-greedy `.*?\*\)`

Not a proof trap, a tooling one, recorded because the repair cost more than
the move. Several doc comments in this development *contain* `(* … *)` —
worked examples, probe lemmas, an inline aside. A non-greedy match from
`(**` to the first `*)` stops at the inner comment's terminator and silently
takes a prefix, leaving the rest of the block orphaned in the source file and
an unterminated `(**` in the destination. The symptom is a file whose second
half vanishes: `etc/check-module-discipline.py` reported
"spec file declares 0 Module Types" for exactly this reason. Count nesting
depth instead — `strip_comments` in that script does, and it is the shared
helper to reuse.

## Restoring a `.v` file with its old mtime makes `make` use a stale `.vos`

Hit twice on 2026-09-18, the second time costing a full 25-minute `vok`
sweep. Both times the symptom pointed somewhere other than the cause.

`make`'s `%.vos: %.v` rule compares mtimes, so **anything that puts an older
mtime on a source file leaves the artifact looking current**. Two ways to do
it by accident:

- `shutil.copy2` (and `cp -p`, `rsync -a`, `git stash`-style round trips)
  preserve the *source's* mtime. Save a file, overwrite it, build, restore
  with `copy2` — and the `.vos` built from the overwritten version is now
  newer than the restored original. `make` skips it. Everything downstream
  then compiles against a spec that is not in the tree.
- Editing a file while a build is running: the artifact gets written after
  the edit, from the pre-edit source.

The tell is an error that does not match the source you are reading.
`iAndDestruct: cannot destruct (own_raft_phys …)` on a `[Hphys Hes]` pattern,
when the spec in front of you plainly has two conjuncts, means the `.vos`
holds a different spec. Confirm with `stat -c %y` on the `.v` and its
`.vos`, not by re-reading the proof.

The other shape of it is at the aggregator:
`Error: Compiled library … makes inconsistent assumptions over library …`,
which is two `.vos` files built against different versions of a third.

So: after any file shuffling, `touch` what you restored (or delete the
artifacts) and rebuild the whole `vos` closure before sweeping. A partial
`vos` rebuild is worse than none, because it is silent.

## `wp_auto` on a stuck expression *succeeds* without making progress

Found 2026-09-17 while fixing the array-indexing defect. The old bug file
said `wp_auto` "fails with `Failed to progress`" on the stuck `IndexRef`. It
does not. On

    WP IndexRef (go.ArrayType 7 go.uint64) (#a, #(W64 0)) {{ Φ }}

with `a : array.t w64 7` — no rule matches, because `array.t` carries no
address — `wp_auto` returns **successfully** and leaves the goal
byte-for-byte unchanged. So

    assert_fails (wp_auto).          (* reports "wp_auto succeeds" *)

is *not* a test for stuckness, and neither is the exit status of the file.

**To tell whether a body is stuck, look at the goal.** `wp_auto. Show.` in a
scratch file, and read whether the head expression moved. This is the one
measurement the "check that it steps before proving about it" habit above
depends on, so it is worth getting right.

## A probe that restates an already-compiled lemma can prove itself

Found 2026-09-17, on the new `pure_wp_array_len` instance. The scratch probe
was

    Lemma show_state n elem `{!st ↓u go.ArrayType n elem} (v : val) :
      PureWp (0 ≤ n < 2^63) (#(functions go.len [st]) v) #(W64 n).
    Proof. pure_wp_start. (* closes the goal outright *)

and it passed — because the scratch file imports the compiled `array.vos`,
so `pure_wp_start`'s `wp_pures` discharged the restated goal using **the very
instance being restated**. Inside `array.v` itself the instance does not
exist yet, the goal is untouched, and the real proof needs `func_unfold` and
`decide_True`.

Two rules follow:

- **Do not probe a lemma by restating it.** Probe it by *using* it: a goal
  that can only be closed if the instance does real work. Here that was
  `WP (FuncResolve go.len [go.ArrayType 7 go.uint64] #() #())` against a
  concrete `Φ`.
- **A `.vos` build accepts a proof script that does not run** (this is in
  CONTRIBUTING and STATUS already), so a passing probe over a `.vos` tree
  says nothing about the proof body of anything it imports. Only `-vok` does.

## Editing a `.v` file invalidates the `.vos` of everything downstream, mid-sweep

Found 2026-09-17. A `-vok` sweep over ~100 files was running when `array.v`
was edited and its `.vos` rebuilt. Every file checked after that point failed
with

    Compiled library New.golang.theory.pre (in file …/pre.vos) makes
    inconsistent assumptions over library New.golang.theory.slice

— 68 failures that looked like a catastrophic regression and were entirely an
artefact. `array.v` sits under `slice.v`, which sits under nearly everything.

**Freeze the tree for the duration of a verification sweep.** Rebuild the
`.vos` closure from a clean slate first (`find new -name '*.vos' -delete`),
then sweep, then edit. If a sweep reports mass failures, read one log before
believing it: "inconsistent assumptions over library X" is a staleness
message, not a proof failure.

## `make x.vok` leaves no `.vok` file behind

The `etc/rocqc.py` wrapper that `make` runs does not write the empty `.vok`
marker `rocq compile -vok` would, so `ls *.vok` proves nothing and a fresh
`make <file>.vok` is never skipped as up to date. The only evidence that a
proof checks is the exit code of the run you watched. (Found 2026-09-19
while verifying an agent's report: the proof was fine, the artifact was
simply not there.)

## `wp_auto` reduces `pr != nil` before you can rewrite it

After a `wp_apply` whose postcondition hands back a pointer `pr`, the test
`pr ≠⟨ptr⟩ nil` is already `# (negb (bool_decide (pr = null)))` — and when
the value is literally `null` it is already `#false`. So in the "present"
branch, `rewrite (bool_decide_eq_false_2 (pr = null) Hnn)` has to come
*before* the next `wp_auto` (which otherwise says "Failed to progress"),
and in the "absent" branch there is nothing left to rewrite —
`rewrite (bool_decide_eq_true_2 (null = null) eq_refl)` fails with "LHS
does not match". Give `bool_decide_eq_false_2` its proposition and proof
explicitly: `rewrite bool_decide_eq_false_2 //` leaves the `¬ pr = null`
side goal unsolved and the next tactic sees two goals. Same family as the
`bool_decide_eq_true_1` / inferred-`Decision` entry above. Goose emits `a &&
b` as `If a b #false` (`new/golang/defn/postlang.v`), so once the first
operand is `#false` the rest of the conjunction is never evaluated — no
ownership is needed for what it would have read. (`promotable`, 2026-09-19.)

## Plain loads through a sealed `r ↦ rv` need no `access_strict`

`wp_start as "(Hr & …)". wp_auto.` steps `r.trk.Progress` and `r.id` reads
on its own when the function never stores to `r`. The `access_strict`
idiom is for handing a callee the *location* of one field (poll's
`RecordVote`, reset's `ResetVotes`), not for reads. (`promotable`,
2026-09-19.)

## `wp_apply … as "H"` already runs the pure steps that follow

After `wp_apply (lemma with "…") as "H"`, the goal already sits on the next
non-pure redex. A `wp_auto.` written after it fails with `Failed to
progress`, which reads like "stuck on a step it cannot take" when in fact
there is no step left. Look at the goal before adding `wp_auto`. Two of the
three defects in the first `Visit` script were exactly this. (2026-09-20.)

## Bullet depth inside `wp_if_join`

`wp_if_join` leaves three goals under `-`; a `wp_if_destruct` or `destruct`
inside the third must use `+`. Rocq's message, "Current bullet - is not
finished", reads as "a case is still open" and sends you hunting for an
unproved goal that does not exist. (`Visit`, 2026-09-20.)

## Slicing a stack array: `sl[:n]` on `var sl [7]uint64`

With Goose passing the array's address, three steps, each with its own
nudge (`proof_ProgressTracker__Visit.v`):

- `wp_auto` leaves `sl_ptr ↦ (a : array.t w64 7)`, a typed points-to at the
  array type (through `into_val_typed_array`, `new/golang/theory/array.v`,
  which is still `Admitted` in the framework). `slice_array`
  (`new/golang/theory/slice.v`) consumes it; its side condition
  `length (array.arr a) < 2^63` is closed by `simpl; lia`, not `word` — the
  `7` is hidden under `array.arr`.
- `slice_array` returns the **whole** array as `slice.mk l (W64 n) (W64 n) ↦* array.arr a`;
  the `[:n]` prefix comes from `own_slice_split_all (W64 k)`, again `simpl`
  before `word` on the side condition.
- The two sides are then not syntactically equal: `slice_array_step`
  produces `slice.mk (array_index_ref V (word.signed low) p) (high-low) (7-low)`
  while `own_slice_split_all` says `slice.slice s V (W64 0) k`.
  `rewrite /slice.slice /slice_index_ref /=` makes them the same term;
  without it `iFrame` silently fails to find the hypothesis.

## A pure premise about a record update must be elaborated *before* `wp_apply`

`wp_raft__resetRandomizedElectionTimeout` takes `0 < sint.Z rv.(electionTimeout') →`
before its triple. At the call in `reset`, the heap holds
`r ↦ rv <| lead' := W64 0 |> <| electionElapsed' := W64 0 |> <| … |>`. Two
obvious ways to pass the premise both fail with an `iFrame: cannot frame`
whose two sides print identically:

- `wp_apply (lem _ _ HelectionTimeout with "[$Hr]")` — the hypothesis is
  stated at the bare `rv`, so unification fixes the lemma's `rv` to the
  pre-update struct.
- `wp_apply (lem _ (rv <| lead' := … |> …) HelectionTimeout with "[$Hr]")` —
  the `Setter` typeclass evars in the explicitly written struct are still
  unresolved when the premise is unified, and first-order unification fills
  the *instance* evar with a degenerate term instead of the real setter. The
  goal then differs from `Hr` only in a hidden, merely convertible argument.

What works: establish the premise at the updated struct in its own step,
then pass the hypothesis:

    assert (0 < sint.Z (rv <| raft.raft.lead' := W64 0 |> <| … |>)
                          .(raft.raft.electionTimeout')) as Het
      by exact HelectionTimeout.
    wp_apply (lem _ _ Het with "[$Hr]") as "%n Hr". clear Het.

`exact` closes it by conversion since the setters leave the field alone.
Also: `wp_apply`'s `as` clause runs on the *last* goal, so leaving a pure
premise as a side goal and proving it after `as` does not work either.
(`reset`, 2026-09-20.)

## Two agents' `make` runs can leave "inconsistent assumptions" between `.vos`

`Compiled library X makes inconsistent assumptions over Y` mid-run means
another writer rebuilt a `.vos` under you. Re-run the same `make …vok`; it
rebuilds the stale intermediate and the message goes away. Not a proof
error. (2026-09-20.)

## `wp_auto` stalls on a `slice.for_range` whose counter name collides

`for_range` expands to `let: "i" := GoAlloc go.int #(W64 0) in for: …`.
When the enclosing Go frame already has a local `i` (`for i := range ents`
inside a closure whose caller also had an `i`), `wp_auto` refuses to
allocate the second one and simply stops. `wp_alloc j_ptr as "j". wp_auto.`
gets past it. (`hasUnappliedConfChanges`, 2026-09-20.)

## `IndexRef`'s `decide (0 ≤ i < len)` appears one `wp_auto` at a time

Each `wp_auto` that exposes a slice index leaves an
`if decide (0 ≤ i < len) …`; `rewrite decide_True; last word.` must follow
*that* `wp_auto` — issuing it early fails with "does not match any
subterm". A body with three element reads needs three of them.

## A field read of a slice element is not `wp_load_slice_index`

`ents[i].Type` loads at the *field*, so `wp_load_slice_index` fails with
`iApply: cannot apply`. Use `own_slice_elem_acc (sint.Z k) e s dq es` to lend
`slice_index_ref … ↦{dq} e`, let `wp_auto` read the field, give it back,
and `rewrite (list_insert_id _ _ _ He)`.

## `wp_apply … with "[$H1 $H2]"` and an unframed pure conjunct

If the callee's precondition has a pure conjunct that the `[$…]` pattern
does not frame, `wp_apply … as "…"` dies with "Expected a single focused
goal but 2 goals are focused" — even when the fact is in the Coq context.
Produce it as an Iris hypothesis first (`iAssert (⌜…⌝)%I as "HP"`) and frame
it. Related: a callback side goal arrives as `"HI" ∷ emp ∗ "#Hf" ∷ □ …`, so
`iSplitR; first done.` comes *before* `iModIntro` (which otherwise reports
"the goal is not a modality"). And `Forall_lookup_1` does not unify against
`Forall (λ e, e.(Type') = EntryNormal) es`; use
`rewrite List.Forall_forall in H. apply H, list_elem_of_In.` as
`Forall_sublist_of` does.

## Destructure `is_Storage` with `iNamed`, not positionally

`is_Storage` is gaining clauses (`HEntries`, `Hbounded`, `HSnapshot` on
2026-09-20 alone). A positional pattern such as
`"(%Hstok & #HLI & #HFI & #HT & #HE)"` silently absorbs the extra clauses
into the last binder and then breaks a later `clear` with
`Error: lv is used in conclusion` — that was `proof_raftLog__term.v`'s
failure. Write `iDestruct … as (isv) "#Hs". iNamed "Hs".` as
`proof_raft__appendEntry.v` does.

## `word` runs `subst`, and can delete the binder your postcondition names

`own_raft_phys`'s `Hid : rv.(raft.raft.id') = id` is exactly the shape
`word` eliminates, so after the first `word` the binder `id` is gone and
everything, `HΦ` included, reads `rv.(raft.raft.id')`. Writing
`own_raft_phys cfg r id s` afterwards yields the baffling
`The term "id" has type "?A → ?A"`. Either `word` before you need the
name, or `pose proof` the fact and `clear` it. (`appendEntry`, 2026-09-20.)

## `slice.for_range` allocates its own counter; both pointers go in the invariant

The construct allocates a counter distinct from the Go-level `i` the body
assigns `$key` to. `wp_auto` parks in front of that `GoAlloc` ("Failed to
progress"); `wp_alloc j as "Hj"` then `wp_auto`, and **both** pointers must
be in the `wp_for` invariant. (The anonymous-`GoAlloc` entry above is the
same trap for a `var` declaration.) Also: `wp_apply lem` where `lem`'s
postcondition is `True` must not take an `as` pattern ("iIntro: nothing to
introduce").

## A half-created collection breaks every agent's `make`

`link_<fn>.v` written before `proof_<fn>.v` exists makes `rocq dep` fail on
the whole tree (`.rocqdeps.d` is global), so every other writer's `make`
dies until the file appears. Create the four files of a collection
together, `proof_` before `link_`.

## `iNamed` stops silently at the first name already in use

It leaves the rest of the predicate bundled in the original hypothesis. In
`bcastAppend`'s closure the enclosing proof's persistent `Hlogger` did
exactly that, and the symptom was `iSpecialize: "Hmisc" not found` fifteen
lines later. `iClear` the clashing name first. (2026-09-20.)

## After `wp_for`, section variables and Coq hypotheses are gone

`wp_for` re-introduces the Coq context: the section variable `cfg` and
hypotheses like `Hprs_dom` are no longer nameable by a tactic inside the
loop. Facts the body needs travel inside the loop invariant (`Visit`
carries `⌜∀ y, y ∈ ys → y ∈ cfg⌝`), and lemma applications use `_` where
they would have named `cfg`.

## Making a predicate conjunct persistent: the whole blast radius

Every `iFrame "∗%"` re-seal becomes `iFrame "∗#%"`; every
`wp_apply (… with "Hprs") as "Hprs"` becomes `as "_"` ("not fresh"); and the
change can pull `ffi_semantics0` into a proof, which under
`Set Default Proof Using "W"` needs `Proof using All`. That was the entire
edit on the eight consumers of the read-only progress map.

## `own_raft_phys_intro` takes its abstract state from the first argument that mentions it

At a `send_msgs s ms` goal, give the state explicitly:
`own_raft_phys_intro cfg r id (send_msgs s ms)`; otherwise it unifies from
`own_tracker … s.(nstate.votes)` and the outbox conjunct fails.

## `word` cannot refute `W64 0 = W64 2`

"Cannot find witness". Use `apply (f_equal uint.Z) in H; vm_compute in H;
discriminate` (a `w64_ne` beside `defs.v`'s `w32_ne` is the right home;
two files carry a local `w64_absurd` today).

## `err == ErrCompacted`, `go.min`, and slice-equivalence rewrites

- `err == ErrX` on an `error` interface does not produce a `bool_decide`; it
  reduces to a `match` on the global's value. `destruct errX; try (exfalso;
  by apply HErrX)` after `is_pkg_init_access`, not `rewrite bool_decide_…`.
- `go.min` has no `PureWp`; `wp_auto` stops dead. `change ([go.uint64; go.uint64])
  with (replicate 2 go.uint64). rewrite func_unfold /minⁱᵐᵖˡ.` — the
  `change` is needed because `min_unfold`'s head is `replicate n t`.
- `own_slice_split_all` / `own_slice_slice` are `⊣⊢`; `iDestruct` runs them
  left to right only. To go back use `own_slice_combine` +
  `own_slice_trivial_slice_2`, or `rewrite` the equivalence on the goal
  **with `s`, `dq`, `vs` given explicitly** — otherwise the setoid rewrite
  hits the first `_ ↦*{_} _` in the IPM *context* and leaves an unprovable
  side condition that looks like a `word` failure.
- `wp_if_destruct` auto-names `n`, `n0`, `e`, …: do not reuse those as
  binder names in the same proof. A `return:` inside a `for:` body wants
  `wp_auto` first (to `return_val v`), then `wp_for_post`.
- ssr `rewrite Hstok` on an IPM goal rewrites the environment too; re-seal
  `own_raftLog_at` with `iExists lv. rewrite Hstok. iFrame "∗#%". all:
  (iPureIntro; done).`

