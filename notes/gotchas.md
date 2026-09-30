# Gotchas

Traps that have already cost time. Add to this whenever something
non-obvious bites you — one entry, what happened, what to do instead.

Keep entries short. If an entry grows past a paragraph it probably wants to be
its own topic file in `notes/`, with a pointer from here.

---

## Don't add a variant of `own_raft_phys` -- refine `nstate.t`

When a spec will not go through on `own_raft_phys` -- a callee needs a
field the struct predicate hides, a caller must hold something across a
call, a function runs while the struct is between two consistent states --
the fix is a new field of `nstate.t` (`election_proof/defs.v`) and a conjunct of
`own_raft_phys` that pins it, **not** a second predicate. This was done
wrong three times (`own_raft_phys_at`, `own_raft_bare`, `own_raft_notrk`,
2026-09-16 to 2026-09-21) and undone on 2026-09-22; notes/decisions.md,
"Three layers", has the whole story and the fields that replaced them
(`stepfn`, `progress`, `log`, `lent`). The same holds for every object,
and was done for the tracker, `Progress`, `Inflights`, the log, `unstable`
and `readOnly` on 2026-09-23 (decisions.md): a loan is a field of the
object's state, not a second shape.  (The one such loan, of a slice of the
log lent to the caller, was `logstate.page` until 2026-09-29, when the log
started holding its entries read-only and the loan went.)

## `own_raft_phys_intro` takes `r ↦ rv` first, and wants `s` when it moved

The first spatial argument fixes `rv`; it is `r ↦ rv` so that `rv` is the
struct the heap holds *now*. A persistent argument first (it used to be
`is_Logger`, and briefly `Hprs`) fixes `rv` from wherever that hypothesis
was stated, and after any field write the heap's `r ↦ (rv <| … |>)` then
fails with `iSpecialize: cannot instantiate`. Likewise `s` is unified from
`Hprs`/`Htrk`, i.e. at the state the struct was *opened* at; when re-sealing
at a different state pass it positionally:
`own_raft_phys_intro _ _ _ (become_follower s t l) with "Hr Hlogger Hprs …"`
(`s` is explicit after the section closes -- `(s:=…)` does not parse).

## A premise passed positionally picks the callee's state

`wp_apply (wp_raft__sendAppend _ _ _ _ i Hne Hicfg Hlent with "[$Hphys]")`
with `Hlent : s.(nstate.lent) = None` fixes the callee's `s` from
`Hlent`'s *type*, i.e. at the caller's `s` -- even when the call is at
`send_msgs s ms` -- and the frame then fails with `iFrame: cannot frame`.
Either name the state (`… _ _ _ (send_msgs s ms) i …`) or let the frame pick
it and discharge the premise afterwards:
`wp_apply (lem with "[$Hphys]"); first exact Hlent. iIntros … . wp_auto.`
(the `as` pattern that the second form drops also ran `wp_auto`).

## `simpl in *` near a raft struct can run for minutes

The raft struct carries `func.t` values (`step'`, `tick'`), and `simpl`
unfolds `functions raft.stepFollower []` into the semantics tables. A
`simpl in *` over re-seal side goals ran 12+ CPU-minutes per file
(`becomeX`, 2026-09-22) before it was killed. Those goals hold by
conversion against the reopened hypotheses (`Hterm1 : rv0.(Term') = (reset_to s t).(term)`
and so on): close them with `done`, not `simpl`.

## A warm rocq-warm session keeps its old dependencies

After you change a file another one `Require`s and rebuild its `.vos`,
checking the dependent file *replays* in its warm session -- with the old
dependency still loaded. The symptom is an error that mentions the old
statement (2026-09-22: the old argument order of a lemma just reordered).
Stop the daemon first (`rocq-warm stop`) whenever an upstream statement
changed; a cold check is the only one that sees it.

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

What the fork fixes, all of which bit here (checked against
`upamanyus/rocq-warm` at `11b27cb`, 2026-09-18, on 2026-09-22):

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
- **Ctrl+C is now cheap, and it is the right thing to do** (added
  2026-09-18). Interrupting a check — Ctrl+C, a closed terminal, an agent
  that gave up, `kill -9` of the client — stops the *work* and keeps the
  *session*, parked at the line Rocq reached; the next check of that file
  replays from there. The daemon notices the closed socket, not a signal, so
  every way of dying is covered. Two consequences worth having in your head:

  - **Exit 130 is not a verdict either.** It means the question was
    withdrawn. Only 0 and 1 say anything about the proof.
  - **The old "killing a client wedges the file" advice is obsolete.** It
    used to leave the file checked out until the 30-minute wall timeout, so
    every later check of the one file you were working on came back exit 2
    ([journal.md](journal.md), 2026-09-16, records that). Now the slot comes
    back in the couple of seconds the interrupt takes. The one delay is
    inherent: a signal is only safe to send Rocq after a command has run a
    couple of seconds without printing, so for those seconds the file is
    still reported busy.

Remember that **exit 2 is not a verdict** — it means the file could not be
checked (stale dependency, already being checked, no daemon, no `rocq`). Only
0 and 1 say anything about the proof.

**It can also do the build step.** `--compile` writes the `.vo` after a
successful check, and `--rebuild` first compiles any stale dependency (in
dependency order, `ROCQ_WARM_COMPILE_JOBS` at a time, default 2), both with
`rocq compile` and the flags from the nearest `_RocqProject`. Neither is what
this tree wants day to day — we build `vos` and pass `--allow-stale` — but
`--rebuild` is the one-command way out if you have let a handful of `.vo`s go
stale. A plain green check warns that the `.vo` was *not* regenerated, which
is a statement about the build, not about your proof.

## `word` does not reliably close `W32 a ≠ W32 b`

It sometimes fails with "Cannot find witness" on goals as simple as
`W32 5 = W32 0 → False`, in contexts where the same shape works elsewhere.
Use instead:
`intros Heq; apply (f_equal uint.Z) in Heq; vm_compute in Heq; discriminate.`
(`w32_ne` in `new/proof/go_etcd_io/raft/election_proof/election.v`.)

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
section — `new/proof/go_etcd_io/raft/election_proof/proof_raft__Step.v`
does exactly this.
## The ambient binders of a `wp_<fn>_body`

This is the single write-up of how `election_proof/`'s closed-`_body` shape
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
available, since they come in with `election_proof/protocol.v` via `defs.v`; the
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

**A worktree is its own checkout for this purpose** (checked 2026-09-22):
rocq-warm keys its daemon on `git rev-parse --show-toplevel`, which in a
worktree is the worktree, so `.claude/worktrees/<name>/.rocq-warm/sock` is a
daemon of its own with its own session table and its own budget. Agents in
separate worktrees therefore do *not* evict each other's sessions, and
`rocq-warm stop` in one leaves the others alone. What they do still share is
the machine: each daemon's budget is capped at `min(half of RAM, 32 GB)`
independently, and eviction also watches `MemAvailable` against
`ROCQ_WARM_MIN_FREE_GB` (default `max(4 GB, 5% of RAM)`) — so on a small box
three worktrees can still push each other out, just via free memory rather
than via one shared budget.

Within one checkout the original problem stands:

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
`new/proof/go_etcd_io/raft/election_proof/inv_tracker.v`.

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
- **`done` on a `WP` goal does not use contradictory pure hypotheses.**
  The `done ::=` override in `proofmode.v` tries only `fast_done`/`trivial`
  there -- no `discriminate`, `contradiction` or `¬_` case split -- so a
  branch that is dead because of `Hl : length (x :: l) = 0%nat` or
  `Hnn : null ≠ null` is not closed by `done`/`first done`/`//` while the
  goal is a `WP`. Write `by exfalso` (the goal is then `False`, not a `WP`,
  and the full stdpp cascade runs). The override came in with 25ce5ca6f
  (2026-09-17) and broke four such sites in `chan_au_recv.v` and
  `chan_au_send.v` unnoticed for 12 days (2026-09-29 journal), and nine
  more in five other files (same day). It also catches goals that merely
  *contain* a `WP` -- an entailment `P ⊢ WP …`, an implication into one --
  so `destruct (envs_app …) eqn:? => //` in `dsp_proofmode.v` failed too.
  Where `try done` must close both live and dead branches (`destruct cst;
  try done`), write `try done; try by exfalso`. Only a full `vo` build
  finds these: `.vos`/`.vok` sweeps of the raft proof never run them.

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

## A `Global Instance` under `Proof Using "All"` is generalised over every earlier section variable

Including type parameters its statement never mentions. `tc_solve` then
cannot use it, because those parameters appear only as unconstrained evars,
and `wp_pure`/`wp_auto` report "Failed to progress" on a goal the instance
visibly matches. That is what kept `wp_map_nil_for_range` and
`pure_wp_map_nil_len` in `theory/map.v` from ever firing (fixed 2026-09-20).
Diagnostic: `About <name>` — look at the `Arguments` line for binders the
statement does not mention. Fix: an explicit `Proof using <needed vars>`,
or, more robustly, move the lemma above the `Context` that introduces the
offending variables.

## Giving a points-to back after `StartRead`/`FinishRead`

`_internal_wp_untyped_start_read` hands back a raw `heap_pointsto`, so the
sealed predicate (`own_map_def`) has to be re-established by hand at every
exit. State it once as a persistent `iAssert` right after `iNamed "Hm"`:

    □ ∀ mv', ⌜is_map_pure mv' mp⌝ -∗ ⌜map_default mv' = #(zero_val V)⌝ -∗
        heap_pointsto mref dq mv' -∗ own_map_def mref dq m

and every exit of the loop closes with one line. `wp_map_for_range` does
this now; any other `theory/` lemma that drops ownership across a read pair
wants the same shape.

## Never write a Go pointer type as `(*T)` inside a Rocq comment

`(*` opens a nested comment; the file then fails with `Syntax Error: Lexer:
Unterminated comment`, and because `.rocqdeps.d` is global it breaks `make`
for everyone sharing the checkout. Write `*T` or `(go.PointerType T)`.
(`base.v`, 2026-09-21, ten minutes of everyone's time.)

## Storing into a slice element: give `wp_store_slice_index` the value, then `wp_auto`

`wp_store_slice_index … _ _ _ (tracker.inflight.mk index bytes) with "[$Hbuf]"`:
left as an evar, `# ?v'` does not unify with the struct literal and `iApply`
"cannot apply". And after `rewrite decide_True; last word` the goal is a
`GoStore` of a `Pair (Val …) (Val …)`, while the lemma is stated at a value
pair; one `wp_auto` collapses it first. Conversely `wp_slice_make2` and
`wp_slice_copy` already step the store/field write/`return:` that follow
them — a `wp_auto` after them "Fails to progress". (`Inflights.grow`, 2026-09-21.)

## `iNamed` the ownership predicate before the `wp_auto` that reads its fields

Otherwise `wp_auto` stalls halfway through a field read, leaving a bare
`![go.int] (# l.[tracker.Inflights.t, "start"])` that looks like a missing
instance but is a missing hypothesis. A top-level `Ltac` cannot mention the
lemma's local variables — pass them as arguments; `Local Ltac` inside a
functor ascribed to a `Module Type` is fine.

## Turning a dead branch live: `destruct … eqn:` replaces the `assert Hb; rewrite Hb` idiom

Where a range test used to be dead and was killed with
`assert (Hb : bool_decide … = false). rewrite Hb /=.`, a total spec needs
`destruct (bool_decide …) eqn:Hb` — and the `rewrite Hb` that followed must
be deleted, since `destruct … eqn:` already replaced the occurrence ("The
LHS of Hb …"). (`raftLog.term`, 2026-09-21.)

## Sequence shared-file edits across agents

One agent editing `base.v` or an `inv_*.v` invalidates the `.vos` closure
(~450 files, ~8 min) under every other agent, and 3–4 `rocqworker`s then
contend for 8 cores; a `-vok` run that would take 2 min takes 20. The
2026-09-21 `maybeSendAppend` run spent ~4 h of wall clock almost entirely in
such cascades. When a wave has a shared-file edit in it, run that item
alone first.

## Comparing two non-nil Go errors: the `CheckComparable` wall

`go_eq_interface` (new/golang/defn/interface.v) is
`if decide (i1.ty = i2.ty) then CheckComparable i1.ty ;; GoOp GoEquals i1.ty (i1.v, i2.v) else #false`,
and `CheckComparable t` steps only for types Goose knows are comparable.
With an *unknown* dynamic type `wp_auto` parks on
`if decide (i.ty = i.ty) then CheckComparable i.ty ;; …` with no error
message. Comparisons against `ErrCompacted`/`ErrUnavailable` in `slice`
needed nothing only because the error there is `interface.nil`. For a
non-nil error you need its dynamic type to be a pointer type:
`is_initialized` (base.v) now carries `is_new_error errSnapUnavail`
(`∃ t p, e = interface.mk_ok (go.PointerType t) #p`, true of what
`errors.New` installs); then `check_comparable_pointer` fires and
`go_eq_pointer` gives `bool_decide (p1 = p2)`. Add the same clause for the
other error globals when a proof compares against them. (2026-09-21.)

## `is_pkg_init_access … as "@"` hands the globals out spatially

Framing one into a callee (`with "[$Hlog $ErrX]"`) consumes it even though
it is `↦□`, and the *next* load of that global leaves `wp_auto` parked with
no error. `iDestruct "ErrX" as "#ErrX".` right after the access moves it
into the persistent context.

## `interface.t`'s constructors are `ok | nil`, in that order

`destruct err as [|eok]` silently puts the nil case second and only warns
(`unused-intro-pattern`); write `destruct err as [eok|]`. Comparing a
non-nil error against `nil` does reduce (the `_, _ => #false` arm of
`go_eq_interface`); only two non-nil errors need the dynamic type.

## `wp_pure. wp_auto.` for `Convert go.untyped_bool go.bool`

`wp_auto` will not step it; `wp_pure` will. Appears at every `if err != nil`
after a total-triple call. (`maybeSendAppend`, 2026-09-21.)

## `case_bool_decide as H`, not `destruct (bool_decide P) eqn:H`, on a goal occurrence

`destruct … eqn:` often elaborates a different `Decision` instance and
fails to abstract the goal's occurrence, leaving `wp_auto` with nothing to
do ("Failed to progress"). `case_bool_decide` works on the goal's own.

## Ltac1's `A; [b|c]` counts all open goals

After a chain that leaves N goals, any further bracketed branching must be
parenthesised: `A; [b1|b2|b3]; (C)` runs `C` once per goal, while
`A; [b1|b2|b3]; C; [d|e]` fails with `Incorrect number of goals (expected 6
tactics)`. `maybeSendAppend` writes its common tail once for six leaves this
way. Related structural idea: when several `if` arms reach one program
point with different resources, package the differences into one
`Definition … : iProp Σ` with named conjuncts, binding any *value* that
differs existentially, and `iNamed` it in the shared tail (`msa_pkg` in
`proof_raft__maybeSendAppend.v`).


## Build timings recorded before 2026-09-21 mix `vo` and `vok`

`.timing.sqlite3`'s `file_timings` table was keyed on the filename alone,
with an `is_vos` flag, so a `vok` build overwrote the `vo` timing for the
same file and nothing afterwards could tell which of the two a number came
from. Since the inner loop is `make <file>.vok` and the numbers people quote
are `vo` numbers, the older figures understate `vo` cost by an unknown
amount — do not compare a pre-2026-09-21 figure against one taken since.

The table is now keyed on `(fname, mode)` with `mode` one of `vo`/`vos`/`vok`,
and `etc/rocqc.py` migrates an old database in place the first time it writes
to it. Legacy rows keep the only labels they can support: `vos`, or `vo` for
everything else. `etc/timing-report.py --mode vok` on a freshly migrated
database is therefore empty until something is rebuilt.
## `rocq` is not on the `PATH` — it is in the `perennial` opam switch

Found 2026-09-22. A fresh shell reports no `rocq`, `rocqc` or `coqc`, and
`opam switch list` warns that the environment is not in sync. The toolchain
is there — `~/.opam/perennial/bin/rocq`, Rocq 9.4+alpha — it just has to be
put on the path first, in every shell, since shell state does not persist:

    eval "$(opam env --switch=perennial --set-switch)"

A session that did not know this recorded "there is no Rocq on the box" in
`decisions.md` and settled for static verification of a 190-file move. Check
`opam switch list` before concluding a build is impossible.

## Rocq 9.4+alpha writes no `.vok` file, so a missing `.vok` proves nothing

Found 2026-09-22. `rocq compile -vok X.v -o X.vok` exits 0 and writes
`X.glob` and `.X.aux`, **but no `X.vok`** — with or without `-o`, even for a
trivial file. `CONTRIBUTING.md` still says it "emits an empty `vok` file";
on this toolchain it does not. Two consequences:

- **Do not judge a `-vok` sweep by counting `.vok` files.** It will be zero
  whether everything passed or nothing ran. Judge it by `make`'s exit status
  and the `Error` lines in its log.
- `make` can never consider a `.vok` target up to date, so every
  `make … X.vok` rechecks from scratch. Budget accordingly: all 197 raft
  files take ~27 minutes at `-j2`.

**The checking itself is real** — confirmed with a negative control: a file
requiring `election_proof/defs` whose only `Qed` proves `False` by `exact
I` fails under the exact flags `make`'s `%.vok` rule uses (rc 1, the right
type error), and the same file with a true lemma passes. The script is
worth keeping as the template for "does this invocation actually check
proofs?"

## `etc/mkvok` is stale

It collects its targets by grepping `make -n` for `echo "COQC `, but the
`Makefile`'s rules now print `ROCQ COMPILE`, and its default `FILE` is
`src/ShouldBuild.v`, where the build root is now `new/should_build.v`. It
finds nothing. Drive `make` with explicit `.vok` targets instead, e.g. every
file `etc/tcb-report.py` says the build reaches.

## `rewrite decide_False` takes the *outer* `decide` when they nest

`become_follower`'s vote field is itself an `if decide (term = s.term) …`,
and `vote_hist_ok` in `election_proof/protocol.v` wraps that in
`if decide (… = W64 0) …`. `rewrite` matches outermost-leftmost, so
`rewrite decide_False` picks the wrapper and leaves a side condition you
cannot prove — reported as

    The LHS of decide_True … does not match any subterm of the goal

one tactic later, which points at the wrong line.

Rewrite the *projection* before anything unfolds it, with a one-line lemma
per field:

```coq
Local Lemma become_follower_vote_ne s term lead :
  term ≠ s.(nstate.term) → (become_follower s term lead).(nstate.vote) = W64 0.
Proof. intros Hne. rewrite /become_follower /=. rewrite decide_False //. Qed.
```

Then `rewrite /vote_hist_ok (become_follower_vote_ne _ _ _ Hne)` leaves one
`decide` and the rest goes through. The same trick — name the projection,
rewrite it before `simpl` gets there — is what keeps `word.add s.term 1`
folded as `t'` in the `step_campaign` case, where otherwise `simpl` unfolds
the record and `lia` sees two unrelated atoms.

## `/=` collapses `[x] ++ l`, so the second `big_sepL_app` has nothing to match

`rewrite /send_msgs /=` on an outbox of the shape
`s.(nstate.outbox) ++ ([m] ++ (f <$> peers))` leaves
`s.(nstate.outbox) ++ (m :: (f <$> peers))`. The first `big_sepL_app` fires
on the outer `++`; the second has no `++` left. Use `big_sepL_cons` for the
inner split (and then the head goal is `Φ m`, not a singleton `big_sepL`, so
drop the `big_sepL_singleton`).

## Two small name traps: `Forall_forall` and `big_sepL_singleton`

- **`Forall_forall` resolves to Rocq's `List` version**, whose membership is
  `In` and not stdpp's `∈`, so `rewrite Forall_forall in H` then
  `eapply list_elem_of_lookup_2` fails to unify. When you are coming from a
  `l !! k = Some x` (which is what `big_sepL_intro` hands you), go straight
  there with `Forall_lookup_1 _ _ _ _ H Hk`.
- **`iDestruct (big_sepL_singleton with "H") as "#Hm"` leaves `P ∗ emp`**,
  not `P`. Applying a wand to it then fails with a baffling
  `iSpecialize: cannot instantiate (P -∗ Q) with (P ∗ emp) ∗ emp`. Destruct
  the conjunction instead: `iDestruct "H" as "[#Hm _]"`.

## A `True` goal in the proof mode: `done`, not `apply bi.True_intro`

`apply` does not see through `envs_entails`, so `apply bi.True_intro` fails
with a type error naming the whole environment. Iris's `done` closes
`envs_entails Δ True` directly, including when the `True` is under a `match`
that has just reduced to it (which is how `leader_wit`'s non-leader case
arrives).

## Working at a record-indexed predicate (`own_raftLog l ls`), 2026-09-23

- **Destruct the state, then reduce only its projections.** The `raftLog`
  proofs start `destruct ls as [prev sents uents lcm lap];
  logstate_simpl`. `logstate_simpl` is `cbn` restricted to the
  five `logstate` projections (never `simpl in *`). A spec called at
  `logstate.mk prev …` returns facts about `(logstate.mk prev …).(logstate.prev)`,
  which `lia`/`word` treat as a different atom from `prev`: run
  `logstate_simpl` (or `cbn [logstate.prev …] in H`) after the call.
- **A state premise cannot be given as `eq_refl` with the state left to
  unification.** (Historical: the example is the `logstate.page = None`
  premise, which went on 2026-09-29 with `logstate.page`.)
  `wp_raftLog__lastIndex _ _ eq_refl` fails: `eq_refl` has
  to be elaborated against `logstate.page ?ls = None`, and a projection of
  an evar does not unify with `None`. Give the state:
  `wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap None) eq_refl`,
  or a hypothesis `Hls : ls.(logstate.page) = None`, which fixes `?ls`.
  Where the resource should fix the state instead, make the premise a
  *wand* premise: `own_raftLog_unless_close` is
  `… own_raftLog l ls -∗ ⌜ls.page = None⌝ -∗ …`, called
  `with "Hlog [//]"`.
- **`iNamed` does not unfold a plain definition.** It went through
  `own_raftLog_at` because that began with `∃ lv`; `own_raftLog_core` is a
  bare `∗`-chain and `iNamed "Hcore"` left it whole ("HisStorage not
  found" later). `iEval (rewrite /own_raftLog_core /=) in "Hcore"` first.
- **`iDestruct (own_raftLog_unfold with "Hlog")` did not use the lemma's
  right-hand side**: with a `⊣⊢` lemma it unfolded `own_raftLog` itself,
  leaving `own_raftLog`'s own names and projections of the literal. Open
  with `iNamed "Hlog"`; the lemma is still the right way to *close*
  (`iApply own_raftLog_unfold`).
- **A struct sealed inside a predicate stops `wp_apply … as`'s automatic
  `wp_auto`.** After `unstable.mustCheckOutOfBounds` returned
  `own_unstable`, the field reads that follow were not stepped; an explicit
  `iNamed "Hun". wp_auto.` was needed.

## Working against the sealed `own_raft_phys` (2026-09-24)

`own_raft_phys` is sealed; the interface is the last section of
`election_proof/inv_raft_phys.v` (decisions.md, "Program proofs do not
unfold `own_raft_phys`").  What bit while converting the proofs to it:

- **`wp_auto` stops in front of every raft-field access**, and a `wp_auto`
  with nothing left to do *fails* ("Failed to progress") -- e.g. right after
  a `wp_apply … as`, which already ran it.  Write `try wp_auto` where a
  load used to be absorbed.
- **A field load in function position is not found by `wp_apply`.**
  `r.step(r, m)` is `![stepFunc] #(r.[…, "step"]) #r #m`, and
  `wp_apply (wp_raft_load_step with "Hphys")` fails with "iApply: cannot
  apply"; so does any field lemma there.  Bind by hand:
  `wp_bind (![raft.stepFunc] _)%E; iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys"`
  (`wp_load_step` in `proof_raft__Step_MsgVoteResp.v`).
- **Passing `Hlent` positionally pins the state.**
  `own_raft_phys_tracker _ _ _ _ Hlent` takes `s` from `Hlent`'s type and then
  fails against a `Hphys` at a setter chain over `s`.  Leave the premise
  open: `iDestruct (own_raft_phys_tracker with "Hphys") as …; first exact Hlent.`
  (A premise about `s` *is* accepted at `s` updated at other fields, by
  conversion; it is the pinning that hurts.)
- **`own_raft_phys_log` consumes `Hphys`**, so code that loads `r.raftLog`
  again while the log is open cannot use it; lend instead
  (`own_raft_phys_lend`), since at `s <| lent := Some tv |>` `Hphys` still
  serves field loads.
- **The tracker accessor gives the state back at `s <| votes := votes' |>`**
  even when nothing changed; use `own_raft_phys_tracker_same` for a
  read-only use or a split/re-seal repeated inside a `Visit` closure, or the
  setters pile up.
- **Relating a run of stores to the state a spec names**: `own_raft_phys_eq`
  with `by destruct s` (or `reflexivity`).  Cheap.  Leaving it to unification
  inside `iFrame`, or `simpl` on a state with `functions …` in it, is not.
- **`wp_auto` reduces the value a field lemma returns**: after a load at
  `become_follower s t l`, `r.Term` shows up as `t`, not as a projection,
  so a `rewrite` with a projection lemma finds nothing to rewrite.

Writing a triple for a *single* heap access (the field lemmas themselves):

- **`wp_auto`'s load/store step does not strip the later off `HΦ`**, so
  after `wp_auto` the goal `Φ v` cannot be closed from `▷ (… -∗ Φ v)`.
  Apply the primitive `wp_load`/`wp_store` with `wp_apply` instead (it
  introduces the later); `wp_load_access`/`wp_store_access` in
  `inv_raft_phys.v` do that through any `AccessStrict` instance.
- **`e1 <-[t] e2` is an expression pair**; after one pure step the goal is
  `GoStore t (#l, #v)%V`, a value pair, which is what the store lemmas are
  stated at.
- **Unsealing a 33-field struct and re-framing it field by field costs
  ~40s** (`iNamed`, then `iFrame "∗%"`).  Destructure positionally and keep
  the untouched fields as one hypothesis: ~6s (`split_field_proof`).
- **`wp_apply` sometimes introduces the postcondition itself** (e.g.
  `wp_slice_literal` when its precondition is trivial, `wp_Logger__logf`'s
  `True`), and an `as` pattern then fails with "iIntro: nothing to
  introduce" -- a failure `try` around the whole step does not catch, since
  it comes from inside `wp_apply`.  `wp_raft_log` tolerates both shapes.

## Proving a long function with sequential `if`s (`newRaft`), 2026-09-24

- **Join the arms of an `if` with `wp_bind` + `wp_wand`, or the rest of the
  proof runs once per path.** `newRaft` has `if !IsEmptyHardState(hs)`,
  then `if c.Applied > 0`, then a loop. Case-splitting each one and carrying
  on under `all:` gave 8 copies of a goal holding the whole raft struct, and
  rocq-warm discarded the session at its 4.2 GB ceiling. Instead:

      wp_bind (if: _ then _ else _)%E.
      iApply (wp_wand _ _ _ (λ v, ⌜ v = execute_val ⌝ ∗ R)%I with "[…]").
      { (* both arms, each ending at the same R *) }
      iIntros (v) "(-> & …)". try wp_auto.

  `e1 ;;; e2` is `exception_seq (λ, e2) e1`, so the `if` is in evaluation
  position and `wp_bind` finds it; each arm ends in `do: …`, i.e.
  `execute_val`. **Pass the local-variable points-tos the arm reads**
  (`hs_ptr ↦ hs`, `r_ptr ↦ r`, …) into the `with "[…]"` and back out
  through `R`: left behind, `wp_auto` silently fails to step the arm's
  `let: "$a0" := ![T] "x"`.
- **`iNamed "Hphys"` stops silently at a name clash.** A precondition
  introduced as `"[Hphys Hlog]"` made `iNamed` stop at `own_raft_phys`'s own
  `"Hlog"` conjunct, leaving every later conjunct (`%Hlogp`, …) packed; the
  symptom is "The variable Hlogp was not found" several lines on. Keep
  caller-side names disjoint from `own_raft_phys`'s (`Hr`, `Htrk`, `Hlog`,
  `Hmsgs…`, `Hmisc`, `Hlogger`, and the `%H…` facts).
- **A state premise at a `set`-bound state wants `ltac:(done)`, not
  `eq_refl`.** `(s0 <| nstate.lent := Some tv' |>).(nstate.lent) = Some tv'`
  with `s0` a `set` local: `eq_refl` and `ltac:(reflexivity)` both fail to
  unify through the record update; `done` works.
- **A `w64` equation is invisible to `lia`.** With
  `Hcm2 : lv2.committed' = lv.committed'` in context, `lia` treats
  `uint.Z lv2.committed'` and `uint.Z lv.committed'` as unrelated atoms;
  `rewrite Hcm2 in H` first. And a `w64` *goal* such as
  `word.sub fi (W64 1) = prev.index` needs `apply word.unsigned_inj; word`.
- **A goal and `HΦ` that print identically may still not unify** (`Φ (# cs)`
  for a returned `raftpb.ConfState.t`, in `switchToConfig`): the `#`
  instances differ. `iSpecialize ("HΦ" $! cs xs with "[…]"); iExactEq "HΦ";
  reflexivity` goes through.
- **`wp_log` does not fit a log call whose arguments include a converted
  struct** (`switchToConfig`'s `Infof(..., r.trk.Config)`): its
  `iIntros "% [? _]"` fails with "nothing to introduce". Spell it out:
  `wp_apply wp_slice_literal. iSplitR; first done. iIntros (?) "[? _]".
  try wp_auto. rewrite Hlok. try wp_auto. wp_apply (wp_Logger__logf with
  "Hlogger"); first solve_log_method.` Note no `as "_"` on the last call.
- **`"Cannot find witness"` is `lia`'s (and `word`'s) failure message**, not
  an existential's. When it appears after `iFrame "∗#%"; iPureIntro; …; lia`,
  the arithmetic is missing a fact -- often a bound thrown away as `_`
  (`own_slice_len`'s `0 ≤ len`).

## Holding things read-only, and borrowing out of the struct without a loan (2026-09-29)

- **Name a persistent conjunct spatially** (`"Huents" ∷ … ↦*□ uents`, not
  `"#Huents"`) when the predicate is opened and re-sealed repeatedly. With
  `#` the hypothesis survives the re-seal in the □ context, so the next
  `iNamed` fails with `"Huents" not fresh`, and `iFrame "∗"` no longer
  frames it (`iFrame "∗#"` would). A persistent assertion is happy in the
  spatial context.
- **`iMod (own_slice_persist …)` needs a WP (or update) goal.** After a
  `wp_apply … as` whose continuation is only pure steps, the goal is
  already `Φ v` and there is no modality to eliminate. Put `iApply
  wp_fupd` *before* the `wp_apply`, persist, then `iModIntro`
  (`proof_raftLog__slice.v`, the `extend` exits).
- **A lemma whose premises are Coq hypotheses takes its state from
  them, not from the hypothesis it is applied to.** `own_raft_phys_pr …
  Hlk Hpvs with "Hphys"` with `Hlk : s.(progress) !! to = Some pr` fixes
  the state to `s`, and fails on `"Hphys" : own_raft_phys … (send_msgs s
  ms)` although the lookup is true there too. State such premises as pure
  wands (`own_raft_phys … s -∗ ⌜ s.(progress) !! to = Some pr ⌝ -∗ …`)
  and apply with `"Hphys [//] [//]"`: the state comes from `"Hphys"`, and
  `done` closes the lookups by conversion (`own_raft_phys_pr` and its
  variants in `inv_raft_phys.v`, used by `maybeSendAppend`).
- **A section variable is the lemma's first argument.** A `Local Lemma`
  in a section with `Context (cfg : gset w64)` takes `cfg` first, so a
  positional use needs one more `_` than its statement shows.
- **`s ↦*{dq} []` says nothing about `dq`.** A nil slice satisfies it
  with no resource at all, and an empty array points-to is free at any
  fraction. So a lemma that turns fresh, fully-owned elements into
  `↦*{dq}` needs `✓dq` as a premise, even though the caller "owns" `s`:
  `wp_slice_append_dfrac` takes `⌜✓dq_s⌝` for this reason.

## `Add Zify` registrations vanish at `End Section` and need an `Import`

Two silent failure modes met while writing `src/Helpers/Word/ZifyWord.v`:

- An `Add Zify InjTyp/UnOp/BinOp/BinRel …` inside a `Section` is dropped
  at `End Section`, with no warning; `zify` then treats the terms as atoms
  and `lia` fails with "Cannot find witness". Declare them at top level.
- The registrations are import-scoped, like `#[export]` instances: a file
  that only `Require`s the one that made them, or that imports a file which
  merely `Import`ed it, does not see them. `Automation.v` therefore
  `Require Export`s `ZifyWord`.

Both bit in a `.vos` build, where a `Local Lemma … Proof. lia. Qed.` smoke
test is not run; check with `Show Zify InjTyp.` from another file.
