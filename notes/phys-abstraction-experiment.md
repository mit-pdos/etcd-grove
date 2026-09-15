# Sealing `own_raft_phys`: what it actually costs

**Date:** 2026-09-15. **Branch:** `worktree-raft-phys-abstraction`, based on
`3e4d07f3e`. **Artifact:** `new/proof/go_etcd_io/raft/v3_proof/election/exp_phys_sealed.v`.

The question: today every `proof_*.v` on the election path opens
`own_raft_phys` with `iNamed` and re-seals it by hand before each call. Would
an abstraction with access lemmas — never unfolding — be cheaper? The
expectation going in was that it would cost us `wp_auto`, replacing it with
manual lemma application at every program step.

## Answer: `wp_auto` survives. That expectation is wrong.

Perennial already has the mechanism. `new/golang/theory/mem.v:78-98`:

```coq
Class AccessStrict {PROP : bi} (A A' P P' : PROP) :=
  { access_strict : P -∗ A ∗ (A' -∗ P') }.
Class Access {PROP : bi} (A A' P P' : PROP) := { access : P -∗ A ∗ (A' -∗ P') }.
#[global] Instance access_transitive : AccessStrict A A' P P' → Access P P' Q Q' → Access A A' Q Q'.
```

`tac_wp_load` / `tac_wp_store` (`mem.v:104-135`) take
`Access (l ↦ v) (l ↦ v') P P'` and then `envs_lookup i Δ = Some (_, P)`. So
they search the Iris context for **any** hypothesis from which the field
points-to is accessible, chaining through `AccessStrict` transitively. The
generated whole-struct instances
(`new/generatedproof/go_etcd_io/raft/v3.v:1220+`, `raft_access_load_Term` and
friends) are just one client of this.

Register your own instances against the sealed predicate and `wp_auto` steps
field reads and writes straight through it, without ever unfolding.

**Verified, not assumed.** `exp_phys_sealed.v` re-proves `becomeFollower`
against a genuinely sealed predicate (`Program Definition ... := sealed`, so
`unfold` cannot reach it) with no `Axiom` and no `Admitted`. Its
`r.lead := lead` and `r.state := StateFollower` are both done by a bare
`wp_auto`. Checked with `.vok`, which checks proof bodies — **not** `.vos`,
which would have accepted a script that does not run.

**Negative control.** Demote `phys_store_lead` from `#[global] Instance` to a
plain `Lemma` and that same `wp_auto` fails with `Failed to progress`. The
instance is load-bearing; the proof is not passing for some other reason.

## Two constraints the design has to respect

**1. Index by physical field values, not by `s`.** Go tears the abstraction
relation: `becomeFollower` writes `lead`, then `state`. In between, the struct
refines no `nstate.t` at all. So the sealed predicate is

```coq
own_raft_phys_at γ r id term vote lead st votes
own_raft_phys' γ r id s := own_raft_phys_at γ r id s.(term) s.(vote) s.(lead) (state_w64 s.(role)) s.(votes)
```

and a model-relevant write is an `AccessStrict` instance that *moves the
index*. Without the extra indices the intermediate states are inexpressible
and you are forced back to unfolding.

**2. Fields whose value is existential inside the predicate cannot be
`AccessStrict` instances.** The class must hand out a concrete `A`, i.e. name
the old value. `own_raft_phys` says nothing about the `step` and `tick`
closures, nor about which `lok` the logger is. Those need explicit
open/close accessor lemmas the proof invokes by hand:

```coq
phys_step_acc : own_raft_phys_at … -∗ ∃ f, r.[raft.raft.t, "step"] ↦ f ∗ (∀ g, … -∗ own_raft_phys_at …)
```

On the election path that is ~12 write sites: `step` (×3), `tick` (×3),
`electionElapsed`, `heartbeatElapsed`, `pendingConfIndex`, `readOnly`,
`uncommittedSize`, plus `logger` reads.

## The shape of the field traffic

Counted over the 11 election-path functions in `new/code/go_etcd_io/raft/v3.v`
(`StructFieldRef raft "…"` occurrences):

| | |
|---|---|
| field accesses | 150 |
| distinct fields touched | 20 |
| distinct fields **written** | 13 |
| read-only | `checkQuorum`, `electionTimeout`, `id`, `logger`, `preVote`, `raftLog`, `trk` |

Written: `Term`, `Vote`, `lead`, `state` (model-relevant) and
`electionElapsed`, `heartbeatElapsed`, `msgs`, `msgsAfterAppend`,
`pendingConfIndex`, `readOnly`, `step`, `tick`, `uncommittedSize`.
`raft__Step` alone has 50 accesses; `reset` 17.

## The baseline it would replace

From the `proof_*.v` files at `3e4d07f3e`:

| file | lines | unfolds | reseals | abstraction-relation rewrites |
|---|---|---|---|---|
| `proof_raft__becomeFollower.v` | 34 | 2 | 2 | 1 |
| `proof_raft__becomeCandidate.v` | 40 | 2 | 2 | 3 |
| `proof_raft__becomeLeader.v` | 56 | 2 | 2 | 5 |
| `proof_raft__send_vote.v` | 63 | 1 | 2 | 2 |
| `proof_raft__Step.v` | 240 | 4 | 3 | 8 |
| **total** | **433** | **11** | **11** | **19** |

"unfolds" = `iNamed "Hphys"` / `wp_start as "@"`; "reseals" =
`rewrite /own_raft_phys`; "abstraction-relation rewrites" =
`rewrite Hterm` / `Hid` / `Hstate` / `Hlok` / `HnoPreVote` …, which exist only
because the unfolded form hands you `rv.(raft.raft.Term')` plus a *separate*
equation instead of the model value.

Each reseal is ~4 lines of `iAssert` + `iExists (rv <| … |>), msgs, msgsAA, lok`
+ `iFrame "∗#%"`. So roughly 45 of those 433 lines are pure seal/unseal
bookkeeping, plus the 19 rewrites.

## What you gain, concretely

- **The end-of-function reseal disappears.** Instead of naming the updated
  `rv` and re-framing ten resources, the proof just has to land on the right
  index; `iApply "HΦ"` after a `rewrite /become_follower /=`.
- **Reads give you the model value.** `phys_load_Term` hands back
  `s.(nstate.term)`, not `rv.(raft.raft.Term')` + `Hterm`. The 19 rewrites go
  away.
- **Sub-function calls stop needing a re-seal.** The three `becomeX` proofs
  each re-seal purely to call `reset`; with the sealed predicate the
  hypothesis never came apart, so there is nothing to put back.

Cost to build it: 5 `AccessStrict` instances + 3 accessors covered
`becomeFollower`. Full election-path coverage is roughly 10 instances (load and
store for `Term`, `Vote`, `lead`, `state`, plus `id` and the four scope
constants) and ~8 accessors (`step`, `tick`, `logger`, `misc`, `trk`,
`raftLog`, `msgs`, `msgsAfterAppend`). Call it 20 lemmas, ~150 lines, each
about four lines of `phys_open` / `iFrame` / `phys_close`.

### The one-time boilerplate, and the tactic that hides it

Every instance proof opens the struct, hands out one field and rebuilds. The
recombination is fiddly; these two tactics are the whole trick:

```coq
Local Ltac phys_open :=
  constructor; unseal; iIntros "H"; iNamed "H";
  iDestruct (typed_pointsto_not_null with "Hr") as "%Hnn";
  iStructNamed "Hr".

Local Ltac phys_close rv' :=
  iExists rv', _, _, _; iFrame "∗#%";
  first [ iApply typed_pointsto_combine; [done | iFrame]
        | iSplitL; [ iApply typed_pointsto_combine; [done | iFrame]
                   | by iPureIntro ] ].
```

Two gotchas cost real time:

- After `iFrame "∗#%"` the residual goal is `r ↦ rv ∗ ⌜pure⌝` — `iFrame`
  leaves the pure conjunct because after `subst` it is `rv.(f) = rv.(f)`,
  reflexivity, which `iFrame "%"` will not *prove*, only discharge from
  context. Hence the `iSplitL … | by iPureIntro` branch. Plain `done` there
  does **not** work; it must be `by iPureIntro`.
- `∃ f, …` over a closure field needs an explicit type ascription
  (`∃ (f : raft.stepFunc.t)`), or you get `UNDEFINED EVARS … TypedPointsto`.

## Recommendation

The mechanism works and is cheaper than the status quo, but **do not build it
yet.** As of 2026-09-15 `own_raft_phys` is being reshaped on
`worktree-raft-election-refinement`: `γ` is dropped, the two message queues
are abstracted into a single `nstate.outbox`, and `step` loses its `sent`
argument. A 20-lemma surface pinned to the old shape would have to be redone.

That refactor makes the abstraction *more* attractive, not less — a
ghost-free, purely physical `own_raft_phys` has fewer indices to thread. Land
the outbox refactor first, then port this file; the `AccessStrict` finding and
both tactics above carry over unchanged.

## Re-running it

```
make new/proof/go_etcd_io/raft/v3_proof/election/exp_phys_sealed.vok
```

Not reached from `new/should_build.v` — it is a prototype, and CI does not
build it. It has no `Axiom` and no `Admitted` (`reset`'s spec is a
*hypothesis*, `wp_reset'_spec`, so it adds nothing to the trust base), so it
*can* be wired in if it is kept.
