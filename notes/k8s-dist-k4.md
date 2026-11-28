# k8s-dist K4: is `SharedModel`'s full mode complete? (paper proof, 2026-11-27)

Stage K4 of `notes/k8s-dist-lean-plan.md` §4, session K4-1, branch `k8s-dist-k4/2026-11-27`. The
question decides one cluster or two (plan §1.3 #1): K8 will prove that the store's real history on the
shared cluster linearizes in a **semantic** model (below); the porcupine check that panics is
`SharedModel`'s full mode (`examples/k8s/dist/storecopy/export.go`); K4 must bridge them.

## Verdict

**Full mode is complete on every history but one shape, and that shape has a one-line Go fix.**

- The argument the plan names (a pending write moves down to one above the greatest revision named
  below it) holds, with one more ingredient: the moved write's object carries the moved revision, so
  the search's configurations equal the cluster's only **up to a renaming of revisions no answer
  shows** (§3). Its revision-number core is proved in Lean (`SharedPlace.lean`, §5).
- **The gap (a counterexample).** `target` gives a watch only its events' greatest revision. A
  watch-list (`SendInit = 2`) whose answer ends before its initial-events-end bookmark, with at least
  one event, is accepted by `Model`'s check (`initialPrefixOkL`, `watchOk`'s `initialPrefixOk`) only at
  a configuration whose revision is at least the request's `max(MinRV, 1)`, and `target` does not move
  there. Concrete history (seeds at revisions 2 and 3, `SeededAt(2, 3)`), one operation:

  ```
  Input{Kind: KWatch, WKey: "/objs/", Recursive: true, MinRV: "10", SendInit: 2, Bookmarks: true,
        Match: MNotOlderThan}
  Output{WEvents: [ADDED ns-1/pod-1 (Value "x", RV 2)]}
  ```

  It linearizes in the semantic model (foreign revisions 4..10, then the watch: the store at 10 has
  pod-1 at 2 and pod-2 at 3; the answer is a prefix of its initial events). `SharedModel` answers
  Illegal in all three modes (run 2026-11-27, a scratch test in `storecopy`, not committed); with
  `MinRV: "3"`, or with a Create answering revision 12 before the watch, all three accept.
  Real k8s: the etcd3 watcher syncs a watch-list at an explicit resource version at exactly that
  revision, refusing one above the current; the answer ends before the bookmark when the consumer's
  500 ms timer or 200-event cap ends it (`consume`).
- **Not reached by the driver's generator**, but not excluded by the theorem's hypotheses:
  `genWatchFrom` never gives a watch-list a future resource version (`m == 6` redrawn), so its
  `MinRV` is at most a revision an earlier answer of the same client showed, and every shown revision
  is at most the search's configuration's from then on. Using that in K8 would need a real-time,
  per-client premise on the history. **Fix instead (G7, a Go change for K9's session):** in
  `target`'s watch arm, for `in.SendInit == 2` with at least one non-Error event, return
  `max(t, max(req, 1))` (`req` = `parseRV(in.MinRV)`). It is the least revision the check needs, so it
  costs no completeness; with a bookmark it changes nothing (`brv ≥ req` is checked). Soundness is
  untouched (it only moves foreign revisions).
- So: **one cluster stays feasible.** With G7, full mode is complete for every history (the theorem
  below); without it, K8 must carry the generator premise.

## 1. The semantic model (what K8 proves the real history linearizes in)

`kSpec h0` (`Proof/.../k8s/etcd3/KWatch.lean:230`, the driver's `Model` as linkv's `PendSpec` over
`HSt` = store + history) with one more silent step, **foreign**: `⟨st, hist⟩ ↦ ⟨st', hist ++ [st']⟩`
with `st' = {st with rv := st.rv + 1}` (items unchanged). `PReach` = pending writes applying (at the
current store, `kstepL`) and foreign steps, any number, in any order; `PStep` unchanged (`ok`, `errW`,
`errR`, `obs` with `watchOkL`). A compacted error is a failed read or a dropped Error event, so
compaction needs no rule. The Lean definition is K4-2's first item (§6).

## 2. The full mode, as a search

Per operation `(in, out)` and configuration `c` (`SharedModel.Step`, mode `Full`): `settle` (each
pending write, in any order, is dropped if it fails on the store, or lands at one of
`landings(revs, d, w, _, true, in, out)` — `d` skipped to `l - 1`, then `mstep`), then `skipTo(target(in,
out, rv))`, then `Model`'s step. Anchors `A` = every revision any input or output of the whole history
names (`HistoryRevs`); full landings = `rv + 1` and every `r > rv + 1` among the key's shown revisions,
the answer's own one, and `a, a + 1` for each anchor `a ≥ rv`.

## 3. The argument

Fix a history and a semantic linearization of it. Build the search's run alongside, operation by
operation, keeping a relation between the search's configuration `s` and the cluster's `c`:

- **(R1)** a strictly increasing **renaming** `ρ : [0, s.rv] → [0, c.rv]` with `ρ(x) ≥ x`, `ρ(x) = x`
  for every anchor in its domain, and no anchor in `(x, ρ(x)]`;
- **(R2)** `c`'s items are `s`'s with every object's resource version renamed by `ρ` (every stored
  object's revision is in `ρ`'s domain: it is the revision of the write that made it, or a seed's);
  the pending lists are equal up to order;
- **(R3)** for every `y ≤ c.rv`, the cluster's store at `y` is the search's store at `σ(y) = max{x |
  ρ(x) ≤ y}`, renamed (the cluster's revisions between two images are foreign);
- so `s.rv ≤ ρ(s.rv) ≤ c.rv`.

**Settle.** The cluster's pending writes before the operation apply at increasing revisions `R₁ < … <
R_k` (foreign steps between). The search applies them in the same order at `L_i = canonL A L_{i-1}
R_i` (`L_0 = s.rv`): `R_i` itself if it is an anchor, else one above `max(L_{i-1}, greatest anchor <
R_i)`. `canonL_mem`: `L_i` is a full landing. `canonL_le`: `L_{i-1} < L_i ≤ R_i`. `canonL_gap`: no
anchor in `[L_i, R_i)`, so extending `ρ` by `L_i ↦ R_i` keeps (R1). The write's effect: `kstepL` reads
keys, preconditions (`PreRV` against the object's revision: `PreRV` is an anchor, `ρ` fixes anchors
and is injective, so equality is preserved), the node (rejection), `sameObjL` (no revision) and the
`canon` flag; the new object's revision is `L_i` against `R_i = ρ(L_i)`. So (R2) holds. A write that
fails on the store (no effect) is dropped by both.

**Target.** The operation's answer needs the cluster at a revision `≥ t` exactly when `t` is
`target`'s (a write at `out.RV - 1`, a not-found's and a current List's revision, a past List's or a
Get's `MinRV`, the greatest event or bookmark revision of a watch) **— and, for the gap above, a
watch-list's `MinRV`**. Each `t` is an anchor or one less than one; `t ≤ c.rv`. The search skips to
`max(s.rv, t)`, extending `ρ` by the identity, which (R1) allows: if `s.rv`'s image is above `t`, no
skip; else every image so far is `≤ t` (an image `R_i > t` would put the anchor `t` or `t + 1` in
`(L_i, R_i]`).

**Step.** Each part of `Model`'s step against the related configuration:

- *exact revisions* (a write answering `out.RV`, a not-found's `ErrRV`, a current List's `ListRV`):
  the cluster is at that revision; the search is at most there, skipped to it, so at it;
- *upper bounds* (`ETooLarge`: `rv < MinRV`): `s.rv ≤ c.rv`;
- *a past List* at the anchor `req`: `σ(req) = req` (skipped there if beyond `s.rv`), the same store,
  renamed; its items' revisions are shown, so anchors, so unrenamed: the same answer;
- *a Get, a write's answer, a precondition message*: an object's revision shown is an anchor, so `ρ`
  maps it to itself;
- *a watch* (`watchOkL`): every bound it compares a revision against is an anchor or one after one
  (an event's or bookmark's revision and the next, `req + 1`); `canonL_cut`: such a `v` is `≤ L_i` iff
  `≤ R_i`, so a range `[lo, hi)` holds the same changes in both histories (foreign revisions hold
  none), and the events of the changes in range are the answer's, so their revisions are anchors,
  unrenamed. `initialPrefixOkL`'s existential revision `r ∈ [max(req, 1), rv]`: the cluster's store
  at `r` is the search's at `σ(r) ≥ req` (`req` an anchor) and `≤ s.rv`; the first `|evs|` initial
  events are shown (anchors), the rest only counted. **This is where the gap is**: `σ(r) ≤ s.rv` needs
  `s.rv ≥ req`, which only G7's target gives.
- a failed write becomes pending in both; a failed read changes nothing.

So the search's step from `s` holds a configuration related to the cluster's next one: by induction,
every step's set is non-empty, and porcupine (whose search is exhaustive over orders) finds the
linearization. The modes' hash-consing, `cfgSet` deduplication, `stepIdx`'s memo and `watchOkIdx` are
K9's (equal to `Model`'s step).

## 4. One cluster or two

- **One cluster (recommended, still feasible).** K4's theorem: under G7, every history that
  linearizes in the semantic model passes the full mode. K8 proves the linearization (the store's
  invariant over the shared KV, ghost linearization into the semantic model); K9 proves the Go code
  equals the Lean search (§2); K4-2 proves §3 in Lean.
- **Two clusters** would not be needed for completeness. If G7 is refused, the alternative is the
  generator premise (watch-lists' `MinRV` at most a revision the client saw), carried by K8 from the
  per-client caches.

## 5. In Lean now

`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/dist/SharedPlace.lean` (pure, no imports):
`landingsFull` (the full mode's `landings`), `canonL`, and `canonL_mem`, `canonL_le`, `canonL_gap`,
`canonL_cut`, `canonAll_ok` (a settle phase). No axiom, no `sorry`.

## 6. K4-2 and after: the Lean of §3

1. `SharedSem.lean`: the semantic model (§1) as `kSpec`'s steps plus `foreign`, over `HSt`.
2. `SharedSearch.lean`: `targetL` (with G7), `landingsL` (= `landingsFull` over `HistoryRevs`'
   anchors), `settleL` (as a relation: a list of landings), `sharedStepL`.
3. The renaming: `renObj ρ`, `renSt ρ`, and `kstepL (renSt ρ st) = renamed (kstepL st)`, `mlistL`,
   `watchOkL` invariance under (R1)-(R3) (the bulk: `changeAtL`, `evAtL`, `eventsInL`,
   `reliableOkL`, `initialPrefixOkL` against `canonL_cut`).
4. The theorem: a linearization in the semantic model gives a run of the search, step by step.
The imports are `KWatch.lean`'s cone (pure defs, but it imports the Goose translation's types: build on
fk-lean1).

## Handoff K4-2 (2026-11-27, branch `k8s-dist-k4/2026-11-27`)

K4-2 started §6 in Lean: the model and the search as definitions, the statement, the first layer of the
renaming. **Build state (fk-lean1, WIP commit `94b6edf709`):** `SharedSem.lean` compiles;
`SharedSearch.lean` had one error, `skipToL_rv` (line 158, `omega`: the `t ≤ rv` case), fixed afterwards
by a case split on `skipToL_le` but **not rebuilt**; `SharedRename.lean` was **never compiled** (it waits
on `SharedSearch`): expect small fixes there (`renItem_zItem`'s `simp`, `preOkL_ren`'s `word` steps and
final `simp`/`congr`, `setStepI_ren`'s case simps, `changeAtL_self`'s `simp only` lemma names). First step
of K4-3: build `Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedRename` on fk-lean1 (the
branch's worktree there is seeded) and fix. **Not proved yet: the invariance of `mstepL`/`mlistL`/`watchOkL` and the theorem.**

**In Lean** (`Proof/.../examples/k8s/dist/`, pure, over `KSteps.lean`'s cone; no axiom, no `sorry`):

- `SharedSem.lean`: `foreignL` (a foreign revision), `SSilent`/`SReach` (`kSpec`'s `PSilent` or a
  foreign step), `SRun h0 c ops c'` (a run of the semantic model: per operation, silent steps then
  `kSpec`'s `PStep` with `ansOf y`). Every step is taken from a configuration with `rv + 1 < 2^64`
  (`NoWrap`): the model's revisions are words, and K8 must show the cluster's never wrap.
- `SharedSearch.lean`: `skipToL` (foreign steps), `targetL` (Go's `target` with G7, as in
  `k8s-dist-go/2026-11-27` `152e1a4634`), `SettleL A` (settle's configurations, landings
  `landingsFull A [] [] rv`: a subset of the Go landings, so the Go search's configurations include
  these), `SearchStep`, `SearchRun`; `OpAnchors`/`AnchorsOk` (the revisions an operation names, as
  `HistoryRevs` collects them, plus `0 ∈ A`, which adds no landing); and **`FullComplete : Prop`**, the
  theorem's statement (seeded `h0` with `hist.length = rv` and every revision up to the seeds' an anchor;
  `AnchorsOk A ops`; `SRun h0 ⟨h0, []⟩ ops c'` → `SearchRun A ⟨h0, []⟩ ops`). `skipToL_le`,
  `skipToL_items`, `skipToL_rv`.
- `SharedRename.lean`: `renObj ρ`, `renItem ρ`; `lookupL_ren`, `delItemL_ren`, `setItemL_ren`
  (store helpers commute with the renaming), `selOkL_ren`, `sameObjL_ren`, `updatedL_ren`, `preOkL_ren`
  (preconditions invariant when `ρ` maps the object's revision to the precondition's iff it is it),
  `preMsgL_ren_uid`, `changeAtL_self`.

**A correction to §3's (R1).** `ρ` cannot be a total map on `[0, s.rv]`: from `s.rv = 5` with
`ρ(5) = 9` (no anchor in `(5, 9]`), a write the cluster put at the anchor `R = 10` lands at `canonL = 10`,
and the search's skipped revisions `6..9` have no image in `(9, 10)`. The revisions in between are
foreign on both sides, and nothing reads them by name, so the relation should rename only the **write
revisions**. Proposed relation (search `s`, cluster `c`), to replace (R1)-(R3) in the Lean proof:

- the stores' versions: `vs s`/`vs c` (the item lists after each write, in order) are related pointwise
  by `map (renItem ρ)`, and `cnt s r`/`cnt c r` (the number of writes at or before `r`) satisfy
  `cnt s v = cnt c v` for every anchor `v` and one after an anchor, and `cnt c r ≤ cnt s r` for `r ≤ s.rv`
  (the search's writes land no later);
- `ρ` on the search's write revisions: strictly increasing, `w ≤ ρ w`, and `v ≤ w ↔ v ≤ ρ w` for `v` an
  anchor or one after (`canonL_cut`); identity on revisions up to the seeds'; injective on every
  revision an object of a stored version carries (for `changeAtL`'s `p = q` test);
- `s.rv ≤ c.rv`; pending lists equal up to order.

`initialPrefixOkL`'s `r ∈ [max(req,1), c.rv]` then maps to a search revision in `[max(req,1), s.rv]` by
a discrete intermediate-value step on `cnt s` (it moves by at most one per revision), which needs
`s.rv ≥ req`: G7's target.

**Left (K4-3 on):** (1) `mstepL`'s invariance (`mcreateL`/`mdeleteL`/`mupdateL`/`mgetL`, over the
helpers above; the new object's revision `L` against `ρ L = R`); (2) the history relation above, its
preservation by a landed write, a foreign step and `skipToL`; (3) `mlistL` (past reads at an anchor:
`histN` at a cut revision); (4) `watchOkL`: `changeAtL` of renamed stores, `evAtL`/`eventsInL` over a
range with cut bounds, `reliableOkL`, `initialPrefixOkL`, `bookmarksOkL` (unchanged: the answer's own
events); (5) settle: the cluster's pending writes before an operation, in order, as `SettleL` steps at
`canonAll`'s landings; (6) `FullComplete`'s proof by induction on `SRun`. Open check: `OpAnchors`
anchors a successful write's `RV` only with a name (Go's `HistoryRevs`), but `targetL` uses `RV - 1` for
every successful write; if a nameless successful write answer can occur, (1) needs a case.

## K4-3: more gaps (counterexamples), G8, G9 and G10 (2026-11-27)

K4-3 settled the handoff's open question and found three more histories that linearize in the semantic
model and that `FullComplete`, as K4-2 stated it, refuses. Both are outside the driver's generator (it
sends writes with `MinRV ""` and names every object), as G7's was; both are fixed by a one-line Go
change, and the Lean statement now carries both fixes, **explicitly** (not a weakening: the search and
the anchors change, so K9 must match them in Go).

- **G8: a write's target must not need its `MinRV` to parse.** Go's `target` (and K4-2's `targetL`)
  parses `in.MinRV` before the kind switch and returns 0 if it fails; `mcreate`/`mdelete`/`mupdate`
  never read `MinRV`. History (seeds at 2, 3; `h0.st.rv = 3`), one operation:
  `Input{Kind: KCreate, Key: "ns/a", MinRV: "a", ...}`, `Output{Err: ENone, Name: "a", RV: 10, ...}`.
  The semantic model: foreign revisions 4..9, the create at 10. The search: no pending write, target 0,
  the create at 4: Illegal. **Fix:** parse `MinRV` only in the List and Get arms (`targetL` now does).
- **G9: a successful answer's revision is an anchor with or without a name.** `HistoryRevs` anchors
  `out.RV` only when `out.Name != ""`; an object whose key has no `/`-suffix (`"ns/"`, `splitKey` gives
  name `""`) is stored and shown with an empty name. History (same seeds): (1) `Create "ns/"` answering
  `EOther` (pending); (2) `Create "ns/b"` answering `RV 10`; (3) `Get "ns/"` answering the object with
  `Name ""`, `RV 7`. Semantic model: the pending create at 7 (foreign 4..6), foreign 8, 9, (2) at 10, (3)
  reads it at 7. Search (Go full mode too): (1)'s landings are `{rv+1}`, the anchors `≥ rv` and the next
  ones, the key's shown revisions (`byKey["ns/"]` is empty: (3)'s object has no name) and the answer's
  own revision for the same key (only in (3)'s step, after (2) moved the search to 10): never 7.
  Illegal. (Lean's `landingsFull` has no answer's-own landing: the 2-operation history (1), (3) already
  fails there.) **Fix:** drop `out.Name != ""` (a zero `RV` is not anchored anyway); `OpAnchors` now
  anchors `y.RV'` of every successful non-watch answer.
- **G10: every kind `mstep` answers with `mget` needs its `MinRV`.** `mstep` sends every kind but
  create, delete and update to `mget` (which refuses a `MinRV` above the store's revision), but
  `target` gives `req` only to `KGet`; any other such kind (`Kind` is a `uint64`: 6, 7, ...) falls to the
  write arm. History (same seeds): `Input{Kind: 7, Key: <a seeded key>, MinRV: rvBytes(10)}`,
  `Output{Err: ENone, <the seed object at RV 2>}`. Semantic model: foreign 4..10, `mget` answers it.
  Search: target 0 (the answer's `RV` 2 is below 3), `mget` at 3 answers `ETooLarge`: Illegal. **Fix:**
  the write arm only for `KCreate`, `KDelete`, `KUpdate`; every other kind (`KGet` included) `req`
  (`targetL` now does).
- **The open question** (a successful write answered without a name): with G8, `targetL` of a
  successful write answering `RV > rv` is `RV - 1`, the cluster's revision before it, whether or not
  `RV` is an anchor; the step's write is at `RV` on both sides (`ρ` the identity there). No case needed.

Go side (for K9's session, branch `k8s-dist-go/2026-11-27`): G8, G9 and G10 in `examples/k8s/etcd3/export.go`
(`target`, `HistoryRevs`), with the two histories above as tests.

## Handoff K4-3 (2026-11-27, branch `k8s-dist-k4/2026-11-27`)

**Built** (fk-lean1, no axiom, no `sorry`): `SharedSem`, `SharedSearch` (with G8, G10; `OpAnchors` with
G9), `SharedRename`. New in `SharedRename`: `CutW A ρ w` (the cut property: `v ≤ w ↔ v ≤ ρ w` and
`v + 1 ≤ w ↔ v + 1 ≤ ρ w` for every anchor `v`), `CutW.fix` (an image that is an anchor is not renamed),
`CutW.eq_iff` (the image is the anchor `r` iff `w` is: the `PreRV` test), `renObj_fix` (a shown object
is not renamed), `renObj_setRV`, `renObj_zObj`, `lookupL_mem`; `StepRen` and `WriteRen` (what a write's
step needs of `ρ`: fixes 0, `ρ (a + 1) = b + 1`, no wrap, stored revisions fit, `PreRV` test kept), and
**`mstepL_ren`** (with `mcreateL_ren`, `mdeleteL_ren`, `mupdateL_ren`): on the stores `⟨its, a⟩` and
`⟨its.map (renItem ρ), b⟩`, the results' items stay renamed and both take a revision or neither. This
is the settle step (`a`, `b` = the landing less one on each side) and the step's write (`a = b`).

**`FullComplete` as K4-2 stated it was false** (three counterexamples, G8-G10 above); the statement now
carries the fixes. The Go side must get G8-G10 (K9's session); until then the Lean search is not the
Go one on those histories.

**Left, in order** (the plan of K4-2's handoff, refined):

1. **The step's answer** (`mstepL`'s `.2`): on `⟨its, a⟩` vs `⟨its.map ρ, b⟩` with `a ≤ b`, `y` the
   cluster's answer, `OpAnchors`, and what the target gives (`y.Err = 1 → ErrRV ≤ a`; a write's success
   `y.RV ≤ a + 1`, so `a = b` when it writes; a non-write `MinRV ≤ a` on success), every item's revision
   `CutW`: the search answers `y`. Cases: `existsL`/`rejectedL` equal; `notFoundL` (`a = b`); a
   precondition message (`preMsgL_ren_uid`, else the message's object is anchored: `renObj_fix`); an
   object answer (`y.RV` anchored, G9: `renObj_fix`); a new object (`a = b`, `ρ (a+1) = a+1`).
2. **The history relation** (replacing K4-2's `cnt` form, simpler to use): a list `W` of the search's
   write revisions after the seeds, `ρ` strictly increasing on `[0, h0.rv] ∪ W`, the identity on
   `[0, h0.rv]`, `w ≤ ρ w`, `CutW A ρ w`, `ρ w ≤ c.rv`; `s.rv ≤ c.rv`; both histories one store per
   revision (`hist.length = rv`); for every `x ≤ s.rv`, `y ≤ c.rv` with `∀ w ∈ W, w ≤ x ↔ ρ w ≤ y`,
   `(histN c.hist y).items = (histN s.hist x).items.map (renItem ρ)`; a search revision not in `W`
   (above the seeds) changes no item; every stored object's revision is in `[0, h0.rv] ∪ W`; pending
   lists equal up to order. Preservation: a foreign step on the cluster (`x` unchanged pairs with `y+1`),
   `skipToL` on the search below the cluster's revision, a landed write (`W ++ [L]`, `ρ L = R`, from
   `canonL_gap`/`canonL_cut`, `mstepL_ren`).
3. **`mlistL`**: a past read at the anchor `req`: `x = y = req` satisfy the cut condition, so the stores
   are renamed; the items shown are anchored (`OpAnchors`), so `renObj_fix`. Needs `listLoopL`/`listOutL`
   to commute with `map renItem` (they read keys, selectors and the objects).
4. **`watchOkL`**: `changeAtL` of renamed stores (renaming injective on stored revisions, keys kept) is
   the renamed change at `ρ r`; `evAtL`/`eventsInL` over `[lo, hi)` with `lo`, `hi` anchors or one
   after (the cut condition gives the same writes in range); events shown are anchored (`renObj_fix`);
   `initialPrefixOkL`'s `r ∈ [max(req,1), c.rv]` maps to `max(max(req,1), greatest w ∈ W with ρ w ≤ r)`
   `≤ s.rv` (G7's target gives `req ≤ s.rv`; `1` is an anchor or one after `0`); the initial-events-end
   bookmark's `brv` is an anchor (`x = y = brv`).
5. **Settle**: the cluster's `SReach` before an operation (pending writes landing at `R₁ < … < R_k`,
   foreign steps, reorders) as `SettleL` steps at `canonAll`'s landings (`SharedPlace.lean`), dropping the
   writes that fail on the store.
6. **`FullComplete`** by induction on `SRun`, the relation as the invariant.

A local `etc/lean-check.py` is not usable here (the worktree has no `.lake`); the edit loop K4-3 used is
`/shared/tmp/k4-3/qc.sh FILE` / `err.sh FILE` (copies the file into fk-lean1's worktree of the branch and
runs `lake env lean` on it alone, no lock: the imports must be built there, which a `fklean1-check.sh`
build of the target does).

## Handoff K4-4 (2026-11-27, branch `k8s-dist-k4/2026-11-27`)

Steps 1-3 of K4-3's list are proved, and the first layer of step 4. New files (pure, no axiom, no
`sorry`; each checked with `lake env lean` on fk-lean1 through `/shared/tmp/k4-4/qcc.sh`, which
concatenates the dist files into one scratch module; build of record: see the last line below):

- `SharedAnswer.lean`, **step 1**: `AnsRen` (what the step's answer needs: `ρ` fixes 0 and cuts every
  stored revision; a resource-version precondition is an anchor; `a ≤ b`; from the cluster's answer
  `y`'s anchors, `rvA`/`msgA`; from the target, `nf`/`wr`/`rd`), and **`mstepL_ans_ren`**: on
  `⟨its, a⟩` and `⟨its.map (renItem ρ), b⟩`, `mstepL`'s answers are equal. A "not found" and a new
  object pin `a = b` (`AnsRen.nf_eq`, `new_eq`); shown objects and a precondition's message are fixed
  (`obj_fix`, `msg_fix`). `SharedRename`'s `preOkL_ren`/`WriteRen.pre` now need the precondition's
  revision only when `HasPreRV`.
- `SharedHist.lean`, **step 2**: `PairW n0 ρ W x y` (below the seeds `x = y`; `w ≤ x ↔ ρ w ≤ y` for
  `w ∈ W`), `StoredRv n0 W r` (`r ≤ n0 ∨ r ∈ W`), and **`HRel A n0 ρ W s c`** (the handoff's relation:
  lengths, `histN` at the top is the store, history revisions, `W` in `(n0, s.rv]`, `ρ` identity to
  `n0`, no earlier, at most `c.rv`, strictly increasing, `CutW`; stored revisions; `hist`: paired
  stores renamed; `seed`: the stores up to `n0` equal; `squiet`/`cquiet`: a search revision not in `W`,
  a cluster one no `ρ w`, changes no item). Preservation: `HRel.init` (premises: `hist.length = rv`,
  `hist.getLast? = some st`, every seed item's revision `≤ n0`), `foreign_c`, `foreign_s`, `skipTo`
  (to at most `c.rv`), `write` (`a+1` on the search, `b+1` on the cluster, `extR ρ a b`, `W ++ [a+1]`;
  needs `CutW A (fun _ => b+1) (a+1)`, from `canonL_cut`, or trivial when `a = b`), `stepRen` (both
  stores change or neither, any `a ≤ b`). Helpers: `mstepL_shape`/`mem`/`same`/`changed`,
  `kstepL_nonwrite`, `advanceL_same`/`new`, `HRel.cur`, `stored_cut`, `inj`.
- `SharedList.lean`, **step 3**: `listLoopL_ren`, `listOutL_ok`, `listOutL_ren`, **`mlistL_ren`**
  (`HRel`, answer not `EOther`, `MinRV` and shown items anchored, the target's bound → equal answers).
- `SharedWatchEv.lean`, **step 4, first layer**: `renEv`, `renChg`, `changeAtL_ren` (renaming injective
  on the items), `toEventL_ren` (a deletion's revision renamed with it), **`evAtL_ren`**, `renItem_inj`.

**`FullComplete` needs two more premises on the seeds** (not a counterexample: well-formedness the
proof uses, true of the seeded store, and `RealReplay.simR_init` already takes the first):
`h0.hist.getLast? = some h0.st`, and every item of every store of `h0.hist` has a revision `≤ n0`
(a seed item at a revision a search write takes would be renamed with it). They also give `n0 ≥ 1`
(used below). **Not yet added to `FullComplete`'s statement**: add them with step 6.

**Left, in order:**

4. `watchOkL` (rest). Plan, all designed:
   - `eventsInL`: `eventsInL x c.hist lo yc = (eventsInL x s.hist lo xs).map (renEv ρ)` for `xs`, `yc`
     paired over stored revisions (`∀ r, StoredRv n0 W r → (r < xs ↔ ρ r < yc)`), `lo` paired with
     itself, `lo ≤ xs ≤ s.rv+1`, `lo ≤ yc ≤ c.rv+1`, by induction on `xs + yc`: (a) `yc-1` no image of a
     stored revision: the cluster's event there is none (`cquiet`, `changeAtL_self`; `yc-1 ≤ n0` is
     an image), pair `(xs, yc-1)`; (b) else `xs-1` not stored: none (`squiet`), pair `(xs-1, yc)`;
     (c) else both are `r`, `ρ r` for one stored `r` (monotone both ways), pair `(xs-1, yc-1)`
     (`HRel.inj`), and `evAtL_ren` at `r` (`r < 2` is a seed, both none; `PairW (r-1) (ρ r-1)` and
     `PairW r (ρ r)` hold for stored `r ≤ s.rv`; injectivity from `renItem_inj` + `HRel.inj`). Needs
     `eventsInL x hs lo (n+1) = eventsInL x hs lo n ++ (evAtL x hs n).toList` (`List.range'_append`).
   - `lo`, `hi` of `reliableOkL` are anchors or one after (events/bookmarks `≠ 4` anchored, `req`
     anchored), so paired with themselves (`CutW`); `hi ≤ s.rv + 1` from the target (`evMaxL`); the
     cluster's events equal `evs`, whose objects are anchors: `renEv` fixes them (`renObj_fix`, the
     original revision stored or `W`).
   - `initialPrefixOkL`: cluster `r ∈ [max(req,1), c.rv]`; search `x = r` if `r ≤ n0`, else
     `max(n0, max(req,1), greatest w ∈ W with ρ w ≤ r)` (pair: `CutW` at `req`, `n0 ≥ 1`); `x ≤ s.rv` by
     G7's target; `initialEventsL` of a renamed store is the renamed list, prefix objects anchored.
   - The initial-events-end bookmark: `brv` anchored, `(brv, brv)` paired; `brv ≤ s.rv` (target).
5. Settle (`SettleL` steps at `canonL A s.rv R` for each cluster write at `R`, `HRel.skipTo` then
   `HRel.write`; a write with no effect: `drop`, `HRel.stepRen`; foreign steps: `foreign_c`; pending
   lists equal up to `Perm`, `PSilent.apply`'s `erase` vs `removeAtL`).
6. `FullComplete` by induction on `SRun`: invariant `HRel` + pending `Perm`; per `PStep`: `ok` non-watch
   (target → `AnsRen`/`mlistL_ren`; the write: `mstepL_changed` gives `y.RV = b+1`, so the target puts
   the search at `b`, `HRel.write` with `a = b`), `errW`/`errR` (target 0), `obs` (step 4). Derive
   `AnsRen`'s fields from `OpAnchors` + `targetL` + `skipToL_rv`.

No new G-item this session. Edit loop: `/shared/tmp/k4-4/qcc.sh SharedRename.lean SharedAnswer.lean
SharedHist.lean SharedList.lean SharedWatchEv.lean` (first file whole, the others' bodies appended).

**Build of record** (fk-lean1, `fklean1-check.sh`, target `...k8s.dist.SharedWatchEv`, commit `02ad74a683`):
exit 0, `Build completed successfully (5216 jobs)`, no error; no `sorry` in the dist files (the only
`sorry` warnings are Perennial's generated `internal/sync`, as before).

## Handoff K4-5 (2026-11-28, branch `k8s-dist-k4/2026-11-27`)

Steps 4 and 5 are proved, and step 6 except one lemma. New files (no axiom; edit loop
`/shared/tmp/k4-5/qc1.sh FILE`: copies one file to fk-lean1's worktree of this branch and runs `lake env
lean` on it against the oleans there, seconds per check; remove the copied file there before running
`fklean1-check.sh`, whose checkout an untracked copy of a tracked file would block):

- `SharedWatch.lean`, **step 4** (no `sorry`): `eventsInL_succ`, `evAtL_quiet`; `HRel.ge`, `lt_iff`,
  `le_iff` (the renaming is strictly increasing on stored revisions), `fits`, `pair_stored`,
  `hist_stored`, `evAt_stored`; **`HRel.eventsIn_ren`** (the handoff's induction on `xs + yc`, cases
  (a)-(c)); `changeAtL_objs`, `evAtL_obj`, `HRel.eventsIn_stored` (an event's object carries a stored
  revision); `map_renEv_fix`/`evsEqL_ren` (renamed events equal to anchored ones are those events);
  `AnchorIsh A u` (an anchor or one after), `HRel.anchorIsh_pair`, `anchor_pairW`, `eventsIn_anchor`;
  `evRangeL_ok`; **`HRel.reliableOk`**; `initialEventsL_ren`, `evMaxL_ge`, **`HRel.pair_below`** (the
  handoff's choice of the search revision for `initialPrefixOkL`), **`HRel.initialPrefixOk`**;
  **`HRel.watchOk`**: under `HRel`, `OpAnchors` and the search at the target, the cluster's
  `watchOkL` gives the search's (the bookmark case included).
- `SharedSettle.lean`, **step 5** (no `sorry`): `SettleL.trans`; **`CRel A n0 e g`** (`HRel` for some
  `ρ`, `W`; pending lists `Perm`; every pending input a write with an anchored precondition);
  **`CRel.silent`** (foreign: nothing; reorder: nothing; a pending write with no effect: `drop` at its
  first index, `removeAtL` at `idxOf` is `erase`; one that changes the store: `land` at
  `canonL A e.rv (g.rv+1)`, `HRel.skipTo` to `l-1`, then `HRel.write`, the cut from `canonL_cut`),
  **`CRel.reach`**.
- `SharedComplete.lean`, **step 6** (WIP): `watchOkL_target` (a watch the cluster allows has its target
  at most the cluster's revision), `targetL_err`, **`CRel.op`** (one `SRun` step: `errW`, `errR`, `obs`
  proved; `ok` by `CRel.ok`), **`fullComplete : FullComplete`** (induction on `SRun`; `n0 ≥ 1` from
  `getLast?`). **`CRel.ok` is `sorry`** (commit `3703c678a7`, marked WIP; the only `sorry`).

**Statement change**: `FullComplete` (`SharedSearch.lean`) now takes K4-4's two seed premises,
`h0.hist.getLast? = some h0.st` and `∀ g ∈ h0.hist, ∀ it ∈ g.items, it's revision ≤ h0.st.rv`
(well-formedness of the seeded store the proof uses; not a counterexample). No new G-item.

**Left: `CRel.ok`** (a successful non-watch operation, `y = (kstepL x g.st).2`, `y.Err' ≠ 4`). Plan:
1. *The cluster's answers are bounded* (new lemmas on `mstepL`/`mlistL`, none exist yet): for
   `r ≤ g.rv`, `targetL x y r ≤ g.rv`: a "not found"'s `ErrRV` at most the store's revision; a list's
   past read's revision (else `ETooLarge`) and `ListRV` at most it; a write's `RV` at most `rv + 1`;
   a read's `MinRV` at most it on success (G10). Then `HRel.skipTo` to `T = targetL x y d.rv`, and
   `skipToL_rv`: the search at `max d.rv T`.
2. List (`Kind 4`): `mlistL_ren` (`htgt` from the search at `≥ T`); both stores unchanged.
3. Otherwise `mstepL_ans_ren` with `AnsRen A ρ x s.items s.rv g.rv y`: `zero` (`ρ_id`), `cut`/`fits`
   (`stored_cut`, `HRel.fits`), `pre`, `rvA`, `msgA` (`OpAnchors`), `le` (`HRel.le`), `b_lt`
   (`NoWrap`), `nf`/`wr`/`rd` from the search at `≥ T`; rewrite the cluster's store with `HRel.cur`.
   Non-write: `kstepL_nonwrite` on both. Write with no effect: `stepRen`, `advanceL_same` on both.
   Write that changes the store: `mstepL_changed` gives `y.RV = g.rv + 1`, so `T = g.rv` and the search
   is at `g.rv`; `HRel.write` with `a = b` (the cut is trivial).

**Build of record** (fk-lean1, `fklean1-check.sh`, target `...k8s.dist.SharedComplete`, commit `3703c678a7`):
exit 1, one error, `SharedComplete.lean:159` (`errW`'s anchored precondition: the arguments of
`OpAnchors`'s second field in the other order). Fixed in the next commit (`fun hp r => hanc.2.1 r hp`)
and checked with `lake env lean` against that build's oleans (`qc1.sh`): no error, the only `sorry` is
`CRel.ok`'s. Rebuild `SharedComplete` with `fklean1-check.sh` first thing in K4-6.

## K4-6: `FullComplete` is proved (2026-11-28, branch `k8s-dist-k4/2026-11-27`)

**`fullComplete : FullComplete`** (`SharedComplete.lean`) has no `sorry` and no axiom of this repository:
`#print axioms fullComplete` gives `[propext, Classical.choice, Quot.sound]`. Build of record:
fk-lean1, `fklean1-check.sh`, target `...k8s.dist.SharedComplete`.

**The theorem** (`SharedSearch.lean`): every run of the semantic model (`SRun h0 ⟨h0, []⟩ ops c'`: per
operation, silent steps (a pending write takes effect, the pending list reorders, or a foreign revision
passes), then `kSpec`'s step on the operation's answer; no step from a configuration at revision
`2^64 - 1`) is a run of the full mode's search (`SearchRun A ⟨h0, []⟩ ops`: per operation, `settle` with
the full mode's landings over the anchors `A`, `skipTo` the target, `Model`'s step). Premises:

1. the seeded store `h0`: its history has one store per revision (`h0.hist.length = h0.st.rv`), the last
   its current store, and every item of every stored store carries a revision at most `h0.st.rv` (K4-4's
   two seed premises: well-formedness, true of the seeded store);
2. every revision up to the seed's is an anchor (`∀ v ≤ h0.st.rv, v ∈ A`);
3. `AnchorsOk A ops`: 0 is an anchor, and every revision an operation names is (`OpAnchors`: its
   `MinRV` and `PreRV`; an answer's error and list revisions, a success's object revision, a list's
   items', a watch's events' and bookmarks', a failed precondition's message's object's; Go's
   `HistoryRevs`).

It holds for the search **with G7-G10** (`targetL` and `stepL` as the Go must be changed to: the
watch-list target, a write's target without `MinRV`, the answer's revision anchored with or without a
name, every `mget` kind's `MinRV`); those Go fixes are K9's. No new counterexample in K4-6.

**K4-6's lemmas** (`SharedComplete.lean`): `mstepL_nf`, `mstepL_wr`, `mstepL_rd`, `mlistL_bound`,
`mlistL_nf`, `HRel.items_le`, **`kstepL_target`** (the cluster's answer's target is at most its
revision), `mlistL_err`; **`CRel.ok`** as K4-5's plan: skip the search to the target, the answer by
`mlistL_ren` (a list; a failed one by `mlistL_err`) or `mstepL_ans_ren`, the relation kept by unchanged
stores (`mstepL_shape`, `advanceL_same`) or, for a write that changes the store, `HRel.write` with the
search at the cluster's revision (both answer the next revision, so the cut is trivial).

**Left**: K4 is done. The search side (`SearchRun` is what Go's full mode computes) and K8's link from
the real history to `SRun` are other stages' (`notes/k8s-dist-lean-plan.md`).
