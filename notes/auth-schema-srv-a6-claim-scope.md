# A6.2: a claim law without the batch lock — Scope (2026-11-17)

Stage `auth-schema-srv`, branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. Decided by
etcd-grove-03 (questions.md "A6.2 decided"): option (i), Scope first, notes only, then an independent review before any
Lean. The gap (questions.md "A6.2 STOP"): the auth realization hands out its read contract (`authBackendOk`) in a ghost
update, before it can claim the auth buckets; the claim (`batchLocked_claim`) needs `batchLocked`; an idle unclaimed part
(`rbOwnIn`) has no readers' law; readers do come first (`Recover`, `store.go:399-410`).

**Target law** (backend, `ClaimedLemmas.lean`, replacing `batchLocked_claim` in place: no twin):

```
theorem rbOwnIn_claim (γ P W Pk b) (Sc : List GoString) (r) (hnd : Sc.Nodup)
    (hS : ∀ n ∈ Sc, (∃ i, P.BT.lookup n = some i) ∧ P.RB n = true) :
  isBackend γ P W Pk b ∗ rbOwnIn γ (· ∈ Sc) r ={⊤}=∗
    rbOwnInR γ (· ∈ Sc) r ∗ [∗list] n ∈ Sc, rbRd γ n ½ (bktOf r n)
```

(The mask can be `⊤ ∖ ↑rbClaimN`'s complement-free form `↑rbClaimN ⊆ E`; the realization uses it at `⊤`.)

## 0. The obstacle, precisely

Today the three per-bucket ghosts of a tracked bucket `n` are held as follows (`InvBackend.lean`):

| ghost | element value | shares today |
|---|---|---|
| `γ.rbk` (writer's contents, pending flag) | `(c, f)` | client ½ (`rbPartF`: `rbPart`/`rbOwnIn`/`rbOwn`), lock ½ (`rbSide`, with the map's authority); once claimed, the client's ½ sits in the lock's `rbrOne` claimed branch |
| `γ.rbr` (readers' contents) | `v = rvBkt P rv n` | readers ½ (`rtCore`'s `rbrHalves`, split by `rfrac`), lock ½ (`rbrOne` unclaimed branch) or client ½ (`rbRd`, claimed); authority in the lock (`rbrSide`) |
| `γ.rbc` (claim marker) | `none` / `some (c, f)` | unclaimed: lock 1 at `none`; claimed: lock ½ + client ½ (`rbOwnInR`); authority in the lock |

The claim must learn `v = bktOf (r n)` from the client's `rbk` share `(r n, false)`. Today the only facts linking `f`
to `v` are in the lock (`rbSide`'s `F n = false → tkI`, `trkOk`'s `kOk .idle`, `rbrOne`'s `v = rvBkt (st.C, st.R) n`),
which the client cannot reach unless it holds the lock. So a lock-free claim needs a **third holder of `rbk`, `rbr` and
`rbc` shares, outside the lock, that keeps the link `f = false → v = bktOf c`**: a new backend invariant.

## 1. What moves where

A new invariant inside `isBackend` (sealed, `@[no_expose]`), `inv rbClaimN (rbClaimInv γ P)`, one conjunct per tracked
name (`[∗map] n ↦ _ ∈ γ.rbD`):

```
rbClaimOne γ P n :=
  (∃ c f v, ghostMapElem γ.rbk n (own ½) (c, f) ∗ ghostMapElem γ.rbr n (own ¼) v ∗
     ghostMapElem γ.rbc n (own 1) none ∗ ⌜f = false → v = bktOfO c⌝)                    -- unclaimed
  ∨ (∃ c f w, ghostMapElem γ.rbk n (own ¾) (c, f) ∗ ghostMapElem γ.rbc n (own ½) (some w) ∗
     ⌜w.1 = c⌝)                                                                          -- claimed
```

plus the `γ.rbc` authority (`∃ M, ghostMapAuth γ.rbc 1 M`). The shares, old → new:

| ghost | holder | old | new |
|---|---|---|---|
| `rbk` | client (`rbPartF`, hence `rbPart`, `rbOwnIn`, `rbOwn`) | ½ | **¼** (§2) |
| `rbk` | lock (`rbSide`, same shape as the client's: `rbPartF`) | ½ | **¼** |
| `rbk` | `rbClaimInv` | – | ½ unclaimed; ¾ claimed (its ½ + the client's ¼ deposited by the claim) |
| `rbr` | readers (`rtCore`) | ½ | ½ (unchanged) |
| `rbr` | lock (`rbrOne`) | ½ unclaimed, 0 claimed | **¼ in both cases** (uniform `rbrOne`, below) |
| `rbr` | `rbClaimInv` (unclaimed) / client `rbRd` (claimed) | – / ½ | ¼ / ¼ (`rbRd γ n q v` redefined as element share `q/2`: the text `rbRd γ n ½ v` and every `rbRd` statement unchanged) |
| `rbc` | lock (`rbrOne`/`rbrSide`, with authority) | 1 or ½, authority | **none** (authority and element move to `rbClaimInv`) |
| `rbc` | client (`rbOwnInR`) | ½ claimed | ½ claimed (unchanged) |

`rbrOne γ P st n` becomes uniform: `ghostMapElem γ.rbr n (own ¼) (rvBkt P (st.C, st.R) n)` (the lock keeps knowing the
readers' contents of every tracked bucket); its claimed branch's facts move: "no unclaimed part of `n` exists" is now
the deposit in `rbClaimInv`'s claimed branch (¾ + the lock's ¼ = 1); "the claimed contents are the writer's" is the
branch's `⌜w.1 = c⌝`; "`tk n = idle ∨ cw n`" becomes a lock-side fact derived when needed (§3.3). `rbrSide` loses the
`γ.rbc` authority and `cwOk`'s link to claims stays (it is about `st.cw`, the lock's).

**Who opens `rbClaimInv`** (each a ghost step at a point where the proof already holds what it held before, plus the
invariant, opened and closed around the step; never across a client callback):
- every write that updates `rbk` (`rbSide_put` and its callers: `UnsafePut`, `UnsafeSeqPut`, `UnsafeDelete`,
  `UnsafeCreateBucket`, `UnsafeDeleteBucket` of `batchTx` and `batchTxBuffered`; the claimed writes, `rbrSide_writeR`,
  which also update `rbc`): today `|==>` lemmas over the lock's and the client's shares, they become `={E}=∗` lemmas
  taking `isBackend` (or the invariant), and the writers' proofs `imod` them (specs at `⊤`: no statement change);
- the readers' updates of `rbr` for non-idle unclaimed buckets: the write-back (`wb_core`), the commit under the lock
  (`rtRes_cm_close`, `unsafeCommit`), and `Unlock`'s accessor steps for claimed buckets (they need no invariant share
  now: lock ¼ + `rtCore` ½ + the client's `rbRd` ¼ make the element whole, as today with ½/½);
- the flag clears (`trkSide_idle`, `rbPartR_idle`, private, in `Unlock`'s macros `bu_free`, `bu_free0`, `bu_release`);
- `NewAlloc` allocates it (with every tracked bucket unclaimed, `f = false`, `v = c = ` the initial contents).
A commit with the lock free (`run`, `ForceCommit`) touches none of these ghosts (unchanged: it changes no tracked
readers' contents, `freeOk` + `trkOk`), so it does not open the invariant.

## 2. Does `rbOwnIn`'s definition change? The trusted texts

**Yes, by its fraction only**: `rbPartF` holds `rbEls γ S ¼ …` instead of `½` (the shape is shared by `rbPart`,
`rbOwnIn`, `rbOwn` and the lock's `rbSide`). Why not keep the client's ½ and take the invariant's share from the lock's
½: `backend.Snapshot.wp_proof` (trusted) hands its observation `rbOwn γ r` **as the lock's resource** (`rbSide`'s
docstring: "the batch lock holds the same shape, so a snapshot's observation is handed one"). If the lock held a smaller
share than a client's `rbOwn`, the axiom would hand more than the lock owns: its meaning would move. Scaling the shape
uniformly keeps "the lock holds exactly one `rbOwn`-shaped share, as each client part does" true.

The argument that every trusted text means the same: these predicates are used by the trusted texts only as opaque
resources passed in and out, and their laws are agreement and exclusivity between parts, which hold at any fraction.
What a client can do with a part is unchanged: (a) two parts agree with each other and with the lock (`rbPart_agree`,
`rbOwnIn_agree`, `rbOwn_agree`, `batchLocked_rbOwn(In)`: ghost-map agreement, fraction-free); (b) two parts of one
bucket cannot both exist (today ½ + ½ + the lock's ½ > 1; new ¼ + ¼ + ¼ + the invariant's ½ > 1); (c) a write needs a
part (the element must be whole: today client ½ + lock ½; new client ¼ + lock ¼ + invariant ½, which only the backend's
own proofs open); (d) no law gives a part from nothing or from `isBackend` (the invariant's share is sealed and never
leaves the invariant except into a claimed branch). The texts and their Go arguments:

| trusted text (premise/post) | uses | same meaning? |
|---|---|---|
| `lease.NewLessor`, `MustUnsafeGetAllLeases` | `rbOwnIn`/`rbPart` of `lease`, `batchLocked … false` | yes: (a)-(d); `lease` never claimed |
| `auth.NewAuthStore` (off modes) | `rbOwnIn` of the auth buckets, unclaimed | yes; in mode `on` the auth buckets go to the realization (claimed there) |
| `RaftCluster.Recover`/`SetBackend`, membership's `MustRead/Save/DeleteMember…` | `rbOwnIn`/`rbPart` of `members*` | yes; never claimed |
| v3alarm's `NewAlarmStore`, `AlarmStore.restore` | `rbOwnIn`/`rbPart` of `alarm` | yes; never claimed |
| `backend.backend.Snapshot` (observation) | `rbOwn γ r` as the lock's share | yes: the lock's share is still one `rbOwn` shape (the reason for the uniform scaling) |
| `storage.OpenBackend` (post `newPostK`: `isBackend`, the client's `rbOwn`) | `isBackend`, `rbOwn` | `isBackend` gains the invariant `rbClaimN`: the axiom's standing argument ("claims what `New` gives", A1 §3) carries over, `New`'s proof allocating it (`NewAlloc`); `rbOwn` as (a)-(d) |
| `authSchemaSrv`/`authSchemaSnap` | `rbOwnIn d.γB authBkts r` (premise) | yes (the premise is what the realization claims with the new law; its text unchanged) |

No trusted text's statement changes; two meanings grow by sealed internals (`isBackend`'s invariant; the fraction inside
`rbPartF`), argued above. The interface files of the backend change (`rbPartF`'s body is exposed: `interface/…/InvBackend.txt`).

## 3. Why the claim is sound without the batch lock (the A1.6-9 review, point by point)

The review's claim argument (§2) rested on the claimer holding the lock: the readers' state is `(st.C, st.R)`, and
idleness gives `tk n = idle` by `tkI`. The new argument rests instead on the invariant's link `L(n) : f = false →
v = bktOf c`, where `v` is the readers' element (equal, by agreement, to `rtCore`'s `rvBkt P rv n` for the current
readers' state `rv`) and `(c, f)` is the `rbk` element (equal to the client's and the lock's shares).

### 3.1 The link is invariant (every step that changes `c`, `f` or `v` of an unclaimed bucket)
- **A write** sets `f := true` (`rbSide_put`): `L` holds vacuously. (Go: the session has a pending write.)
- **The write-back** changes `v` only for a non-idle kind; if `f = false` then `tk n = idle` by `tkI` (the lock's
  `rbSide`, whose `F n` agrees with the invariant's `f`), and `rvBkt_writeback_nop` keeps `v`. The step opens the
  invariant only to update `v` of buckets with `f = true`.
- **The commit under the lock** (`bu_release`, and the hook's commit inside `LockInsideApply`): for `f = false`,
  `tk n = idle`, `rvBkt_commit_idle` keeps `v`; for `f = true` no obligation.
- **A commit with the lock free**: no tracked readers' contents change (`freeOk` + `trkOk`), `c`, `f` unchanged.
- **A flag clear** (`f := false`, `c := r n`, only in `bu_free0`/`bu_free`/`bu_release`, the review's §1): there every
  kind is idle and `trkOk`'s `kOk .idle` gives `rvBkt (st.C, st.R) n = bktOf st.S n = bktOf c`; the lock's `rbrOne`
  share (¼, at `rvBkt (st.C, st.R) n`) agrees with the invariant's `v`, so `v = bktOf c`: `L` re-established.
  This is why the lock keeps an `rbr` share for every bucket.
- **`New`**: every bucket starts idle, the readers' contents the writer's.
- Go: `f = false` means no write of the current session to `n` (the trusted readers' argument for `rbOwnIn`: the last
  `Unlock` handed the part wrote back and committed), so every `ReadTx` reader sees `c`; a reader of `ConcurrentReadTx`
  is not covered (as `rtHeldF_rbRd`, the cached copy can be stale).

### 3.2 The claim itself
Open `rbClaimInv`; for each `n ∈ Sc`: the unclaimed branch (the client's `rbk` ¼ with the invariant's ½ is valid only
there: in the claimed branch ¾ + ¼ + the lock's ¼ > 1, which is the review's `rbr_claimed_excl` argument, so **a second
claim is impossible**); agreement gives `(c, f) = (r n, false)`, so `L` gives `v = bktOf (r n)`. Update `γ.rbc n` from
`none` (whole) to `some (r n, false)` (the authority is in the invariant), split it ½/½: one half stays (claimed branch),
one goes to the client (`rbOwnInR`); deposit the client's `rbk` ¼ in the claimed branch (¾; `w.1 = r n = c`); hand the
invariant's `rbr` ¼ to the client as `rbRd γ n ½ (bktOf r n)` (`rbRd`'s `q/2`). Close. **Accounting, no duplication**:

| consumed | produced |
|---|---|
| the client's `rbk` ¼ (`rbOwnIn`) | deposited in the claimed branch |
| the invariant's `rbc` element, whole at `none` | ½ claimed branch + ½ client, at `some (r n, false)` |
| the invariant's `rbr` ¼ | the client's `rbRd` |

`rbRd`'s value is what every `ReadTx` reader sees **now and until the client moves it**: its other holders are `rtCore`
(½, the readers) and the lock (¼); the element changes only with all three, i.e. through `Unlock`'s accessor (A1.5), which
is the client's.

### 3.3 The lock's view of a claim it did not see (new: the claim no longer runs under the lock)
A claim can now happen while another session holds the lock, at any point of it (between two writes, inside `Unlock`'s
window after the write-back, inside the hook's window). What the lock needed from its claimed branch, and where it now
comes from:
- **"Only a claimed writer reaches `n` once claimed"**: a write via `rbPut` needs the whole `rbk` element (client ¼ +
  lock ¼ + invariant's ½); in the claimed branch the invariant holds ¾, so no `rbPart` of `n` exists (the review's
  "no law back to `rbPart`" stands: nothing ever takes the deposit out).
- **"`tk n = idle ∨ cw n`"** (used by `Unlock`'s accessor and `trkSide_updR`): at the claim `f = false`, hence `tk n =
  idle` by `tkI` in whatever session holds the lock (the lock's `F n = false`, by agreement); afterwards `tk n` changes
  only by a write to `n`, which is a claimed write (`cw n := true`). So the lock-side invariant becomes `∀ n, tk n ≠ idle →
  F n = true ∧ (n unclaimed ∨ cw n)`, stated in `trkSide` with the claim status read from `rbClaimInv` when needed
  (the invariant opened at the step). To check in the Lean: no lock-side proof today derives a fact from "unclaimed"
  without opening something; where `rbrOne`'s claimed branch was destructured (`trkSide_updR`, `rbrSide_writeR`, the
  accessor steps, `batchGhostAt_idle`), the invariant is opened instead.
- **"The claimed contents are the writer's"** (`v.1 = (rbData P st.S) n`): the claimed branch's `w.1 = c`, `c` agreeing
  with the lock's `rbk` share at `rbData P st.S`.
- **The hook's window** (the review's "claim inside the hook's window"): `n` idle, the hook's commit keeps it
  (`rvBkt_commit_idle`); `hookStep` keeps the kinds (`trkKept`); nothing new.
- **Inside `Unlock`'s window** (after the write-back, `readTx` released, before the commit): `n` idle, neither the
  write-back nor the commit moved or will move `v`; Go: a reader there sees `c` for an idle bucket (A1's Go test, put-only
  and delete-only buckets, `notes/auth-schema-srv-a1/zz_a1_trackedwindow_test.go`: an untouched bucket is never split).

### 3.4 The review's other points
- **(1) `tkI` and the flag clears**: unchanged; the three macros additionally re-establish `L` (§3.1).
- **(2) split laws**: unchanged (they rearrange the client's `rbc` halves; `rbc` updates of a claimed part's flags now
  open the invariant, whose authority they need).
- **(4) claimed → `rbPart`: no law**: unchanged (the deposit never leaves). **Mode `true` → `false`** (MINOR 1):
  unchanged; this Scope does not touch `trkSide_mode`; the note's §4.2 sentence to restate as the review says (to do
  with the Lean).
- **MINOR 2** (`rbPartR_idle` clears claimed flags without a `tkI`-style premise): it now opens the invariant to update
  `rbc`; give it the premise `∀ n ∈ Sr, P.RB n → tk n = idle` as `trkSide_idle` has (the realization will not read a
  claimed flag either: `rbOwnInR` still grants nothing beyond `rbPartR`).
- **MINOR 3** (claimed buckets' `rbk` flag set by claimed writes, never cleared): unchanged; `L` is only for unclaimed
  buckets, so nothing reads it. Documented in `rbClaimOne`'s docstring.

## 4. The cross-world and fresh-world checks

- **crossWorld** (the axiom skill, step 3: a law whose left side bare persistent cells can satisfy and whose conclusion
  is a pure equation about an opaque function of a pointer): the new law is **proved**, not trusted; its left side is
  `isBackend` (persistent, holding invariants with ghost names `γ`) and an exclusive client part, its conclusion
  resources (`rbOwnInR`, `rbRd`), no pure fact. In a fresh world with `isBackend`'s cells only (no `rbOwnIn`), the law
  gives nothing; with an `rbOwnIn` made in that world (only `New`/`NewAlloc` or a trusted post makes one, at the same
  `γ` as its `isBackend`), its output is that world's. Not suspect.
- **Fresh world, persistent authoritative heap** (could a persistent fact plus the law conjure an authority or an
  exclusive share in a world where nothing backs it?): the only authority the law touches is `γ.rbc`'s, inside the
  invariant; no law makes `rbOwnIn`, `rbk`/`rbr`/`rbc` shares or the invariant from `isBackend` alone; the invariant's
  shares leave it only into the claimed branch (`rbk`) or to the claimer in exchange for its part (`rbr` ¼, `rbc` ½).
  The trusted texts that **give** `isBackend` (`OpenBackend`'s `newPostK`) now promise the invariant too: in Go's terms
  nothing (ghost only); its standing argument is `New`'s proof, which allocates it with fresh names. The trusted texts
  that give `rbOwnIn`/`rbPart`/`rbOwn` (`NewAlarmStore`, `NewLessor`, ... posts) give the same shape at the new fraction:
  their meaning is (a)-(d) of §2, unchanged.

## 5. Plan and estimate

| step | content | Lean lines (est.) |
|---|---|---|
| C1 | `InvBackend`: `rbPartF` at ¼, `rbSide`'s shape, `rbRd` as `q/2`, `rbrOne` uniform ¼, `rbrSide` without `rbc`, `rbClaimInv`/`rbClaimOne`, `isBackend` with `inv rbClaimN`; `NewAlloc` allocation | 150-300 |
| C2 | `TrackedLemmas`: agreement/exclusivity at the new fractions (`rbElem` validity: ¼+¼+½), `rbSide_put` and friends as `={E}=∗` over the invariant, `rbrSide` laws without `rbc` | 300-600 |
| C3 | `ClaimedLemmas`: `rbOwnIn_claim` (replaces `batchLocked_claim`; `trkSide_claim1`/`trkSide_claim` go), `rbrSide_writeR`/`trkSide_updR`/`rbPartR_idle` opening the invariant, MINOR 2's premise, the lock-side `tk`/`cw` fact | 300-600 |
| C4 | writers' proofs (`batchTx`, `batchTxBuffered`: put, seq-put, delete, create, delete bucket), `unsafeCommit`, `Unlock` (write-back, commit, macros, accessor), `InvCommit`, `InvStop`, `InvBatch`: `imod` of the fancy steps; masks (`rbClaimN` disjoint from the backend's other namespaces) | 200-500 |
| C5 | interfaces regenerated, `etc/api-check.py`, tcb `--check` (no axiom or sorry added), `etc/gen-interface.py` diffs reviewed; the soundness note (`notes/auth-schema-srv-a1-soundness.md`, a section) | 50-100 |

Total **1000-2100 lines**, all in `storage/backend` (checked by grep: no proof outside it mentions `rbPartF`, `rbEls`,
`rbElem` or `rbrOne`; mvcc's `InvStore.lean:249` lists `BNames`' fields, `rbc` among them, for injectivity: unaffected), 2-4 sessions; risk: the writers' and `Unlock`'s ghost steps sit
inside another open invariant (the read lock's resource, the hook's window) where opening `rbClaimN` needs the namespace
disjoint and the step atomic: probe `wb_core` and `unsafeCommit` first (C2's first commit). A6 then uses
`rbOwnIn_claim` inside the realization's update (boot and every snapshot backend), and the rest of A6 proceeds as
planned.

**Not done in this Scope**: no Lean probe; the proof bodies of `wb_core`, `rtRes_cm_close`, `rbrSide_writeR` were read
only at their statements and call sites.
