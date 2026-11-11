# bbolt's public API: a library spec over client-owned state, and what its trusted pieces may assume

**Kind**: a whole library API replacing a trust boundary (bbolt v1.5.0 as etcd uses it: `Open`,
`Begin`, `Commit`, buckets, cursors; 23 triples, nine sealed predicates, the option axioms, a
logger contract), designed over 12 rounds with 11 reviews and frozen 2026-11-03.
`Spec/go_etcd_io/bbolt/` (`Api.lean`, `Data.lean`, `Logger.lean`, `Options.lean`, one file per
function); the design and every decision in `notes/bbolt-spec-decisions.md`.

## First version (round 1)

The backend's old `_kv` axioms passed an exclusive `ownDB db γ D` and a write token `wrTok γ`
around. Round 1 replaced them:

```lean
opaque isBolt (db : Loc) (γ : BoltName) : IProp GF            -- persistent handle
opaque boltState (γ : BoltName) (q : Qp) (D : Data) : IProp GF -- client-owned, fractional
opaque boltTx (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) : IProp GF  -- both kinds

abbrev Tx.Commit.spec := ∀ tx γ D S G Q,
  {{ boltTx tx γ 1 { rw := true, base := D, cur := S, gen := G } ∗
     AU <{ ∃∃ D', boltState γ 1 D' }> @ ⊤ \ ↑boltN, ∅ <{ ⌜D' = D⌝ ∗ boltState γ 1 S, COMM Q }> }}
    tx.Commit()
  {{ err, RET err; txDone tx ∗ ((⌜err = nil⌝ ∗ Q) ∨ (⌜err ≠ nil⌝ ∗ (Q ∨ AU …))) }}
```

`Begin(false)` took the caller's `threadTok` (the read transaction's `mmaplock` reader slot) and a
read update; `Open` took `osInv`, `fileHolds path D`, `ThreadBoundLe GF (2^30)`; a fixed `boltN`;
`boltLogger` opaque; `OptsM` with four fields.

## Rounds 2-8: the reviewers' findings, decided by the agent

Each round a fresh `spec-reviewer` read the candidate against bbolt's Go code and its callers.
What their findings changed, briefly: `Cursor.Prev` scoped to read transactions (a Go bug in
writers, `issues/bbolt-cursor-prev-empty-leaf.md`); a spare reader slot for `Commit`'s
`freepages`, so `2^29` threads; a caller-chosen namespace `N` instead of `boltN`; `fileHolds`'
well-formedness made what every panic in the read and commit paths needs, then kept by `Commit`
(exact branch keys, extents, the synced freelist, the current meta at page `txid % 2`); agreement
laws dropped rather than a `db ↦ γ` registry (clients carry `γ`); `Commit` over a view variable,
not a literal record. Principles: "No unneeded premise", "Local", "few predicates, each earned".

## The user's decisions, and what each changed

- **D7, D1, D3, D4, D5 (round 3).** Client-owned `boltState` reached by atomic updates, not
  `ownDB`/`wrTok`; the reader slot a `threadTok`; the thread and receipt bounds on `Open`; `Put`'s
  entry bound `bboltEntryMax = 2^28` replacing the false `MaxValueSize` arm; `FillPercent` written
  back only non-NaN. Approved as recommended.
- **D13 (round 3).** `OptsM.ok` excludes `Mlock` and `MmapFlags` other than `0`/`MAP_POPULATE`
  (scope restrictions of the file model), and the option axioms are restated for the new fields.
- **D17 (round 3).** Perennial gives float multiplication and float-to-int no meaning, so
  `splitTwo`'s threshold was arbitrary and `Commit` could panic in the model. The user approved a
  fork helper `splitThreshold`, `trusted` with a model bounding it (`0 ≤ t ≤ pageSize`, except
  NaN or `pageSize ≥ 2^53`), and the general Perennial fix proposed separately.
- **D18 (round 5).** `fileHolds` needed "no user value holds a valid meta at an offset
  `getPageSize` probes", which no `Commit` can keep (`Put` takes any bytes). The user chose a
  fork change (`getPageSize` returns a meta read error instead of probing on); the clause went.
- **D20 (round 6, in principle).** `boltLogger` exposed as a method contract lending each
  argument's resources, since the backend's trusted `newBoltLoggerZap` asserts it. (The agent's
  D20′ then restated it for what Go's `fmt` really calls.)
- **D22 (a), round 9.** A torn meta write could validate by an FNV collision. The user chose to
  make "no checksum collision on a torn meta" (P2) a visible restriction of every run, not an
  assumption about the hash: **an axiom that a hash has no collisions is false (FNV-64a has
  them), so it would make the logic inconsistent.**
- **D22 (b), round 11.** Review 9 found P2 was not what it was described as: an in-process `pwrite`
  of one aligned page never tears on Linux, so P2 removed no real execution, and it excluded
  constructible runs in the byte-granular model instead. Told so in plain terms (what `pwrite`
  does to a page, when it can stop half-way, what bbolt then sees), the user chose to state the
  physical fact in the file model: OsFs's `pwrite` within one aligned OS page is all-or-nothing,
  under the environment hypothesis "`RLIMIT_FSIZE` unlimited or a multiple of the page size". P2,
  the restricted semantics and the Lean FNV left the spec; `Commit`'s error post ("took effect or
  not") now rests on the model rule.

## After the freeze: the invariant design's corrections (decided by the coordinator)

Designing the invariants that prove the frozen spec found four laws unprovable under any
representation consistent with the triples: `boltTx_timeless` (`boltTx` must hold the locks'
invariants: now `boltTx_later : isBolt db γ ⊢ ▷ boltTx … -∗ ◇ boltTx …`); `fileHolds_timeless`
(`osInv` folded in: unfolded again, `Open` takes `osInv`); the γ-free `txBytes`/`boltBkt`/`boltCur`
(nothing reached from `tx` alone agrees with `boltTx tx γ`'s names: they take `γ`, and the general
fix, a meta token on allocation, goes to Perennial); `boltTx_fill` (only for writers). D19's
"registry is provable" was wrong too. Lesson: a law is part of the spec; check each against a
sketch of the representation before freezing, not only the triples.

## The frozen spec (excerpt)

```lean
abbrev Tx.Commit.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (Q : IProp GF),
  {{ boltTx tx γ 1 T ∗ ⌜T.rw = true⌝ ∗
      AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }> }}
    tx.Commit()
  {{ err, RET #err; txDone tx ∗
      ((⌜err = nil⌝ ∗ Q) ∨ (⌜err ≠ nil⌝ ∗ (Q ∨ AU <{ … }> @ ⊤ \ ↑γ.ns, ∅ <{ …, COMM Q }>))) }}

abbrev Open.spec : Prop :=
  ∀ [HasExt osFsExt] [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)] N path mode opts dq o D,
  {{ isPkgInit bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗ fileHolds path D ∗ optsAt opts dq o ∗ ⌜o.ok⌝ ∗
     (⌜o.logger = nil⌝ ∨ boltLogger o.logger) }}
    Open path mode opts
  {{ db err, RET (db, err); optsAt opts dq o ∗
     ((⌜err = nil⌝ ∗ ∃ γ, ⌜γ.ns = N⌝ ∗ isBolt db γ ∗ boltState γ 1 D) ∨ ⌜err ≠ nil⌝) }}
```

Every predicate and triple carries `[HasExt osFsExt]` (in the statement: Lean drops an unused
section variable). The user's decisions D1, D3, D4, D5, D7, D13, D17, D18, D20 (as D20′) and
D22 (b); the agent's D2, D6, D8-D12, D14-D16, D19, D20′, D21 (each with its basis in the notes).
Principles: "An assumption states the physical fact the code relies on" (a hard rule), "Explain a
finding in plain terms before asking for a decision", "An instance binder a statement must carry
goes inside the statement".
