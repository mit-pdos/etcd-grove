> **Copied into the repository on 2026-11-03** from the spec design's scratch file `candidate.md`
> (12 rounds, frozen). What it calls `candidate.lean` is the frozen statement text, landed as
> `Spec/go_etcd_io/bbolt/{Data,Api,Logger,Options}.lean`, `Spec/fmt/ErrorOk.lean`, the spec files
> `Spec/go_etcd_io/bbolt/<T>__<M>.lean` and the option axioms
> `Proof/go_etcd_io/bbolt/Options.lean`; `candidate-rN.lean` and `review-N.md` (earlier rounds,
> the reviews) were not committed. The rounds' story is in
> `.claude/skills/spec/examples/bbolt-api.md`; `notes/decisions.md`, "bbolt's API spec", has the
> summary.

# bbolt's API specs: candidate 12, the frozen spec (2026-11-03)

The final summary is "Frozen spec" at the end of this file. The landing plan is `LANDING.md`.

## Changes in round 12 (after `review-11.md`: nothing blocks; edits decided by the coordinator)

Round 11's text is kept as `candidate-r11.lean`. No statement changed.

- **M1.** `os.File.WriteAt`'s planned post is `j = 0 ∨ j = data.length` for a one-page aligned
  write, whatever `err` (D22 item 4). `Tx.Commit`'s proof fires the update when
  `j = data.length`.
- **M2.** D22's environment hypothesis, for `Impl.lean`'s Environment paragraph:
  "`RLIMIT_FSIZE` unlimited or a multiple of the OS page size".
- **M3.** The `hash/fnv` trust boundary is stated: only `Sum64`'s determinism is needed. The
  chosen route is translating `New64a`/`sum64a` with bodies, which makes it trusted by nothing.
  The fallback is a determinism-only spec.
- **L1.** D22's Linux argument is restated for an uptodate folio (a short copy continues within
  the page).
- **L2.** Stale "restricted semantics" text is removed (`candidate.lean`'s `fileHolds` comment,
  `candidate.md`'s `Open_kv` lines).
- **L3.** The backend table: every `_kv` corollary gains `[HasExt osFsExt]`; "exact" is dropped.
- **L4.** `optsZero_ok` has `omit [GooseSemantics] [GooseInterp] go_gctx in`.
- **Re-elaborated** on a temporary copy in the `worktree-bbolt-v2` worktree (deleted).


The final summary is "Frozen spec" at the end of this file.

## Changes in round 11 (the user's D22 = (b))

Round 10's text is kept as `candidate-r10.lean`.

- **P2 is dropped entirely.** Gone from `candidate.lean`: `osP2`, `osFsSemStepWith`, `fnv64a`,
  `leNat`, `boltMetaValid`, `slotAt`, `boltMetaOffsets`, and the restricted-semantics binders.
  Gone from D22: infrastructure items G, W, T, F and C. `fileHolds`' meta validity stays in its
  docstring (bbolt's `Meta.Validate`), as before round 9.
- **The specs are back over the default semantics.** Each triple starts with
  `∀ [HasExt osFsExt]`, and each vocabulary predicate takes `[HasExt osFsExt]` in its signature.
  The unused-section-variable linter stays on.
- **The check.** A temporary copy elaborated with `lake env lean` in the `worktree-bbolt-v2`
  worktree, then deleted: 0 errors. With `pp.explicit`, `#check` of `fileHolds`, `fileHolds_new`
  and `boltState_read_au`, and `#print` of `Open.spec` and `Tx.Commit.spec`, show
  `@HasExt … osFsExt osFs_semantics os_interp`.
- **`fileHolds_new` is stated again**, elaborated, in `vocab`.
- **`boltPageSize_eq_osPageSize : boltPageSize = osPageSize`** (`rfl`) ties bbolt's page to
  OsFs's OS page.
- **D22 is rewritten as the OsFs change.**
  - The `Impl.lean` conjunct, its consequence in `wp_osPWriteFinish` and `os.File.WriteAt`'s
    spec, and a test.
  - The Linux justification (`generic_perform_write`).
  - Why `Commit`'s error post, the meta parity and "one valid meta" hold with it.
  - `Tx.Commit.spec`'s and `fileHolds`' docstrings cite D22 instead of P2.


## Changes in round 10 (after `review-9.md`)

Round 9's text is kept as `candidate-r9.lean`.

**Done:**
- **H1, the restricted semantics in the statements.** Each triple has the binder
  `∀ [HasExt (S := osFsSemStepWith osP2) osFsExt]` at its head. Each vocabulary predicate has it
  in its signature, and the laws take it through the predicates.
  - `set_option linter.unusedSectionVars false` is removed. In round 9 it had hidden that the
    section variable was in no statement.
  - Verified on a temporary copy elaborated with `lake env lean` in the `worktree-bbolt-v2`
    worktree (deleted): `pp.explicit` `#print` of `Open.spec` and `Tx.Commit.spec`, and `#check`
    of `fileHolds` and `boltState_read_au`, show `@HasExt … osFsExt (osFsSemStepWith … osP2)
    os_interp`.
  - `fileHolds_new` cannot be stated at the restricted semantics until item G, since OsFs's
    `osMeta`/`osBytes`/`osInv` are at `osFs_semantics`. Its text is kept in `candidate.lean`
    for then.
- **L1, stale text.**
  - The target is `goose-lean-v2` `b3e06648`, pinned since `44ed0aad76`, with round 7's commits
    landed.
  - The candidate elaborates.
  - `osInv` is inside `fileHolds` (`Open`, `Open_kv`, the summary, D8).
  - "Not done", the open items, D11, the summary's heading and P2's trust-boundary note are
    updated.
- **L2.** `osP2` is on the step's post-state: `osFsSemStepWith`'s restriction sees `st` and
  `st'`, and no written count is decoded from a `W64`, so liveness needs no size bound.
- **L3.** The named constant `boltPageSize = 4096` replaces the literal in the meta offsets, and
  is the page size of `fileHolds` and `OptsM.ok`.
- **M1, rewritten regardless.** D22's rationale is now honest: P2 removes no Linux execution, and
  is not a collision premise.

**Held, the user is re-asked: M1–M3, (a) P2 vs (b) atomic in-page `pwrite`.** D22 below sketches
both paths' infrastructure:
- after M2, a write-local restriction `R cur off data k` with liveness and a retry-closure law;
- after M3, the default is literally `osFsSemStepWith (fun .. => True)`;
- and (b)'s `PWriteFinish` conjunct.


## Changes in round 9 (after the user's decision on H1)

Round 8's text is kept as `candidate-r8.lean`.

- **D22 (the user's): P2 is a restriction of the runs**, placed per review 7's H1 fix. It is in
  `candidate.lean`, section "P2: the run restriction". (b), OsFs's all-or-nothing one-page
  `pwrite`, stays below as the documented alternative.
- **`candidate.lean` states it in Lean, over every file:**
  - `fnv64a` (FNV-64a);
  - `boltMetaValid` (`Meta.Validate`: magic, version, checksum over bytes 0..56);
  - `tornMetaOk` (at offsets 16 and 4112 of any file, a torn write leaves no validating slot
    other than the old or the new one);
  - `osP2` (only a `PWriteFinish` with `k < data.length` is restricted);
  - `osFsSemStepWith P` (OsFs's semantics with the step `OsStep ∧ P`, generic in the
    instances, as `ExtSemantics.step` is).

  P2 is never an axiom or an assumption class about FNV.
- **Every bbolt spec names the restricted semantics.** The spec section's instance is
  `[HasExt (S := osFsSemStepWith osP2) osFsExt]`. `Open` no longer takes `osInv` separately: it
  is folded into `fileHolds` (D8's option), and `fileHolds_new` takes it.
- **It elaborates.** Checked with `etc/lean-check.py -a` on a temporary copy in the
  `worktree-bbolt-v2` worktree, 0 errors (`sorry` warnings only); the copy was deleted and the
  server stopped.
- **The infrastructure D22 needs** is listed under D22 below: what, where, and who owns it.


## Changes in round 8 (after `review-7.md`, the freeze check)

Round 7's text is kept as `candidate-r7.lean`.

**Decided by me:**
- **M1, `fileHolds`.** Every tree page's header id is its page number (`tx.page`'s `FastCheck`
  panics otherwise, in every read). An inline bucket's page has header id 0 (`node.read` takes
  `n.pgid` from it, and `spill` frees `tx.page(n.pgid)`). bbolt maintains both: `allocate` sets
  the id, and an inline value is a fresh zeroed buffer. `WriteTo` copies pages verbatim.
- **M2.** `loggerPtrOk o.logger` (nil, or a pointer type) goes into `OptsM.ok` and into
  `wp_Options_String`'s precondition. `(*Options).String` formats the logger with `%p`, which for
  a non-pointer type prints by reflection, and that is racy. This is a scope restriction of the
  model. The backend's `*zapBoltLogger` and the nil logger meet it.
- **M3.** `logArgOk` tests signatures: `methodSet ty !! "Error"/"String" = some noArgStringSig`,
  the `() string` signature. A Stringer must have no `Error() string`.
- **M4.** One shared `fmt`-level predicate, `fmtErrorOk err`: `Error() string`, no `Format`, and
  `Error()` returns needing nothing. It goes in the repository's `Spec/fmt/`, beside
  `fmt.argOk`. `logArgOk`'s error disjunct is `fmtErrorOk`. Its producers:
  - a law for `errors.New`'s `*errorString`;
  - `fmt.Errorf.spec`'s post, restated;
  - the OsFs-backed `os`/`syscall`/`unix` specs' error posts, once `(*fs.PathError).Error` and
    `syscall.Errno.Error` are translated with bodies (D20' infrastructure).
- **L1.** `candidate.lean` now elaborates.
  - Changes: the imports (`Iris.BI.Lib.Atomic`, `GooseLang.Ext.OsFs.Specs`,
    `Proof.go_etcd_io.bbolt.PkgInit`, `Perennial.Proof.fmt.Base`, `Spec.fmt.Errorf`),
    `[∗list]`, and `(GF := GF)` on the first predicate of the triples that start without
    `isPkgInit`.
  - Checked against the `worktree-bbolt-v2` build with `etc/lean-check.py -a` on a copy at
    `Spec/go_etcd_io/bbolt/CandTmp.lean`: 0 errors, `sorry` warnings only. The copy was then
    deleted and the check server stopped; the worktree is clean.
  - The Hoare-triple form inside `boltLogger` is kept: it elaborates.
- **L2.** `fileHolds` wording:
  - "within the file's length" is now implied by the high-water-mark clause;
  - "every valid meta records page size 4096";
  - the high-water-mark maintenance no longer rests on `grow`: under `NoGrowSync`, `grow` does
    not truncate, and the mark holds because `tx.write` writes every allocated extent whole.
- **L3.** Stale text: D16's open question cites D21, the "Not done" and vocabulary rows are
  updated, and the target line says round 8.

**H1, P2's placement:** decided by the user in round 9 (D22, route (a)). The "H1" section
below keeps (b) as the documented alternative.

## H1: where P2 goes (for the user)

P2 ("a torn meta write does not leave a checksum-valid mix in the page cache") is needed by
`Commit`'s error post, by the parity maintenance, and by `isBolt`'s "one valid meta". The
statements are over `osFs_semantics`, where a colliding torn write is a possible execution. So
P2 must either show in every closed result, or be made unnecessary.

**(a) P2 as a premise of every closed result.**
- A step-restricted semantics `osFsSemStepWith P2`, whose step is `OsStep ∧ P2`, and whose
  restriction always admits the complete write.
- A Lean FNV-64a, equal to the trust-boundary model of `hash/fnv` (minibolt's `metaValid` in
  `examples/bboltfs/Meta.lean`).
- One `File.WriteAt`/`PWriteFinish` spec parametric in the restriction, giving its fact.
- A transfer lemma `WP_{OsStep} ⊢ WP_{OsStep ∧ P}`, for restrictions that keep every reducible
  configuration reducible, so that the existing OsFs specs (WAL, snap) are reused.
- P2's scope: every file, at the meta offsets `16..80` and `4112..4176`.
- Every closed result then carries the restricted semantics, visibly, as `BootCrashSafety`
  carries P1.

**(b) OsFs's `pwrite` all-or-nothing in-process for one aligned OS page.** Torn metas then arise
only at crashes, where P1 already covers them. Precisely:

**What changes:**
- `GooseLang/Ext/OsFs/Impl.lean`, the `PWriteFinish` rule (now `k ≤ data.length ∧ (k =
  data.length ∧ e = 0 ∨ e ≠ 0)`). It gains the conjunct `off % osPageSize = 0 ∧ data.length ≤
  osPageSize → k = 0 ∨ k = data.length`: a write within one aligned OS page writes all of its
  bytes or none, whatever the errno. The header's "a failed `pwrite` wrote a prefix" gets the
  exception.
- `GooseLang/Ext/OsFs/Write.lean`: `wp_osPWriteFinish`'s post gives the fact (`k = 0 ∨ k =
  data.length` for such a write).
- `os.File.WriteAt`'s spec (`Spec/os/File__WriteAt.lean`) passes it on: a one-page aligned
  `WriteAt` that fails changed nothing.
- `GooseLang/Ext/OsFs/Tests.lean`: a test that a torn one-page write is not a step.
- Unchanged: the crash relation `OsCrash`, so a crash can still tear a page in the durable image
  (P1's case), and `PWriteStart`.

**Is it true of Linux** (regular files on ext4/xfs, buffered I/O, which is how OsFs is scoped)?
`pwrite` goes through `generic_perform_write` (`mm/filemap.c`). It loops over the page-cache
folios the range covers. For each one it calls the filesystem's `write_begin`, which allocates
or reserves the block, then `copy_folio_from_iter_atomic` (a `memcpy` from the user buffer into
the page), then `write_end`. For a range inside one aligned page:
- **The loop runs once.** It checks `fatal_signal_pending` only before a page, so a signal cannot
  cut the page.
- **`write_begin` failure** (`ENOSPC`, `EDQUOT`, `ENOMEM`) returns before any byte is copied: 0
  bytes.
- **A short copy** happens only when the user buffer faults, and is retried after
  `fault_in_iov_iter_readable`. It stays short only if the source is unmapped (`EFAULT`), which a
  Go slice never is.
- **`write_end`** with a short copy into a non-uptodate folio returns 0, so the page is not
  half-written either.
- **Media errors (`EIO`)** surface at writeback, through `fsync`/`fdatasync`, not in `pwrite`;
  the page cache keeps the whole new page.
- **Large folios** do not change this: the copy into one folio is one call.

So for a one-page aligned buffered write, Linux's in-process outcome is all or nothing, and (b)
removes only behaviours Linux does not have. Two consequences follow:
- Concurrent mapped readers could see a `memcpy` in progress. OsFs already makes such loads stuck
  (holes), and bbolt reads metas only under `metalock`.
- The model stays "never more defined than Linux" only for this aligned case. Unaligned or
  multi-page writes keep their prefixes (bbolt's data pages are multi-page and may tear).

**bbolt facts that then hold without P2** (bbolt writes each meta as one `pageSize = 4096` buffer
at offset `id · 4096`, exactly one aligned OS page):
- `Commit`'s error post ("took effect or not"): the meta page is either wholly the new one,
  which is valid and current (the fork's `rollback` keeps it), or untouched.
- The parity maintenance: a failed commit leaves the current meta valid and current.
- `isBolt`'s "at least one valid meta", hence no `meta()` panic in `Begin` or in `rollback`.
- `fileHolds`' meta clauses, kept in-process.

What still needs P1: only a crash spec (out of scope here), whose torn durable metas P1 already
handles for minibolt. No FNV model is needed in-process. `hash/fnv` stays as it is: names-only,
with `Validate`'s result taken from the bytes by a trusted spec.

**Recommendation in round 8:** (b). **The user chose (a): D22.**
- It is true of Linux by the `generic_perform_write` argument above.
- It changes one rule of this repository's own trusted model, plus its spec.
- It needs no Lean FNV, no second semantics and no transfer lemma.
- No closed result gains a premise.
- Its cost is a trusted-model change, reviewed like D17's model. (a) keeps the model as it is,
  but puts a probabilistic premise in every closed result above bbolt.


## Changes in round 7 (after `review-6.md`)

Round 6's text is kept as `candidate-r6.lean`.

**Decided by me** (the user asked that spec decisions with clear guidance be made here; each
cites its basis):
1. **D21: the `WriteTo` fork fix** (precedent: D18, and raft's fork fixes for real Go bugs).
   - The bug, reproduced at upstream `main`: `issues/bbolt-writeto-meta-parity.md`, with a
     fault-injection test. The in-process torn-write variant is testable through `db.ops.writeAt`.
   - The fix: `d21/writeto.diff`.
   - The parity clause stays in `fileHolds`.
2. **D20': the logger contract**, restated for Go's `fmt`:
   - `fmtVerbs` restricts format strings to bare `s v q d t x`;
   - `logArgOk` follows `fmt`'s method precedence (`Format`, then `Error`, then `String`), under
     method verbs only;
   - two fork commits, `%w` → `%v` (upstream's) and a no-op `discardLogger`;
   - one trusted axiom, `wp_Options_String`.

   Principles: "sound: true of the code" (a trusted statement must hold for every input it
   admits); "complete": every argument bbolt logs has a source (the list under D20'); "the spec
   of an API": a contract any logger implementation can meet. The closed-list alternative (an
   enumeration of bbolt's argument types) would couple the API to bbolt's call sites without
   being simpler.
3. **`fileHolds`**:
   - `hwm · pageSize ≤` the file's length;
   - the current meta's txid strictly higher than any other valid meta's;
   - **P2**, the named premise "a torn meta in the page cache does not validate". It is
     minibolt's P1 (`BootP1.lean`, `CrashP1.lean`) moved from the crash relation to the step.
     - Where: a new step-restricted OsFs semantics, `GooseLang/Ext/OsFs/StepP2.lean`, local
       infrastructure.
     - Who supplies it: the end-to-end theorem, visible in its semantics, as P1 is.
     - It cannot be an assumption about FNV-64a itself, which is false for some inputs.
4. **Documentation:**
   - the stale `Open`/logger comment is replaced by `wp_Options_String`;
   - 49 `Errorf` sites;
   - D11's heading.

**Needs the user:** nothing new. D20' rests on D20, which the user approved in principle, and
its fork commits follow D18's precedent. The infrastructure items under D20' are ordinary work.

**Open:**
- filing the `issues/` and `nonissues/` drafts, now with `bbolt-writeto-meta-parity`;
- a review of round 7.


## Changes in round 6 (after `review-5.md`)

Round 5's text is kept as `candidate-r5.lean`.

1. **`fileHolds`: the current meta lies at page `txid % 2`** (finding 1).
   - Under OsFs a `pwrite` may stop after any prefix. A commit writes its meta at page
     `txid % 2`, which by the clause is not the current meta's page. So a torn write there leaves
     the current meta valid and current. A complete write is the commit point; this is the fork's
     `rollback` rule.
   - A partial write that covers the txid but not the checksum is invalid, barring an FNV
     collision.
   - The next commit after a failure has the same txid, so it writes the same other page again,
     and the parity holds.
   - Without the clause, the next commit can overwrite the only valid meta, and `db.meta()`
     panics.
2. **The synced freelist** (finding 2). It is of freelist type, its count and ids lie within its
   own extent, and the ids are distinct and in `[2, hwm)`.
   - Maintained: without `NoFreelistSync` the commit writes free plus pending ids into a
     freelist-type page sized for them. With it (etcd), the meta's freelist is `PgidNoFreelist`.
3. **Contents within extents** (finding 3). Element headers and key/value bytes lie within the
   page's own extent, and below `MaxAllocSize`. An inline bucket's page is a leaf whose elements
   lie within the bucket's value.
   - Maintained: `node.write` writes into a buffer sized by `node.size()`.
4. **`boltLogger` is an exposed method contract** (finding 4; new decision **D20**, below). Each
   of the methods bbolt calls (`Debugf`, `Errorf`, `Infof`, `Warningf`) is lent resources `R` for
   the call, under which each argument formats: plain values; `String()`/`Error()` methods
   needing `R` (`*Options` through `optsAt`, all 15 fields); and `[]byte` keys whose bytes `R`
   lends (`%q` in `Put`, `Delete`, `CreateBucket*`, `DeleteBucket`). `R` comes back.
5. **`boltTx_agree` is restated over one name.** `txSnap`, `boltTx_snap` and `txSnap_agree` are
   dropped (finding 5): no caller needs them, and without a name they need the registry D19
   rejected. The backend keeps `boltTx tx γ q (ro D)` where it kept `rtxSnap`.
6. **Documentation** (finding 6):
   - the target was then `goose-lean-v2` `b30879b2` (round 10: `b3e06648`, pinned since `44ed0aad76`);
   - D17 and D18 are committed, and `DefaultPageSize`'s fact exists (`PkgInit.lean:108-112`);
   - the old/bbolt table's forged-meta row now names D18;
   - `optsAt_nonnull`'s docstring covers both producers;
   - the corollary counts are consistent (8 exact, `Open_kv` a corollary under added premises,
     8 restated, 3 not corollaries, `Close_kv` a layer);
   - D13's `NoFreelistSync` wording is fixed;
   - the margin that `OptsM.ok` excludes etcd's `defrag`, which sets `OpenFile`, is stated.
     `defrag` is names-only in the backend's translation, so no spec here covers its bbolt
     calls. Proving it later needs `OptsM.ok` to admit a custom `OpenFile` with a contract over
     OsFs.
7. **Process** (finding 7): the `issues/` and `nonissues/` drafts are still to be filed in the
   repository. That is the coordinator's step, since this agent writes to scratch only.


## Changes in round 5 (after the user's D18 decision)

Round 4's text is kept as `candidate-r4.lean`.

1. **D18 decided: the fork change.** The candidate uses that variant only.
   - `fileHolds` assumes nothing of user values. The no-fork clauses are gone.
   - The exact Go change, a diff of `getPageSize`, `getPageSizeFromFirstMeta` and
     `getPageSizeFromSecondMeta` against v1.5.0, is under D18 and in `d18/getpagesize.diff`.
     The patched file is `d18/db.go`. It builds, and v1.5.0's `TestOpen*` and `TestDB_Open*`
     tests pass with it.
2. `nonissues/bbolt-getpagesize-probes-user-data.md` is finalized as a double-fault hardening
   finding. Only when both meta reads fail, or both metas are damaged, can a checksum-valid fake
   meta in a user value at offset 8 KiB or more be picked. A normal crash damages at most one
   meta.
3. `BoltName`'s `Pos.Countable` is defined (`boltName_countable`, `countableOfLeftInverse` over
   `(gs, ns)`, as mvcc's `dbNames_countable` is).
4. `optsAt_other_rd`'s placeholder helpers are replaced by one axiom per Go type:
   `optsAt_bool_rd`, `optsAt_int_rd`, `optsAt_freelist_rd` and `optsAt_timeout_rd`.

The frozen-candidate summary is at the end of this file.

## Changes in round 4 (after `review-3.md`; nothing blocking)

Round 3's text is kept as `candidate-r3.lean`.

Decisions taken by the user so far:
- **approved:** D7, D17 (with the Perennial float fix proposed separately), D1, D3, D4, D13, and
  D5 (the non-NaN `FillPercent` premise);
- **open in round 4, decided in round 5:** D18 (the fork change). Round 4 had kept both of its
  variants describable: `fileHolds` named the clause the
  no-fork-change variant adds.

What round 4 changed:
1. **D17's model holds for every input.**
   - `splitThresholdOk` gains the escape disjunct `2^53 ≤ pageSize`. From there,
     `float64(pageSize)` may round up, and a product of `2^63` or more converts to `MinInt64`.
     bbolt's `4096` never takes this disjunct.
   - The docstring now argues why the bound holds below `2^53`.
   - It moved out of the client API, into a section standing for
     `TrustedCode/go_etcd_io/bbolt.lean`.
2. **`Open` against the option axioms** (review 3, finding 2).
   - New axiom `optsAt_nonnull`, so the `DefaultOptions` branch is dead.
   - New read axioms at any fraction: `optsAt_readOnly_rd`, `optsAt_mlock_rd`,
     `optsAt_pageSize_rd`, `optsAt_mmapFlags_rd`, `optsAt_openFile_rd` and `optsAt_logger_rd` give
     the `OptsM` value; `optsAt_other_rd` gives some value of the field's type for the rest.
   - All are trusted, under D13. They fit the infrastructure's choice to keep `Options` and
     `DefaultOptions`' initializer axiomatized until `Open`'s proof, when they become lemmas.
   - Noted as open: with a non-nil logger, `Open` formats `options` with `(*Options).String()`,
     so `boltLogger`'s contract must allow reading every field.
3. **`fileHolds`' page facts are over extents** (`id .. id + overflow`).
   - Every tree page's extent and the synced freelist page's extent lie in `[2, hwm)` and within
     the file's length: OsFs makes a mapped load past the end of the file stuck.
   - The extents are pairwise disjoint and disjoint from the synced freelist's ids.
   - The maintenance argument covers extents too. The separate `0xFFFF` clause is dropped,
     since the extent bound implies it.
4. **`BoltName` is a structure** `{ gs : List GName, ns : Namespace }`, deriving `Inhabited` and
   `DecidableEq`, with `Pos.Countable`.
   - This is what `InvStore.lean`'s `bNames_countable` and `InvApplier.lean`'s `Inhabited`
     derivations need once `BNames.db : BoltName`.
   - Sealing still hides what `gs` means.
   - `γ.ns` is now a field.
5. **Metas** (D16). "Two valid metas" becomes at least one valid meta, the current one the valid
   meta with the higher txid, and no other valid meta at page 0's probe offsets 1024 and 2048.
   - A failed commit keeps this; it did not keep "two valid metas".
   - (Round 4: under D18's no-fork variant, `fileHolds` also had the forged-meta clause. That variant was dropped in round 5.)
6. **Minor.**
   - The `↑N ## ↑osN` docstring is corrected. The commit update fires just after the `pwrite`,
     under `metalock`; the premise lets bbolt's own invariants stay open across OsFs steps.
   - `optsAt_discard_persistent` is in the moved list.
   - **Infrastructure dependency:** `internal/common`'s package fact must give
     `DefaultPageSize = 4096` (`os.Getpagesize`, linux/amd64). It is still `True` per the
     coordinator, although `notes/bbolt-v2-infra.md` describes a `SPECIAL` entry for it. Every
     page bound rests on it: `OptsM.ok`'s default page size, D17's `t ≤ pageSize`,
     `bboltEntryMax`'s margin, and the element count.
   - The token-flow note now says `begin(true)` pays its `Stats` with `statSlot γ none`.

## Changes in round 3 (after `review-2.md`)

Round 2's text is kept as `candidate-r2.lean`.

1. **Float-to-int conversion** (finding 1). I checked Perennial at the pin and at `origin/lean`
   (`b3e996d84`): `convert_float64_to_integer` still gives an `ArbitraryInt` for every value
   (`Golang/Defn/Predeclared.lean:1001`), and `float64Mul`/`float64Leb` are uninterpreted.
   - The recent bbolt-driven commits (unsafe memory R1 to R3, byte-level integers and floats,
     `sync.Pool`) do not interpret float-to-int conversions.
   - New decision **D17**: a fork helper `splitThreshold`, `trusted` with a `TrustedCode` model
     (`splitThresholdOk`: for a NaN, any int; otherwise `0 ≤ t ≤ pageSize`). The general
     Perennial fix is proposed separately.
   - `bboltEntryMax` and `boltTx_fill` rest on it, as their docstrings now say. `rebalance`'s
     unclamped threshold may stay arbitrary.
2. **`fileHolds`' shape facts** (finding 2). Added:
   - each branch key is exactly its child's first key;
   - every branch has at least two elements;
   - every page's elements end below `MaxAllocSize`, with fewer than `0xFFFF` of them;
   - every page is of leaf or branch type, below the high-water mark, with no sharing and none
     in the freelist.

   The maintenance argument is in "fileHolds is kept by Commit" below. With these facts, the
   `recursivelyCheckBucket` that a failed `Commit`'s `freepages` runs finds nothing.
3. **The forged-meta probe** (finding 3). New decision **D18**: a fork change in which
   `getPageSize` returns read errors instead of probing. The clause is dropped from `fileHolds`
   under D18, and the alternative is stated. Drafted as
   `nonissues/bbolt-getpagesize-probes-user-data.md`.
4. **Option axioms** (finding 4). `optsAt_bool` and `optsAt_int` are restated without `Mlock` and
   `MmapFlags`. New setter axioms `optsAt_mlock` and `optsAt_mmapFlags` update their fields.
   `optsZero` and `optsZero_ok` are restated. All are trusted, under **D13 (changed)**.
   `noFreelistSync` is dropped (finding 7).
5. **`Cursor.Last` hangs** in a writer once every leaf is empty (finding 5). Its docstring now
   notes the hang. Drafted as `issues/bbolt-cursor-last-empty-leaves-hang.md` with the
   reviewer's test, which also hangs at upstream `main` `a4ef197` (go1.27.3, 5 s timeout).
6. **Agreement laws dropped** (finding 6). Without a registry they are not provable: a registry
   `db ↦ γ` would have to be a package-initialization fact. Instead the clients carry `γ`: the
   backend's `BNames` already has `γ.db` beside every `isDB db`, so the layer is `isDB db :=
   isBolt db γ.db`. New decision **D19**.
7. **Minor** (finding 8):
   - `Open` takes `⌜↑N ## ↑osN⌝`, because the commit update fires inside an OsFs step
     (**D15, changed**).
   - The txid invariant is `< 2^63` (`t₀ < 2^62` plus the receipts).
   - `2^29`'s docstring now says it is a chosen power of two, not a necessity.

## Changes in round 2 (after `review-1.md`)

Round 1's text is kept as `candidate-r1.lean`.

1. **`Cursor.Prev` is scoped to read transactions** (`⌜T.rw = false⌝`), finding 1.
   - In a write transaction, Go's `prev` does not skip the empty leaves that deletes leave
     before `Commit`'s rebalance. It returns nil in the middle of the bucket.
   - This is a Go bug, reproduced at upstream `a4ef197`, and drafted as
     `issues/bbolt-cursor-prev-empty-leaf.md` with its test.
   - `Next`'s docstring now says its end position is the abstract one. Only a writer's `Prev`,
     which is no longer specified, could tell it apart.
   - Chosen over a weaker post or dropping `Prev`: the read-transaction spec is exact and costs
     nothing. etcd never calls `Prev`. (D14, new)
2. **A spare reader slot for `Commit`'s error path**, finding 2.
   - With `NoFreelistSync`, etcd's Linux default, `rollback()` runs `freepages()`, which
     `beginTx`s: an `mmaplock` reader slot nobody paid for.
   - `isBolt` now keeps one spare slot in `rwlock`'s resource, which only the writer reaches.
   - `Open`'s bound becomes `ThreadBoundLe GF (2^29)`: the next power of two that leaves room
     for the spare under `actualMaxReaders = 2^30 - 1`, and still met by `BuildServer`'s
     `2^28`. (D3, changed)
   - The rest checked for hidden reader slots, and none found:
     - `Tx.Check` is reached only with `StrictMode`, which clients can't set (item 7) — that also
       covers `Commit`'s other forks;
     - `loadFreelist`'s read in `Open` runs before the pool exists;
     - `Batch` is not specified;
     - `Close`, `Rollback` and `Commit`'s success path only take `Lock`s;
     - `freepages`'s goroutine gets its token from the fork.
3. **`OptsM` gains `mlock`, `mmapFlags` and `noFreelistSync`**, finding 3. `OptsM.ok` adds
   `mlock = false ∧ mmapFlags ∈ {0, MAP_POPULATE}`. These are scope restrictions of the model:
   `unix.Mlock` is names-only, and OsFs's `Mmap` takes only those flags.
   - Checked further: `InitialMmapSize` (etcd's 10 GiB) is harmless, because OsFs's `Mmap` can
     always fail with an errno, so it is never stuck. `Timeout` is harmless, because OsFs's
     `Flock` returns any errno, so `flock` loops or fails.
   - The backend then needs `Config.Mlock = false` (D13, new). `MmapFlags = MAP_POPULATE` is
     admitted.
4. **The fresh file and `fileHolds`**, findings 4, 5 and 10.
   - New law `fileHolds_new`: an absent file, or an empty one with no mapping, holds `∅`
     (`osMeta path 1 mo`).
   - `fileHolds`'s well-formedness now lists no empty non-root page, keys strictly sorted
     within and across pages, a non-empty branch, and the root holding only buckets.
   - "Every byte synced" is dropped: the in-process specs read the page cache. (D16, new)
5. **A namespace the caller chooses**, finding 6. `Open` takes `N`, the post says `γ.ns = N`, and
   every mask is `⊤ \ ↑γ.ns`. `boltN` is gone. (D15, new)
6. **Agreement laws**, finding 7: `isBolt_agree` and `boltTx_isBolt` (`txDB tx db ∗ boltTx tx γ
   q T ∗ isBolt db γ' ⊢ ⌜γ = γ'⌝`). With them, the backend's `isDB db := ∃ γ, isBolt db γ`
   feeds `DB.Stats` and `DB.Info`.
7. **`Tx.Commit` over `boltTx tx γ 1 T ∗ ⌜T.rw = true⌝`**, finding 8. The update is
   `<{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }>`, with no literal record. (D7, changed in
   form)
8. **`isBolt` owns `DB`'s exported fields**, finding 9, as documented in its docstring and in
   "Not covered". Clients must not write `StrictMode`, `NoSync`, `AllocSize` and the rest after
   `Open`. etcd writes none of them.
9. **Minor**, finding 11:
   - `statSlot`'s docstring now gives its soundness: the pool lends an (`mmaplock`, `statlock`)
     pair, and the whole transaction is needed.
   - D8's cost now says `[HasExt osFsExt]` is a variable of every spec over bbolt, and of their
     callers.
   - D12 is kept, with its draft in `nonissues/`.
   - `Close`'s post `True` and the unused `Q` of `Begin(true)` are left as they were (margins).

The full statements are in `candidate.lean` (beside this file). This file covers the design and
why it was chosen, what each spec rests on in bbolt's Go code, how the backend's 20 `_kv` axioms
follow from the new specs (or what changes for their callers), and the decisions that need the
user.

The specs describe bbolt v1.5.0 as translated from the goose fork `upamanyus/bbolt`
`goose-lean-v2` (`b3e06648`, pinned by `etc/goose.py` on `worktree-bbolt-v2` since `44ed0aad76`; round 10). The fork
carries two fixes, `2d39641` (from `issues/bbolt-commit-meta-error-frees-reader-pages.md`) and
the crash-safe `init`, plus D17's `splitThreshold` helper and D18's `getPageSize` change. **The `Commit`
spec is false of upstream v1.5.0 without `2d39641`** (D11).

## The design in one paragraph

A database is a persistent handle `isBolt db γ` that any goroutine may use. Its committed data
is client-owned ghost state `boltState γ q D`, which is fractional. bbolt's two linearization
points reach that state through logically atomic updates the client passes in:
- a read transaction's snapshot: `Begin(false)` copies the meta under `metalock` and fires a
  read update there;
- a commit: `Commit` writes the meta page under `metalock` and fires the commit update there.

There is no write token. `Begin(true)` blocks on `rwlock`, and while a write transaction is live
the committed data is the one it began at. That is a law (`boltTx_base`), so `Begin(true)` needs
no update.

A live transaction of either kind is a single fractional predicate `boltTx tx γ q T` over a pure
view `T` with four fields: writable, base, contents and bucket generations. This gives one spec
per function: `Tx.Bucket`, `Bucket.Get`, `Bucket.Cursor` and the cursor moves each serve both
kinds of transaction. Reads accept any fraction; changes need all of it.

A read transaction keeps its caller's `threadTok` from `Begin(false)` until `Rollback`. That
token is the transaction's `mmaplock` reader slot, the bounds-plan pattern, and `Open` takes
`ThreadBoundLe GF (2^29)`, which leaves one spare slot for the writer's `freepages`.
`Open` also takes a namespace of the caller's choosing.

The backend's `ownDB db γ D` becomes the definition `isBolt db γ ∗ boltState γ 1 D`, and its
`_kv` axioms become corollaries, except where listed below.

## Vocabulary (`Spec/go_etcd_io/bbolt/Api.lean`, sealed)

| predicate | kind | meaning |
|---|---|---|
| `isBolt db γ` | persistent | the database handle: its locks, mapping, file, freelist and reader pool, the commit counter, and the authority of the committed data |
| `boltState γ q D` | fractional, timeless | the client's view of the committed data. A read needs some fraction, a commit all of it |
| `boltTx tx γ q T` | fractional for a fixed `T`, timeless | a live transaction with view `T`. A read transaction's whole holds the reader slot |
| `txDB tx db`, `txDone tx` | persistent | as today |
| `boltBkt tx b n g` | persistent | `tx`'s handle `b` of bucket `n` at generation `g` (this is `wBkt`, now for both kinds) |
| `boltCur tx c T es pos` | exclusive | a cursor made at view `T` over the entries `es` |
| `txBytes tx s b` | persistent | as today. `txBytes_acc` now takes any `boltTx` fraction |
| `fileHolds path D` | exclusive | moved from the backend; defined over the OsFs file extension (its docstring lists the well-formedness it includes) |
| `optsAt`, `OptsM`, `dbCloseOk` | | moved from the backend (the option axioms restated, D13) |
| `boltLogger l` | persistent, exposed | the method contract of D20' (round 7; round 8: by signature, errors through `fmtErrorOk`) |

The pure helpers are `TxView` with `ro`, `wr`, `setBkt` and `dropBkt`; `bktEnts`; `seekIdx`;
`curAt`; and the named bounds `maxKeySize` and `bboltEntryMax = 2^28`.

The laws:
- fractions, agreement, validity and timelessness for each predicate;
- `boltTx_base`: a live writer's base is the committed data;
- `boltTx_nonnull`;
- `boltTx_fill`: `FillPercent` is written back only as a non-NaN value;
- `txBytes_acc`;
- the layer lemmas `boltState_read_au` and `boltState_commit_au`, for a client that owns the
  whole state, which is the backend's case.

## The four design questions

### 1. Concurrency

**Reads.** `Begin(false)` (`db.go` `beginTx`) takes `metalock`, then `mmaplock.RLock`, then
copies `db.meta()`. Writers write the meta under `metalock` too (`tx.go` `writeMeta`), so the
copy is an atomic read of the committed data. The spec fires a read update there:
`AU <{ ∃∃ q D, boltState γ q D }> <{ boltState γ q D, COMM Q D }>`. The reader then reads `D`
for its whole life. This is bbolt's MVCC: pages a live reader may see stay pending
(`ReleasePendingPages`). A one-shot update, not `□`, because `Begin` linearizes once. On an
error the update comes back.

**Writes.** `Begin(true)` (`beginRWTx`) blocks on `rwlock`. `rwlock` is a `sync.Mutex`, so the
call blocks rather than fails, which a weakest precondition allows. A write token would add
nothing for soundness and would stop concurrent writers that each just call `Begin(true)`, which
the planned concurrent test does. **No `wrTok`.**

While the writer is live it holds `rwlock`, and nobody else can commit. So the committed data
equals the writer's `base`. This is a law, `boltTx_base`, not an update, and the client reads it
off its own `boltState` whenever it likes. `S` (contents) and `D` (base) both live in the
writer's view `T`; the committed data is only in `boltState`.

**Commit.** The commit point is the meta page's `pwrite` under `metalock`. The update is
`AU <{ ∃∃ D', boltState γ 1 D' }> <{ ⌜D' = D⌝ ∗ boltState γ 1 S, COMM Q }>`. The library gives
back `⌜D' = D⌝` because the client cannot use `boltTx_base` inside the update: it has already
handed `boltTx` to `Commit`.

**Commit errors.** Every error path rolls back and closes the transaction. The commit has taken
effect if and only if the meta page reached the file before the error (the
`fdatasync`-after-meta case, or a short write that completed the meta's bytes). On the fork,
`2d39641` keeps the freed pages pending in that case, and new readers see `S`. Otherwise the
freelist is reloaded and the data is still `D`. So the error post is `Q ∨ AU`: the update was
fired, or it comes back. That is a split on the outcome, not two alternative specs, and neither
side always holds.

**Why `boltState` is fractional.** A reader's update works with any fraction. A client such as
the backend can then leave part of the state in an invariant for readers outside its lock (see
`backend.Snapshot` below) and keep the rest under the lock, which the commit joins.

**`Close`.** It takes `rwlock`, then `metalock`, then `mmaplock`, so it waits for every
transaction. After it, `beginTx` and `beginRWTx` return `ErrDatabaseNotOpen`. A second `Close`
returns nil. So the persistent handle is enough. `Close` racing transactions is safe: a live
transaction excludes it, which is why `DB.Info` needs one.

### 2. Good for etcd

See "The backend" below. In short:
- 8 statements are exact corollaries once the backend's names are definitions (round 6 count,
  matching the summary table; `DB.Begin_kv` counts once for each mode).
- `Open_kv` is a corollary under added premises (`N`, the instances, `Config.Mlock`, and `[HasExt osFsExt]` as every `_kv` corollary; `osInv` is inside `fileHolds` since round 9).
- 8 need a mechanical restatement: `txLive tx q ∗ rtxSnap tx D` becomes `boltTx tx γ q (ro D)`,
  and `rtxStats` is dropped.
- 3 are not corollaries, because of new premises: `Begin(false)`'s token (D1), `DB.Stats`'s slot
  (D2), and `Put`'s bound (D4).
- `DB.Close_kv` stays a trust-boundary layer, because of `dbCloseOk`.

The new specs also make `backend.Snapshot` provable. It is an axiom today because the
exclusive `ownDB` could not serve a read transaction begun outside the batch lock.

### 3. The refuted and weak points

- **FillPercent NaN.** `boltTx_fill` takes the field back only as a non-NaN value
  (`float64IsNaN` defined on the bits). `splitTwo` clamps every other value, including ±Inf. The
  backend's `0.9` discharges it by computation (D5).
- **Put's size bound.** `Put` checks only `len(value) ≤ MaxValueSize`.
  - What bbolt can actually store depends on the entry's neighbours. A leaf of at most four
    entries is never split, and a page's buffer, rounded up to the page size, must stay below
    `MaxAllocSize = 2^31 - 1`.
  - With four entries of `E` bytes each, the page takes `4(E + 16) + 16` bytes plus the rounding,
    so `E ≲ 2^29 - 2^10` is the most one can claim regardless of neighbours.
  - At the default 4 KiB page, `bboltEntryMax = 2^28` (key plus value) is safe with room to
    spare. It is also the old proof's `SpillFit` bound.
  - The premise replaces the false `MaxValueSize` arm. The key's empty and too-large errors stay
    as a case split, so the code checks them rather than the premise (D4).
  - Other page sizes: `Open` keeps the default page size (`OptsM.ok`). From about 1 MiB a page
    holds 65535 small entries and `Commit` panics (`nonissues/bbolt-large-page-size.md`). An
    existing file's page size comes from its meta, so `fileHolds` fixes it to the default.
- **Deleted-bucket handles.** Generations, as on `lean` (`TxView.gen`, `dropBkt`). Every bucket
  operation takes the handle at `T.gen n`.
- **Returned slices.** `txBytes`, readable with any live fraction (`txBytes_acc`).
  - What makes this sound: a remap needs `mmaplock.Lock`, which waits for readers, and the writer
    remaps only inside its own `Commit`, which needs all of `boltTx`. `Close` waits for every
    transaction. Before unmapping, `mmap` dereferences the writer's mmap-backed inodes into its
    own memory.
  - A value slice from `Get` can't be passed to `Put`, which needs `↦*□`. A key slice can be
    passed to `Delete` (`own = false`).
- **Close racing transactions.** Safe, as in question 1. `DB.Info` keeps its live-transaction
  premise, and `DB.Stats` is guarded by `db.stats != nil` and `statlock`.
- **old/bbolt safety findings**:

  | finding | where it went |
  |---|---|
  | file well-formedness: nested bucket in an inline one, a page shared by two parents, empty first key, freelist id or page past the high-water mark, an inline bucket's value of 16 bytes or less, `grow` with the file longer than the mapping | **`fileHolds`'s definition**, then the DB invariant |
  | the forged meta at `getPageSize`'s probes | **D18's fork change** (a meta read error is returned; probing past page 1 needs both metas checksum-invalid, and `fileHolds` requires one valid meta) |
  | page size of `2^32` or more (`mmapSize`), above `MaxAllocSize` (`Tx.write`), or about 1 MiB (65535 inodes) | `Open`'s `OptsM.ok` (default page size), and `fileHolds` for existing files |
  | more than `2^30 - 1` readers | `ThreadBoundLe GF (2^29)` on `Open`, plus the reader token on `Begin(false)`, plus the writer's spare slot (D1, D3) |
  | empty non-root pages (round 2) | `fileHolds` (committed trees). Writers' `Prev` is excluded (D14) |
  | txid wrap (old proof: ids below `2^62`) | `ReceiptBoundLe GF (2^62)` on `Open`, and `fileHolds`'s txid below `2^62` (D3) |
  | `node.put` needs non-empty keys | `Put`'s case split. `fileHolds` excludes empty keys |
  | `Rollback` inside `View` panics (`managed`) | `View` and `Update` are not specified (D10) |
  | `recursivelyInspect` nil dereference | `Inspect` is not specified |
  | failed remap leaves `db.data` nil | fixed upstream (`ErrInvalidMapping`). `Begin`'s error branch |
  | `writeMeta` reached the file then failed | fixed on the fork (`2d39641`). `Commit`'s `Q ∨ AU` |

### 4. Scope

- **Top-level buckets only.** etcd has no nested buckets, and `Data` cannot express them. A file
  with nested buckets satisfies `fileHolds` for no `D`. No spec creates one: `Bucket.CreateBucket`
  is not specified, and the root holds only buckets.
- **Mutations only on write transactions.** On a read transaction Go returns `ErrTxNotWritable`,
  which the specs leave out (`T.rw = true` is a premise). This is a scope restriction: no client
  does it, and a corollary could add the error arm.
- **Durability and crashes.**
  - Perennial's own `Fs` extension is a whole-file toy. This repository's OsFs (Linux file)
    extension models `pread`/`pwrite`/`fdatasync`/`mmap`, nondeterministic errnos and crash
    images. `examples/bboltfs`'s minibolt is the acceptance test that it suffices for bbolt.
  - The proof should go over OsFs (D8). `fileHolds` is then defined over `osMeta`/`osBytes`, and
    `Open` took `osInv` until round 9; it is now inside `fileHolds`.
  - The specs are in-process only: no crash spec. A durable layer would follow raft's durable-API
    lesson: the client owns the durable state, and the commit point after `fdatasync` is an
    update. It is listed, not designed.
- **What `Open` assumes of the file.** `fileHolds path D`, whose docstring gives the
  well-formedness. A missing or empty file is `fileHolds path ∅` by the law `fileHolds_new`
  (round 2).

## The specs, against the Go code

| spec | key facts in Go (v1.5.0, `goose-lean-v2`) |
|---|---|
| `Open` | `options == nil` uses `DefaultOptions`. The specs require non-nil options (`optsAt`), which etcd always passes; this is a margin. A non-read-only open runs a `Begin(true)`/`Commit` when the freelist was not synced (internal). `flock` blocks until the lock is free |
| `DB.Close` | three locks, then `close()`. Every error comes from a system call (`munmap`, `funlock`, `file.Close`) |
| `DB.Begin` | read: `metalock`, then `mmaplock.RLock` (held until `removeTx`), then `!opened` or `data == nil` is an error. Write: `readOnly` is an error (excluded by `OptsM.ok`), `rwlock` (held until `close`), then the same two checks |
| `Tx.Commit` | `tx.db == nil` gives `ErrTxClosed` and `!writable` gives `ErrTxNotWritable`; the pre excludes both. Spill, freelist, grow and write errors lead to `rollback()` (old data). A `writeMeta` error leads to `rollback()`, which on the fork keeps the commit if its meta is current |
| `Tx.Rollback` | read: `removeTx` (the `RUnlock` returns the slot, hence the token). Write: `freelist.Rollback` then `close` |
| `Tx.Bucket` | write: caches the child in `root.buckets` (a map write), so all of the transaction is needed. Read: no cache, reads only |
| `CreateBucket(IfNotExists)` | checks only `len(key) == 0` (`ErrBucketNameRequired`). **No length check, despite the doc** (finding 1). Root keys are all buckets, so `ErrIncompatibleValue` is unreachable |
| `DeleteBucket` | absent gives `ErrBucketNotFound`. It frees the child's pages and deletes the cached handle; the generation is bumped |
| `Bucket.Get` | `seek`; a nil value for an absent key. A nil value put earlier also reads as nil: Go can't tell these apart (margin) |
| `Bucket.Put` | errors in order: `ErrTxClosed`, `ErrTxNotWritable`, `ErrKeyRequired`, `ErrKeyTooLarge`, `ErrValueTooLarge`. It clones the key and keeps the value slice |
| `Bucket.Delete` | an absent key gives nil. Only reads the key |
| `Bucket.Cursor` | `IncCursorCount` is atomic in v1.5.0. **So `rtxStats` was the proof's bookkeeping, not bbolt's need**: it is dropped |
| `Cursor.Seek/First/Last/Next/Prev` | `next` at the last element "stays there" and returns nil; `Seek` past the end leaves the index past the last. So `Prev` differs by how the end was reached (finding 2), and the specs model it exactly. `Last` of an empty bucket sets the index to −1, and every later move returns nil |
| `Tx.Size`, `Tx.DB` | read `tx.meta`, `tx.db`, `db.pageSize`; immutable while the transaction is live |
| `Tx.Stats` | non-atomic copy of atomic counters, so the transaction must be done |
| `DB.Info` | `Assert(db.data != nil)`, read without `mmaplock`, so a live transaction is needed. The result is a fresh allocation: `i ↦ v`, stronger than today's `↦□` |
| `DB.Stats` | `statlock.RLock`: a reader slot (D2) |

## `fileHolds` is kept by `Commit` (round 3)

The argument for each clause, checked case by case against `node.go`, `bucket.go` and `tx.go`
(not yet a proof). The reviewer could not confirm the map-iteration-order independence of
`rebalance`.

- **Exact branch keys.** `node.read` sets a node's key to its first key. Every node `Put` or
  `Delete` changes is reached through `Cursor.node()`, which materializes its ancestors. `spill`
  writes each materialized node's pieces and calls `parent.put(oldKey, piece.inodes[0].key, …)`.
  A child that is not materialized keeps its page and its exact parent element from the file.
- **At least two elements per branch, and no empty non-root page.** These hold whatever the
  thresholds:
  - split pieces have at least `minKeysPerPage = 2` elements (`splitIndex`);
  - `rebalance` removes an empty node (`numChildren() == 0`);
  - it merges a node with fewer than `minKeys` (2 for a branch) into a sibling;
  - it collapses a root branch with one child.
- **Pages below `MaxAllocSize` and under `0xFFFF` elements.** This needs `splitThresholdOk`'s
  `t ≤ pageSize` (D17). A piece then takes at most two large entries plus elements up to the
  threshold, and pieces of at most four elements are never split, so a page is at most
  `4·(bboltEntryMax + 16) + 16 + pageSize`. With the default page size and entries of at least
  17 bytes, a page has under 256 elements.
- **No sharing, below the high-water mark, not in the freelist.** `spill` allocates fresh pages
  (`tx.allocate`) and frees the old ones as pending, which a reader sees until it ends. The
  freelist is written after the spill (`commitFreelist`).
- **`freepages`' check** (a failed commit with `NoFreelistSync`). `recursivelyCheckBucket` over
  the *committed* tree reports multiple references, unexpected page types, pages above the
  high-water mark and key-order violations. It also checks keys against the parent's bounds,
  which exact branch keys imply. The `nofreed` map it passes is empty. A well-formed tree gives
  no report.
- **Metas (round 6).** The current meta lies at page `txid % 2`. `init` writes txid `i` at page
  `i`, and a commit writes `txid + 1` at the other page. A torn write there leaves the current
  meta valid; a complete one makes it current, at its parity.
- **The synced freelist (round 6).** `commitFreelist` allocates a page sized for the free and
  pending ids (`EstimatedWritePageSize`) and writes them distinct and in `[2, hwm)`. With
  `NoFreelistSync` there is none.
- **Contents within extents (round 6).** `node.write` writes into the buffer `spill` allocated by
  `node.size()`. An inline bucket's value is `Bucket.write()`'s leaf page.
- **txid.** It stays below `t₀ + #commits < 2^62 + 2^62` (`ReceiptBoundLe GF (2^62)` counts
  commits), so it never wraps.

## The backend: each `_kv` axiom against the new specs

The layer (`InvBbolt.lean` would turn from axioms into definitions):
- `ownDB db γ D := isBolt db γ ∗ boltState γ 1 D`
- `wrTok γ := emp`
- `isDB db` becomes `isBolt db γ.db` (D19, round 3)
- `ownWTxG tx γ D S G := boltTx tx γ 1 {rw := true, base := D, cur := S, gen := G}`
- `wBkt := boltBkt`
- `ownCur tx c es pos` gains the view `T`
- `fileHolds`, `optsAt`, `OptsM`, `boltLogger` and `dbCloseOk` move to bbolt's API and are
  re-exported

`DBNames` becomes `BoltName` (the `γ.db` field of the backend's `BNames`). `wrTok` has no uses
beyond the specs, and nothing uses its exclusivity.

| `_kv` axiom | derivation from the new spec |
|---|---|
| `Open_kv` | **a corollary under added premises**, given the `ThreadBoundLe GF (2^29)` and `ReceiptBoundLe GF (2^62)` instances (D3; etcd's closed results have `2^28` and `2^48`, which imply them), `[HasExt osFsExt]` (D8, as every `_kv` corollary), a namespace (D15), and `Config.Mlock = false` with `MmapFlags ∈ {0, MAP_POPULATE}` in `OptsM.ok` (D13) |
| `DB.Stats_kv`, `DB.Info_kv`, `DB.Close_kv` (round 3) | `isDB db` becomes `isBolt db γ.db`, the name the backend already carries in `BNames` (D19); the statements take `γ`. To check against each `isDB` use (`InvBatch`, `InvBackend`, `HooksLoeb`, `NewAlloc`, `backend__Close`: in each, `γ : BNames` is in scope) |
| `DB.Begin_kv` (write) | **exact**: `Begin(true)`, then `boltTx_base` with the owned `boltState` gives `base = D` |
| `DB.Begin_kv` (read) | **not a corollary**: needs a `threadTok` (D1); `boltState_read_au` supplies the update. Post: `boltTx tx γ 1 (ro D)` instead of `txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx` |
| `Tx.Commit_kv` | **exact**: `boltState_commit_au` with `D = T.base` and `S = T.cur`, where `T` is the record `ownWTxG` unfolds to; success gives `ownDB db γ S`. The old error branch is weaker (it drops `Q ∨ AU`) |
| `Tx.Rollback_kv` | restated (`boltTx` in place of `txLive ∗ rtxSnap`); drops the returned token |
| `DB.Close_kv` | **stays a trust-boundary layer**: the proved `Close.spec` plus the assumed `err = nil ∨ ¬ dbCloseOk`. The proved spec can't produce `¬ dbCloseOk` over a model where the system calls fail. Only `storage.snapOpensOk`'s callers need it (PRINCIPLES: "the exception is the trust boundary") |
| `DB.Info_kv`, `Tx.Size_kv`, `Tx.DB_kv` | restated (`txLive tx q` becomes `boltTx tx γ q T`). `Info` is stronger |
| `DB.Stats_kv` | **not a corollary**: needs `statSlot` (D2) |
| `Tx.Stats_kv` | **exact** |
| `Tx.Bucket_kvr` | restated: `rtxStats` dropped, `rBkt tx b es` becomes `boltBkt tx b n 0` plus `D.lookup n = some m`, and `es = bktEnts m` |
| `Tx.Bucket_kvw` | **exact** |
| `Tx.CreateBucketIfNotExists_kv` | **exact** (the old `0 < n.length` premise selects the success arm) |
| `Tx.DeleteBucket_kv` | **exact** (`T.dropBkt n` unfolds to the old post) |
| `Bucket.Put_kv` | **not a corollary**: the new premise `kb.length + vb.length ≤ bboltEntryMax` (D4). The old key premises select the success arm |
| `Bucket.Delete_kv` | **exact** |
| `Bucket.Cursor_kvr` | restated (`rtxStats` dropped) |
| `Bucket.Cursor_kvw` | **exact**, and stronger: `boltTx` stays with the caller. The old wand shape follows |
| `Cursor.Seek_kv`, `Cursor.Next_kv` | restated: `boltCur` carries `T`, and the pre adds `boltTx tx γ q T` where the old one had `txLive tx q`. `Next` now also covers an unpositioned cursor and stays at the last element (the old `min (i+1) len` described the same observations) |
| `ownWTxG_fill` (law) | restated with the non-NaN premise (D5); `0.9` by `decide` |
| `ownWTxG_live`, `ownWTx_live` | **gone**: `txBytes_acc` takes the writer's `boltTx` directly |
| `rtxStats_excl` | **gone**: `ReadLemmas.stats_take`/`stats_give` and the `γ.txb` token of `intvInv` can go |

**What the backend's proofs change**:
- about 10 files restate `txLive tx q ∗ rtxSnap tx D` as `boltTx tx γ q (ro D)`: `InvBackend`
  (`intvInv`, `rdShare`), `ReadSide`, `ReadLemmas`, `NewAlloc`, `backend__begin`,
  `newBatchTxBuffered`;
- the `rtxStats` machinery is deleted;
- `unsafePut` needs the entry bound from its callers (D4);
- the thread-token flow (D1, D2):
  - `backend.New` takes a `threadTok` and returns one;
  - in `newBackend` the token goes to the first read transaction, and `begin` calls `Stats`
    with that transaction (D2's second form);
  - the fork of `run` gives the forker a token, which `New` returns;
  - `run` exits with the token of the rollback goroutine it forks in `CommitAndStop`;
  - in `unsafeCommit`, the fork of the rollback goroutine gives the committer the token the
    new `begin(false)` takes, and the goroutine exits with the old transaction's token;
  - `begin(true)` (from `batchTx.commit`) also calls `Stats`. With no read transaction, it pays
    with `statSlot γ none`, the token it holds at that moment (the creator's in `newBackend`, the
    fork's in `unsafeCommit`), given back before `begin(false)` takes it (round 4);
- `backend.Snapshot` (an axiom today) becomes provable, if the backend keeps a fraction of
  `boltState` in an invariant that its out-of-lock reader can open. Its spec would also take a
  `threadTok` that the snapshot holds until `snapshot.Close` (a later decision).

The examples: `examples/axiomcx/bboltnan`'s `Run` would no longer be provable, since
`boltTx_fill` refuses a NaN. That is the point of the repair.

## Decisions for the user

Each changes a spec that has clients, adds a premise, or adds client-owned ghost state.

**D7 (the core): client-owned committed state, by atomic updates, instead of exclusive
`ownDB` + `wrTok`.**
- Old: `ownDB db γ D` is exclusive, and `Begin`, `Commit` and `Open` pass it around. `wrTok γ`
  gates `Begin(true)`.
- New: `isBolt db γ` is persistent, plus `boltState γ q D`. `Begin(false)` and `Commit` take
  atomic updates over `boltState`. No `wrTok`.
- Alternatives:
  - (a) keep `ownDB`: sequential clients only; the concurrent test can't be proved and
    `backend.Snapshot` stays an axiom;
  - (b) a HoCAP predicate fixed at `Open` ("every committed state satisfies P"): ruled out by
    "TaDa, not HoCAP";
  - (c) a non-fractional `boltState`: the backend's `Snapshot` reader could not read beside
    the lock.
- **Recommend: new.**

**D1: `Begin(false)` takes the caller's `threadTok`, held by the read transaction until
`Rollback` gives it back.**
- Old: no token.
- Why: each live read transaction holds an `mmaplock.RLock` (`beginTx` to `removeTx`). Beyond
  `2^30` readers the `RWMutex` breaks mutual exclusion and a remap unmaps under readers. bbolt,
  the owner, bounds readers by the threads paying for them.
- Alternatives:
  - (a) receipts: count `Begin(false)` calls over the whole run with `ReceiptBoundLe GF (2^30)`.
    This weakens every closed result to runs of fewer than `2^30` receipts;
  - (b) a counted stock of slots from `Open`: forbidden by `bounds-plan`.
- Cost to etcd: `backend.New` takes and returns a token, and the backend's token flow is
  rearranged (above).
- **Recommend: the thread token.**

**D2: `DB.Stats` pays for `statlock`'s reader slot.**
- Old: `isDB db` only.
- New: `statSlot γ o`, either the caller's `threadTok` or the whole of a read transaction. The
  implementation's pool lends one slot per token, covering both `mmaplock` and `statlock`.
- Why the second form: in `newBackend` the creator's only token is in the first read
  transaction when `begin` calls `Stats`.
- Alternatives:
  - (a) `threadTok` only: `New` would need two tokens;
  - (b) receipts, as in D1.
- **Recommend: `statSlot`.** It is not a disjunction of specs: the client chooses, and the same
  resource comes back.

**D3 (changed in round 2): `Open` gains the instances `ThreadBoundLe GF (2^29)` and
`ReceiptBoundLe GF (2^62)`.**
- Old: none. Round 1 had `2^30`.
- Why:
  - The read transactions' slots plus one spare for the writer's `freepages` must fit
    `actualMaxReaders = 2^30 - 1`.
  - Txids must not wrap (the old proof's `flBelow`).
- Alternative to the spare slot: `Begin(true)` takes and holds a `threadTok` too, which costs
  every writer a token.
- Cost: none for etcd's closed results (`BuildServer` has `2^28` and `2^48`).
- **Recommend: accept.**

**D13 (new in round 2): `OptsM.ok` excludes `Mlock` and any `MmapFlags` other than `0` or
`MAP_POPULATE`.**
- Old: only `readOnly`, `pageSize` and `openFile` were constrained.
- These are scope restrictions of the model, to be filed in `notes/perennial-changes.md`: model
  `unix.Mlock`/`Munlock`, and more `mmap` flags in OsFs. Go has no such restriction.
- Cost: the backend's `newBackend` needs `Config.Mlock = false`, a configuration premise on the
  config's producer (etcd's default is false). The backend's `boltOpenOptionsOk` must also state
  `MmapFlags = MAP_POPULATE`, which `OptsM` tracks. It sets `NoFreelistSync`, which `OptsM` does
  not track (round 6 wording, consistent with the round-3 addendum); `BboltOptsDefs.lean`'s
  docstring should still mention it.
- Alternative: model `Mlock` (trivially, like minibolt's planned trivial models), which lifts the
  premise.
- **Recommend: accept now**, and propose `Mlock` models for OsFs as a separate Perennial-side
  change.

**D13, round 3 addendum (changed):** the option axioms are restated, not just moved:
- `optsAt_bool` loses `Mlock`, and `optsAt_int` loses `MmapFlags`;
- new `optsAt_mlock` and `optsAt_mmapFlags` set their fields;
- `optsZero` gains `mlock := false` and `mmapFlags := 0`.

The backend's `newBackend` proof then tracks `bopts.Mlock = bcfg.Mlock` through `optsAt_mlock`,
and needs `bcfg.Mlock = false`. `boltOpenOptionsOk` states `mmapFlags = MAP_POPULATE`; the
`NoFreelistSync: true` it also sets is untracked.

**D17 (new in round 3): the split threshold, through a trusted helper.**
- The problem: Perennial (pin and `origin/lean` `b3e996d84`) makes every float-to-int conversion
  an `ArbitraryInt`, and float `*`/`<` are uninterpreted. In the model, `splitTwo`'s threshold is
  then arbitrary, a node never splits by size, and `Commit` can panic (`inode overflow`, or a page
  past `MaxAllocSize`). So `Tx.Commit.spec` is unprovable for any transaction that makes a node
  split, which is etcd's normal case.
- Options:
  - **(a) Local workaround.**
    - A fork commit factors `node.go:237-243` into `func splitThreshold(pageSize uintptr,
      fillPercent float64) int`. This is a refactor that keeps behaviour.
    - The helper is listed `trusted` in `bbolt.toml`, with a `TrustedCode` model: an arbitrary
      int `t` with `splitThresholdOk` (NaN: any `t`; otherwise `0 ≤ t ≤ pageSize`).
    - Its docstring argues faithfulness: the clamp to `[0.1, 1.0]` and the truncation give
      `[⌊pageSize/10⌋ - 1, pageSize]`, inside the model's range.
    - It is a clearly marked trust boundary of this repository, per CLAUDE.md "Changes to
      Perennial".
  - **(b) General Perennial fix**, proposed separately and listed in
    `notes/perennial-changes.md`: interpret IEEE `float64` multiplication and comparison, and the
    in-range float-to-int conversion, or give the hypothesis class `notes/decisions.md` already
    sketches ("`int64(f)`: a hypothesis class"). Once it lands, the trusted helper can go.
  - **(c)** Make `splitTwo` itself trusted: too large a trust base.
- What then rests on (a): `bboltEntryMax`'s page bound, `boltTx_fill`'s non-NaN premise (the
  helper's NaN case), and `fileHolds`'s page-extent clause.
- **Recommend: (a) now, (b) proposed in parallel.** This is a change to the verified Go code (the
  fork) and to the trust base, so it is the user's decision.

**D18 (decided by the user, round 5): the fork change. `getPageSize` returns meta read errors,
and probes past page 1 only after successful reads with a bad checksum.**
- Before (round 2): `fileHolds` assumed "no user value holds a valid meta at an offset
  `getPageSize` probes". No `Commit` can keep that, because `Put` takes arbitrary bytes.
- Now:
  - `getPageSizeFromFirstMeta`, and each probe of `getPageSizeFromSecondMeta`, return a `ReadAt`
    error other than `io.EOF`. The short read at the end of the file stays as it was: an invalid
    meta.
  - `getPageSize` returns any error other than `ErrInvalid`, which includes the `Stat` error.
  - Probing past page 1 then needs both metas read and checksum-invalid. `fileHolds` requires one
    valid meta, so it assumes nothing of user values.
- Behaviour change: `Open` fails on a read error of a meta page, where it used to probe on.
- The no-fork alternative is dropped from the candidate.
- The finding is `nonissues/bbolt-getpagesize-probes-user-data.md`: a double-fault hardening
  that could be offered upstream.
- **The Go change**, as a diff of `db.go` against upstream v1.5.0. It is the same function text
  on `goose-lean` `3207bac`, so it applies there as a fork commit, and `etc/goose.py`'s pin is
  then bumped. The file is `d18/getpagesize.diff`. It builds, and v1.5.0's `TestOpen*` and
  `TestDB_Open*` tests pass with it (go1.27.3):

```diff
--- a/db.go
+++ b/db.go
@@ -335,19 +335,25 @@
 	)
 
 	// Read the first meta page to determine the page size.
-	if pgSize, canRead, err := db.getPageSizeFromFirstMeta(); err != nil {
+	// A read error is returned: probing further on a failed read could take
+	// the page size from user data that happens to hold a valid meta.
+	if pgSize, canRead, err := db.getPageSizeFromFirstMeta(); err == nil {
+		return pgSize, nil
+	} else if err != berrors.ErrInvalid {
+		return 0, err
+	} else {
 		// We cannot read the page size from page 0, but can read page 0.
 		meta0CanRead = canRead
-	} else {
-		return pgSize, nil
 	}
 
 	// Read the second meta page to determine the page size.
-	if pgSize, canRead, err := db.getPageSizeFromSecondMeta(); err != nil {
+	if pgSize, canRead, err := db.getPageSizeFromSecondMeta(); err == nil {
+		return pgSize, nil
+	} else if err != berrors.ErrInvalid {
+		return 0, err
+	} else {
 		// We cannot read the page size from page 1, but can read page 1.
 		meta1CanRead = canRead
-	} else {
-		return pgSize, nil
 	}
 
 	// If we can't read the page size from both pages, but can read
@@ -369,7 +375,12 @@
 func (db *DB) getPageSizeFromFirstMeta() (int, bool, error) {
 	var buf [0x1000]byte
 	var metaCanRead bool
-	if bw, err := db.file.ReadAt(buf[:], 0); err == nil && bw == len(buf) {
+	bw, err := db.file.ReadAt(buf[:], 0)
+	if err != nil && err != io.EOF {
+		// An I/O error, not a short file: report it.
+		return 0, metaCanRead, err
+	}
+	if err == nil && bw == len(buf) {
 		metaCanRead = true
 		if m := db.pageInBuffer(buf[:], 0).Meta(); m.Validate() == nil {
 			return int(m.PageSize()), metaCanRead, nil
@@ -405,6 +416,10 @@
 			break
 		}
 		bw, err := db.file.ReadAt(buf[:], pos)
+		if err != nil && err != io.EOF {
+			// An I/O error: report it rather than probe further.
+			return 0, metaCanRead, err
+		}
 		if (err == nil && bw == len(buf)) || (err == io.EOF && int64(bw) == (fileSize-pos)) {
 			metaCanRead = true
 			if m := db.pageInBuffer(buf[:], 0).Meta(); m.Validate() == nil {
```

**D20 (round 6; approved by the user in principle, superseded by D20' in round 7; kept for comparison): `boltLogger`, the contract of the logger bbolt calls, stated and exposed.**

It changes what the backend's trusted axiom `backend.newBoltLoggerZap.wp_proof` asserts.

- Old (rounds 1-5): `boltLogger l` was an opaque, sealed predicate whose only law was
  persistence: "a logger bbolt may call". The axiom's post `boltLogger l` asserted a meaning no
  one could see. `Open` could not be proved with a non-nil logger:
  - it logs `options` with `%s`, so `(*Options).String()` reads all 15 fields;
  - `Put`, `Delete`, `CreateBucket*` and `DeleteBucket` log the key with `%q`;
  - the repository's `fmt.argOk` needs a *persistent* method spec, which `*Options` has only
    over a discarded `optsAt`. The backend opens with `DFrac.own 1`.
- New (`candidate.lean`, "The logger contract"):

  ```lean
  def boltLogger (l : GoInterface) : IProp GF :=
    match l with
    | .nil => iprop(False)
    | .ok li => iprop(□ ∀ m fmtS args xs dq R, ⌜m ∈ boltLogMethods⌝ -∗
        {{ args ↦*{dq} xs ∗ ([∗ list] x ∈ xs, logArgOk R x) ∗ R }}
          (methods li.ty m li.v) #fmtS #args
        {{ RET #(); args ↦*{dq} xs ∗ R }})
  ```

  - `boltLogMethods` is `Debugf`, `Errorf`, `Infof` and `Warningf`, the only ones bbolt v1.5.0
    calls. It calls no `Fatal*`/`Panic*` and no non-`f` form.
  - `logArgOk R x` admits nil, a method-free value (`fmt.ArgWf`), a value whose
    `String()`/`Error()` returns given `R` and gives it back (`stringMethodWith`), or a `[]byte`
    whose bytes `R` lends.
- The backend's statement is unchanged in text: `newBoltLoggerZap.spec`'s post is still
  `boltLogger l`. What it asserts is now visible. The backend's zap logger (the axiom now; a proof
  later) must supply that `zapBoltLogger`'s `Debugf`/`Errorf`/`Infof`/`Warningf`:
  - format synchronously with `fmt.Sprintf` semantics, calling each argument's
    `String()`/`Error()` at most during the call and reading `[]byte` arguments only then;
  - keep no argument after returning;
  - never stop or panic. bbolt never calls zap's `Fatal`/`Panic` through these methods;
  - be callable concurrently: zap's core is thread-safe.

  A proof over zap would derive each from a `fmt.Sprintf` spec with lent-resource arguments. That
  is a generalization of `fmt.argOk` to a non-persistent `R`, and could go to Perennial's `fmt`
  as a separate change.
- Alternatives:
  - (a) keep `boltLogger` opaque, and assume in `Open`'s proof whatever reads the logger does:
    unprovable, as above;
  - (b) a persistent-arguments contract (`fmt.argOk`): `Open` would then need a discarded
    `optsAt`, which the backend does not have (`own 1`), and the `[]byte` keys would not be
    covered;
  - (c) require a nil logger: false for etcd, which always passes one.
- **Recommend: the new statement.** It is the user's decision, since it changes a trusted axiom's
  content.

**D22 (the user's decision, round 11): OsFs's in-process `pwrite` within one aligned OS page is
all-or-nothing. No P2.**

(History: round 9 chose a run restriction P2; round 10 showed P2 removes no Linux execution; the
user then chose this option, (b). P2, `osP2`, `osFsSemStepWith`, `fnv64a`, `boltMetaValid` and the
restricted-semantics binders are gone from `candidate.lean`. Rounds 9 and 10 are kept as
`candidate-r9.lean` and `candidate-r10.lean`.)

**The exact change to this repository's Linux file extension** (trusted model, reviewed as
such):

1. **`GooseLang/Ext/OsFs/Impl.lean`, the `PWriteFinish` rule.** Today it says
   `k ≤ data.length ∧ (k = data.length ∧ e = 0 ∨ e ≠ 0)`. It gains one conjunct:

   ```lean
   (off % osPageSize = 0 ∧ data.length ≤ osPageSize → k = 0 ∨ k = data.length)
   ```

   A write that starts on an OS page boundary and fits in one OS page writes all of its bytes or
   none, whatever the errno. The header's "a failed `pwrite` wrote a prefix" gets this
   exception.
2. **The crash relation `OsCrash` is unchanged.** A crash can still leave such a page torn in
   the durable image (sectors, write-back). That is P1's case (minibolt's `BootP1.lean`), and the
   crash results only.
3. **`GooseLang/Ext/OsFs/Write.lean`: `wp_osPWriteFinish`'s post gives the fact.** For a write
   with `off % osPageSize = 0 ∧ data.length ≤ osPageSize`, the written count is `0` or
   `data.length`.
4. **`Spec/os/File__WriteAt.lean`: `os.File.WriteAt`'s spec passes it on** (round 12, review 11
   M1). Its post gains a pure conjunct with no tie to `err`:
   `off.toNat % osPageSize = 0 ∧ data.length ≤ osPageSize → j = 0 ∨ j = data.length`. Here `j`
   is the written prefix the post already describes: a one-page aligned `WriteAt` leaves the
   range unchanged or wholly written, *whatever it returns*; `nil` means wholly written.
   - Why not tie it to `err`: the model admits a whole write with an errno
     (`k = data.length ∧ e ≠ 0`), and the `EINTR` retry loop (`TrustedCode/os.lean`) can follow
     a whole attempt with a failed one. Each attempt writes `0` or all of the same data at the
     same offset, so the composite prefix, a `max` over the attempts, is `0` or `data.length`.
   - One spec, with this conjunct added to its post. **`Tx.Commit`'s proof fires the commit
     update when `j = data.length`** (the whole new meta reached the page cache), not when
     `err = nil`. With an error and `j = data.length` the post is `Q` (the fork's `rollback`
     keeps the current new meta); with `j = 0` the update comes back.
5. **`GooseLang/Ext/OsFs/Tests.lean`: a test.** A torn one-page aligned write
   (`0 < k < data.length`) is not an `IsOsStep "PWriteFinish"`; a multi-page or unaligned one may
   still tear.

**Environment hypothesis** (round 12, review 11 M2; it goes into `Impl.lean`'s **Environment**
paragraph with the rule): **the process's `RLIMIT_FSIZE` is unlimited (etcd's default), or a
multiple of the OS page size.**
- Why: `generic_write_checks` → `generic_write_check_limits` shortens a write that crosses the
  limit to `limit - pos` bytes, overwrites included. So an aligned one-page `pwrite` with
  `pos < limit < pos + 4096` writes a prefix.
- Go ignores `SIGXFSZ` (`_SigNotify`, `runtime/sigtab_linux_generic.go`). Its `pwrite` loop
  retries and gets `EFBIG`, leaving the page torn.
- `s_maxbytes` is page-aligned, so it never splits a page.

**Why it is true of Linux** (OsFs's scope: buffered I/O on regular files of ext4/xfs, no
`O_DIRECT`; under the environment hypothesis above). `pwrite` goes through `generic_perform_write` (`mm/filemap.c`), which loops over the
page-cache pages (folios) the range covers. For each one it calls the filesystem's
`write_begin` (allocate or reserve the block, get the locked page), then
`copy_folio_from_iter_atomic` (a `memcpy` from the user buffer), then `write_end`. For a range
inside one aligned page:
- **`write_begin` failures** (`ENOSPC`, `EDQUOT`, `ENOMEM`) return before the page's copy, so
  `k = 0`. On a page already in the cache and dirty, as bbolt's meta page is (mapped and read),
  `write_begin` allocates nothing.
- **A short copy** (round 12, review 11 L1, corrected). `copy_folio_from_iter_atomic` copies short
  only when the user buffer faults.
  - For a folio that is **not uptodate**, `write_end` commits 0 bytes and the loop retries the
    page from the start.
  - For an **uptodate** folio, which bbolt's meta page is, `write_end` commits the copied prefix,
    and the loop continues *within the same page*. It runs `fault_in_iov_iter_readable` again
    and checks `fatal_signal_pending` again.
  - Either way the page ends torn only if the retry's fault-in fails, which needs an unmapped
    source (`EFAULT`). A live Go slice never is unmapped.
  - Or a fatal signal arrives between the parts. A fatal signal kills the process, and a process
    death is a crash in OsFs (the `Impl.lean` header), outside the in-process rule (P1's case).
  - From memory of `mm/filemap.c`, `fs/buffer.c` and iomap; marked uncertain where it matters,
    to be checked when the rule lands.
- **Device errors (`EIO`)** surface at write-back (`fsync`/`fdatasync`), not in `pwrite`. The
  page cache, which in-process readers and the mapping see, holds the whole new page.
- **Large folios** do not change this: a page-sized range is one copy into one folio.

So the rule removes only behaviours Linux does not have. The model stays "never more defined than
Linux". Unaligned and multi-page writes keep their prefixes; bbolt's data pages are such writes,
and may tear.

**Page size.** bbolt's page size is `boltPageSize = 4096`:
- `OptsM.ok` forces the default page size;
- `DefaultPageSize` is `os.Getpagesize()`, 4096 by the package fact;
- every valid meta records 4096 (`fileHolds`).

OsFs's OS page is `osPageSize = 4096` (`Impl.lean:154`), and `boltPageSize_eq_osPageSize` is
`rfl`. `writeMeta` writes one `pageSize` buffer at `p.Id() · pageSize` (`tx.go`), so a meta write
is exactly a write within one aligned OS page.

**What then holds in-process, with no premise:**
- **`Commit`'s error post ("took effect or not").** `writeMeta`'s write of page `txid % 2` either
  wrote the whole new meta or nothing.
  - If whole, the new meta is valid and current, the commit took effect, and the fork's
    `rollback` (`2d39641`) keeps it: `Q`.
  - If nothing, the page holds what it held. That is the older meta, not the current one, by
    the parity clause, so the current meta stays current: the update comes back.
  - No mixed slot exists, so no FNV-64a reasoning is needed. `Validate` of an untouched or
    complete meta follows from `Sum64`'s determinism, through any trusted or proved `hash/fnv`
    spec.
  - A failed `fdatasync` after a whole write changes nothing in the page cache: `Q`.
- **The parity clause.** A successful commit writes `txid + 1` at the page the current meta is
  not on, which becomes current at its parity. A failed one changes nothing (`k = 0`), or makes
  the whole new meta current at its parity. The next commit after a failure reuses the same
  txid, so it writes the same page. `WriteTo` images satisfy it with D21.
- **"At least one valid meta", and so no `meta()` panic in `Begin` or `rollback`.** The current
  page is never written. The written page is wholly new (valid) or unchanged.
- **The `fileHolds` meta clauses**, which every in-process step keeps.

The crash case, a crash leaving a torn page in the durable image, is out of scope here (no crash
spec). There P1, minibolt's premise, is the precedent.

**What it needs:** six items, all in this repository:
1. `Impl.lean`'s conjunct;
2. its header text;
3. the environment hypothesis;
4. `Write.lean`'s post;
5. `File__WriteAt.lean`'s post (`j = 0 ∨ j = data.length`, whatever `err`);
6. a test.

No second semantics and no transfer lemma.

**The `hash/fnv` trust boundary** (round 12, review 11 M3). `Meta.Sum64` calls `hash/fnv`'s
`New64a` and then `hash.Hash64`'s `Write`/`Sum64`. These are names-only today
(`Code/hash/fnv.toml`, `translate = ["!*"]`, owned by this repository's etcd project), with no
spec. The only fact any clause needs is **determinism**: `Sum64` returns `H bs` for one fixed
function `H` of the bytes written. That is the same `H` `fileHolds`' sealed "valid meta" uses. A
zero or non-meta slot fails at the magic, before any hash, so there is no collision assumption.

**Chosen route: translate with bodies.** Translate `New64a` and the type `sum64a` with its
methods `Write`, `Sum64` (plus the method-set facts `hash.Hash64` conversion needs). Do not
translate `sum128`, which pulls in `math/bits`. Then prove:
- `Spec/hash/fnv/New64a.lean`;
- `Spec/hash/fnv/sum64a__Write.lean`;
- `Spec/hash/fnv/sum64a__Sum64.lean`.

They are proved against a Lean FNV-64a: Perennial's `unsafememory` example has `fnv64`
(`…/unsafememory/Meta.lean:41`), which also shows the `*[56]byte` view of a `Meta`. Nothing is then
trusted. It is a small, plain-`uint64` package.

**Fallback,** only if that view over *mapped* cells proves impractical: a trust-boundary spec
of the three functions over an opaque `H`. It would be listed under "Also trusted".

**D21 (new in round 7; decided by me, by the precedent of D18 and of raft's fork fixes for
real Go bugs): `Tx.WriteTo` writes the current meta at page `txid % 2`.**

In plain terms:
- bbolt keeps two copies of its "table of contents" (the meta page). Each commit overwrites the
  *older* copy, so if the write is cut off half-way (a crash, or a disk error), the newer copy
  survives and the database still opens at the last good commit.
- `Tx.WriteTo` (how etcd saves and sends snapshots) always puts the newest copy in slot 0. Half
  the time that is the slot the next commit will overwrite.
- So on a database restored from such a snapshot, two failed commits in a row (each torn while
  writing its meta, before the first successful one) can damage both copies. bbolt then panics,
  or after a crash the file no longer opens.
- A database bbolt wrote itself does not have this window. It takes a double fault, and it is
  present upstream (v1.5.0 and `main`).
- Reproduced by a Go test with fault injection, `issues/bbolt-writeto-meta-parity.md`: it fails
  at upstream `main` and passes on the fork with the fix.
- **The fix** (`d21/writeto.diff`, against `goose-lean-v2` `b30879b2`) writes the newest copy at
  slot `txid % 2` and the older one at the other slot, as a commit would have left them. It
  builds, and with it the issue's test and bbolt's test suite pass.
- **Why it matters to the proof:** `fileHolds` keeps its parity clause, which the next commit's
  safety needs. Without the fix, etcd's snapshot path (`SaveDBFrom`, `DBFilePath`) would assert
  `fileHolds` of files that violate it.

**D20' (new in round 7; replaces D20; decided by me under the principles, as the user asked):
the logger contract, restated for Go's `fmt`.**

In plain terms:
- bbolt logs through a logger the client supplies, and passes it values to print: paths,
  numbers, keys, errors, the open options. The spec has to say what the logger may do with them,
  because printing an error or the options runs code that reads memory.
- Round 6's contract said "the logger calls each argument's `String()` or `Error()` while we lend
  it what that method needs". That is not what Go's `fmt` does in every case:
  - it calls `Format` first if a type has one, and `Error` before `String`;
  - under `%w` outside `fmt.Errorf` (ten of bbolt's log calls), it calls no method at all and
    prints the pointed-to struct field by field;
  - under `%d` and similar verbs, it prints a pointer's target the same way.
- The new contract allows only the format strings bbolt really uses: bare `%s %v %q %d %t %x`, no
  flags (`fmtVerbs`). It pairs each argument with its verb, and accepts four kinds of argument:
  - plain values;
  - errors (type has `Error`, no `Format`, under `s v q x`), whose `Error()` runs with the lent
    resources;
  - Stringers (type has `String`, but neither `Error` nor `Format`, under `s v q x`);
  - byte slices whose bytes are lent.

  Under these restrictions `fmt` calls exactly the method the contract names.
- The fork takes upstream `main`'s change of its ten logger `%w` to `%v` (`d21/logverb.diff`),
  which also fixes garbled log lines (`%!w(...)`).
- It makes bbolt's default (nil-option) logger a real no-op (`d21/discardlogger.diff`). The old
  default formatted every message and threw it away. With the change, the nil-logger branch
  needs no `fmt` or `log` model at all.
- zap's standard cores meet the contract: they format synchronously with `fmt.Sprintf`, keep no
  argument, and never stop at these levels. A user-supplied `zapcore.Core` that panics is out of
  scope.

**Old (D20, round 6) vs new (D20'):**

| | D20 (round 6) | D20' (round 7) |
|---|---|---|
| format strings | any `fmtS` | `fmtVerbs fmtS = some vs`: bare `%s %v %q %d %t %x`, `%%` |
| an argument | `logArgOk R x`: basic, or `Error`/`String` given `R`, or lent `[]byte` | `logArgOk R v x` under its verb `v`: basic; or an error (`Error`, no `Format`, `v ∈ s v q x`); or a Stringer (`String`, no `Error`/`Format`, `v ∈ s v q x`); or lent `[]byte` |
| `%w` sites | admitted, though `fmt` prints them by reflection | excluded; the fork logs with `%v` (upstream `main`'s change) |
| nil logger | `discardLogger` formats, then discards: needed `Sprintf` and `log.Logger.Output` | `discardLogger` is a no-op (a fork commit) |
| backend's axiom | `newBoltLoggerZap`'s post `boltLogger l`, unscoped | the same post; its docstring scopes it to zap's standard cores |

**What it needs** (all local to this repository; no Perennial change is required):
1. Fork commits: `%w` → `%v` in the ten logger calls, and the no-op `discardLogger` (`d21/`).
2. `wp_Options_String` (trusted, D13's family): `(*Options).String()` reads `optsAt` and returns.
   It is in the candidate.
3. Error values with an `Error()` spec, so that bbolt's proofs can show `logArgOk` of the errors
   they log:
   - translate `io/fs`'s `(*PathError).Error` and `syscall`'s `Errno.Error` with bodies (this
     repository's `io/fs` and `syscall` projects, `Code/io/fs.toml`, `Code/syscall.toml`);
   - make the OsFs-backed `os`/`syscall`/`unix` specs return `fmt.stringMethodSpec err "Error"`;
   - keep the `PathError`'s points-to as `↦□` in `wp_wrapErrno` (`Proof/os/Base.lean`).

   bbolt's own errors (`errors.New`, `fmt.Errorf`) already have it in Perennial.
4. `io/fs`'s `FileMode.String` translated with a body (`Open` logs `mode` with `%s`), with a spec
   needing nothing.

Optional, a separate Perennial proposal: a `fmt.Sprintf` spec over arguments with lent
resources, which would let `wp_Options_String` become a proof once `Options` is translated.

**D19 (new in round 3): no `γ`-agreement laws; the clients carry `γ`.**
- Round 2's `isBolt_agree`/`boltTx_isBolt` need a registry `db ↦ γ`: ghost state allocated in
  bbolt's package initialization, as a package fact through `etc/gen-init.py`'s `SPECIAL`.
- The backend already carries `γ.db` everywhere it has `isDB`, so its layer becomes `isDB db :=
  isBolt db γ.db`.
- Alternative: the registry. It is provable (the package fact holds an authoritative `ghost_map`,
  and `Open` inserts `db ↦ γ`) but adds a package-initialization fact.
- *(Corrected after the invariant design, D-E: the registry is **not** provable this way. A package
  fact is a fixed proposition, so an existential ghost name inside it does not agree between two
  copies; see "Corrections after the invariant design" at the end.)*
- **Recommend: drop the laws.**

**D14 (new in round 2): `Cursor.Prev` is specified for read transactions only.**
- Old: there was no `Prev` spec. Round 1's was false in writers.
- Alternatives:
  - drop `Prev`;
  - a weaker post for writers (a key or nil), which is near-vacuous.
- **Recommend: the scope restriction.** It is exact where Go is correct, and the bug is drafted
  for `issues/`.

**D15 (new in round 2): `Open` takes the namespace `N`.**
- Old: a fixed `boltN`, round 1 only; the backend had no namespace.
- Every update's mask is `⊤ \ ↑γ.ns`.
- Cost: the backend's `newBackend` picks one, for example `bN .@ "bolt"`, provided none of the
  backend's own invariants is at `bN` itself.
- Round 3 (changed): `Open` also takes `⌜↑N ## ↑osN⌝`, because the commit update fires inside the
  meta's `pwrite`, an OsFs step. It is cheap for both callers.
- **Recommend: accept**, per the caller-chosen-namespace preference.

**D16 (new in round 2): `fileHolds`'s content, and `fileHolds_new`.**
- `fileHolds` is trusted vocabulary: its definition decides what `Open` assumes.
  - Round 2 added no empty non-root page and sorted keys across pages, dropped "every byte
    synced", and added the fresh-file law.
  - Round 3 (changed) adds exact branch keys, branches of at least two elements, pages below
    `MaxAllocSize` with under `0xFFFF` elements, and page types. It drops the forged-meta clause
    (under D18), and states the txid invariant as `< 2^63`.
  - Maintenance: the section above.
- Open question: etcd's received snapshot file (`.snap.db`, then `os.Rename`, then `Open`) must
  supply this well-formedness. Today it comes from `fileHolds`'s axiomatized producers in the
  snapshot path (`Snapshotter.DBFilePath`, `rafthttp`). Those producers assert it of
  `Tx.WriteTo`'s images, which satisfy it only with D21's fork commit (round 8): the producers rest
  on that commit, and on the peer running the same bbolt.
- **Recommend: accept.**

**D4: `Put` premises `kb.length + vb.length ≤ bboltEntryMax` (`2^28`), replacing the arm "value
above `MaxValueSize`: an error".**
- The old arm is refuted (`notes/axiom-review/bbolt.md` §2).
- Alternatives:
  - (a) `2^28` (old proof, power of two, ample slack);
  - (b) the tightest neighbour-independent bound, about `2^29 - 2^10`, which needs the page-size
    rounding argument;
  - (c) keep the error arm and add the premise only below it. This is no stronger, since the
    arm is unreachable under any premise that makes `Put` sound.
- Cost to etcd: `unsafePut` (and `UnsafeSeqPut`) need the bound from mvcc, ultimately etcd's
  request size limit (`MaxRequestBytes`, 1.5 MiB by default). No spec carries it to the backend
  today.
- **Recommend: (a)**, carried as a workload premise on the backend's producer (PRINCIPLES' "a
  workload premise ... goes on the resource's only producer").

**D5: `FillPercent` is taken back only as a non-NaN value.**
- Old: `∀ f'`, which is refuted.
- **Recommend: accept.** It is the axiom review's proposed restatement.

**D6: one transaction predicate `boltTx tx γ q T` for both kinds.**
- It replaces `txLive`, `rtxSnap`, `rtxStats`, `rBkt` and `ownWTxG`, about 10 backend files
  restated mechanically.
- Alternative: keep two families (`_kvr`/`_kvw` specs), which goes against the hard rule "one
  spec per function".
- **Recommend: new.**

**D8: bbolt's proof is over the OsFs Linux-file extension.**
- `[HasExt osFsExt]` becomes a section variable of every spec over bbolt, not only `Open`'s
  (`isBolt`'s definition reaches OsFs ghost state), and so of every backend and etcdserver spec
  over them and of `os.Rename`'s spec (round 2). `osInv` is folded into `fileHolds` (round 9).
- etcd's closed results then run under OsFs's adequacy.
- `os.Rename` (etcd's snapshot install) stays a trust-boundary axiom: OsFs has no rename.
- Alternative: a bbolt-specific file axiom model, like the old branch's `FileModel.lean`, which
  is weaker and untested.
- **Recommend: OsFs**, with `osInv` folded into `fileHolds` if the user prefers fewer
  conjuncts.

**D9: `Close`'s post is `True`, and it does not give `fileHolds` back.**
- Alternative: give `fileHolds path D` back to a closer that brings all of `boltState`. This
  needs the path in `isBolt` and the file parked in the invariant after a non-owning `Close`.
- No client needs it now: etcd renames a new file in and opens it.
- **Recommend: defer**, as a stated margin.

**D10: `View` and `Update` are not specified now.**
- `View` fits the vocabulary: its callback gets half of a read transaction, so it cannot call
  `Rollback`, which panics as managed.
- `Update` needs a `managed` field in `TxView`. `Commit` and `Rollback` would require it to be
  `false`. That is why the literals use named fields: a field with a default can be added later
  without changing a statement.
- **Recommend: defer**, unless the concurrent test uses them.

**D11: the specs are of the fork `goose-lean-v2` (`b3e06648`, round 7's three commits included), not upstream v1.5.0.**
- `Commit` is false of upstream after a failed `fdatasync` once the meta was written, with
  readers open.
- The fork also carries D17's `splitThreshold` refactor and D18's `getPageSize` change: both are
  committed on `goose-lean-v2` (now `b3e06648`), with `etc/goose.py`'s pin bumped on
  `worktree-bbolt-v2`, and D17's `TrustedCode` model is committed (`d7ac2c2ea2`).
- etcd's own results are unaffected, since it exits on a commit error.
- **Recommend: accept**, as raft's fork is.

**D12: `CreateBucket(IfNotExists)` keeps `n.length ≤ maxKeySize`.**
- This premise exists today. Go checks no length (finding 1), so it is stricter than the code
  but within the documented API.
- Alternative: drop it and bound the name by `bboltEntryMax`.
- **Recommend: keep**, documented as a scope restriction.

## Not covered, and margins

**Not covered:** `View`, `Update`, `Batch`, `ForEach`, `Tx.Cursor`, `Cursor.Delete`, `WriteTo`
and `Copy` (the backend's snapshot), nested buckets, `Sequence`, `Check`, `Compact`, crash
durability.

**Margins:**
- options passed as nil;
- `Get` of a nil value;
- re-`Seek`ing a cursor after a change, which Go allows and the spec does not;
- mutations on read transactions (`ErrTxNotWritable`);
- `Close` returning the file;
- the error identities of `Put`, `Commit` and `Begin` (only `≠ nil`; `ErrBucketNotFound` and
  `ErrBucketExists` are exact).

## Findings in the Go code

The first two were found by specifying and confirmed with Go tests. Their drafts are in
`nonissues/` beside this file, and the tests are in `gotest/main_test.go`. The third's draft and
test are in `issues/`.

1. **`nonissues/bbolt-bucket-name-length-unchecked.md`**: `CreateBucket` and
   `CreateBucketIfNotExists` are documented to refuse names that are too long, but they accept
   names of `MaxKeySize + 1` bytes and of 1 MiB. Documentation only; not etcd.
2. **`nonissues/bbolt-cursor-prev-after-next-end.md`**: `Prev` after reaching the end returns
   the last key if the end was reached by `Seek`, but the key before it if reached by `Next`.
   Documentation and API behavior only; etcd never calls `Prev`.

3. **`issues/bbolt-cursor-prev-empty-leaf.md`** (round 2; found by the reviewer, test
   `issues/bbolt-cursor-prev-empty-leaf/prev_empty_leaf_test.go`). In a write transaction,
   `Prev` returns nil in the middle of the bucket once deletes have emptied a leaf. It fails at
   upstream `main` `a4ef197` (go1.27.3: `Prev returned "", want "k00499"`; a backward walk sees
   500 of 1000 keys). It is a public-API bug with a failing upstream test, so it goes in
   `issues/`. `blocks-proof: no` (scope restriction D14; etcd never calls `Prev`).

4. **`issues/bbolt-cursor-last-empty-leaves-hang.md`** (round 3; found by the reviewer, test
   `issues/bbolt-cursor-last-empty-leaves-hang/last_all_deleted_test.go`). In a write
   transaction, `Last` never returns once deletes have emptied every leaf of a multi-leaf bucket.
   It hangs at upstream `main` `a4ef197` (go1.27.3). `blocks-proof: no` (a WP is partial; etcd
   never calls `Last`).
5. **`nonissues/bbolt-getpagesize-probes-user-data.md`** (round 3; code reading). After a read
   error on the meta pages, `getPageSize` probes user pages and takes the page size from a forged
   meta. Excluded by D18's fork change.

None of these blocks the proof. The `splitThreshold` dependency is not a Go bug, but a limit of
Perennial's float model (D17).

## Not done

- The `spec-reviewer` read rounds 1 to 9 (`review-9.md`). Rounds 10 and 11 have not been
  reviewed. The candidate elaborates (`lake env lean` on a temporary copy in the
  `worktree-bbolt-v2` worktree: 0 errors; `sorry` and unused-section-variable warnings); the
  restricted instance was checked in the elaborated statements; the copy was deleted.
- The `issues/` and `nonissues/` drafts beside this file are not yet filed in the repository.
- The `axiom` skill was not rerun on the restated trust-boundary layer.

## Frozen candidate: summary (round 10; superseded by "Frozen spec" at the end)

The statements are in `candidate.lean`. This section only lists them.

### Pure vocabulary (`Spec/go_etcd_io/bbolt/Api.lean`)

- **Data:** `BktData`, `Data` (top-level buckets only), `BoltEnt`, `bktEnts`, `seekIdx`.
- **Named bounds:** `maxKeySize` (`32768`), `maxValueSize` (reference only), `bboltEntryMax`
  (`2^28`, key plus value), `mapPopulate`.
- `float64IsNaN`.
- **`TxView`**, with fields `rw`, `base`, `cur` and `gen`, and the helpers `TxView.ro`,
  `TxView.wr`, `TxView.setBkt` and `TxView.dropBkt`.
- **`BoltName`**, a structure `{ gs, ns }`: `Inhabited`, `DecidableEq`, and `Pos.Countable`
  (`boltName_countable`, by `countableOfLeftInverse`).
- `curAt`, persistent; `statSlot`.
- **Options:** `OptsM` (`readOnly`, `pageSize`, `openFile`, `logger`, `mlock`, `mmapFlags`),
  `optsZero`, `OptsM.ok` and `optsZero_ok`.
- `dbCloseOk`, an opaque environment premise used only by the backend's `DB.Close_kv` layer.

### Predicates (sealed)

| predicate | kind |
|---|---|
| `isBolt db γ` | persistent |
| `boltState γ q D` | fractional, timeless |
| `boltTx tx γ q T` | fractional for a fixed `T`, timeless |
| `txDB tx db`, `txDone tx` | persistent |
| `boltBkt tx b n g` | persistent |
| `boltCur tx c T es pos` | exclusive, timeless |
| `txBytes tx s b` | persistent |
| `fileHolds path D` | exclusive, timeless; over OsFs |
| `boltLogger l` | persistent; an **exposed** definition (D20') |
| `fmtErrorOk err` | persistent; the shared `fmt`-level error predicate (round 8; `Spec/fmt/`) |
| `optsAt l dq o` | discarded fraction persistent |

### Laws

- `isBolt_persistent`.
- `boltState`: `_timeless`, `_fractional`, `_agree`, `_valid`.
- `boltTx`: `_timeless`, `_fractional`, `_agree`, `_valid`, `_nonnull`.
- `boltTx_base` (a live writer's base is the committed data). `boltTx_agree` is over one name
  (round 6). `txSnap`, `boltTx_snap` and `txSnap_agree` are dropped.
- The persistence and timelessness instances of `txDB`, `txDone`, `boltBkt`,
  `txBytes`, `boltCur`, `fileHolds` and `boltLogger`.
- `txBytes_acc`.
- `boltTx_fill` (`FillPercent`, written back only as a non-NaN value).
- `fileHolds_new` (a fresh or empty file holds `∅`).
- `boltState_read_au` and `boltState_commit_au` (the layer lemmas for a client owning all of
  the state).

### Trust-boundary axioms

The options, all trusted under D13:
- **moved unchanged:** `optsVal`, `wp_optsLit` (to `optsZero`), `wp_optsAlloc`, `wp_optsLoad`,
  `wp_optsStore`, `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger`,
  `optsAt_discard_persistent`;
- **restated:** `optsAt_bool`, `optsAt_int`;
- **new:** `optsAt_mlock`, `optsAt_mmapFlags`, `optsAt_nonnull`, the `optsAt_*_rd` read axioms
  for `ReadOnly`, `Mlock`, `PageSize`, `MmapFlags`, `OpenFile` and `Logger`, and
  `optsAt_bool_rd`, `optsAt_int_rd`, `optsAt_freelist_rd`, `optsAt_timeout_rd` (round 5, in
  place of round 4's type-generic `optsAt_other_rd`), and `wp_Options_String` (round 7, D20').

D22 (round 11): no premise. OsFs's in-process `pwrite` within one aligned OS page is all-or-nothing, a rule of this repository's Linux file extension (`Impl.lean`'s `PWriteFinish`), justified by `generic_perform_write`.

The logger contract `boltLogger` (D20'): exposed, with `fmtVerbs`, `methodVerbs` and `logArgOk`.

The model of the trusted fork helper `splitThreshold` (D17, `TrustedCode/go_etcd_io/bbolt.lean`):
`splitThresholdOk`, with the NaN, `pageSize ≥ 2^53` and `[0, pageSize]` disjuncts.

### Triples (`Spec/go_etcd_io/bbolt/<T>__<M>.lean`)

| function | pre, in short | post, in short |
|---|---|---|
| `Open` | the restricted semantics (D22); `ThreadBoundLe GF (2^29)`, `ReceiptBoundLe GF (2^62)`; `isPkgInit`, `↑N ## ↑osN`, `fileHolds path D`, `optsAt opts dq o` with `o.ok`, the logger | options back; ok: `γ.ns = N`, `isBolt db γ ∗ boltState γ 1 D`; or an error |
| `DB.Close` | `isBolt` | `True` |
| `DB.Begin(w)` | `isBolt`; read: `threadTok` and a read update | ok: `txDB`, writer `boltTx tx γ 1 (wr D)`; reader `boltTx tx γ 1 (ro D) ∗ Q D`. Error: the token and the update back |
| `Tx.Commit` | `boltTx tx γ 1 T`, `T.rw`, a commit update `D' = T.base` to `T.cur` | `txDone`; ok: `Q`; error: `Q ∨` the update |
| `Tx.Rollback` | `boltTx tx γ 1 T` | `txDone`; a reader's `threadTok` back |
| `Tx.Bucket` | `boltTx tx γ q T` (`q = 1` if `T.rw`) | nil if absent, else `boltBkt tx b n (T.gen n)` |
| `Tx.CreateBucket`, `Tx.CreateBucketIfNotExists` | a writer, a name `≤ maxKeySize` | empty name: an error; exists: `ErrBucketExists` (or the handle, for `IfNotExists`); else `setBkt n ∅` and the handle |
| `Tx.DeleteBucket` | a writer | absent: `ErrBucketNotFound`; else `dropBkt n` |
| `Bucket.Get` | any fraction, a current handle | nil if absent, else `txBytes` of the value |
| `Bucket.Put` | a writer, a current handle, `key + value ≤ bboltEntryMax`, the value read-only for good | a bad key: an error, unchanged; else `setBkt n (m.insert k v)` |
| `Bucket.Delete` | a writer, a current handle, the key owned or `txBytes` | `setBkt n (m.delete k)` |
| `Bucket.Cursor` | any fraction, a current handle | `boltCur tx c T (bktEnts m) none` |
| `Cursor.Seek`, `First`, `Last`, `Next` | `boltTx` at the cursor's `T` | the position and `curAt`, as stated. `Last` hangs in a writer whose leaves are all empty (a Go bug, noted) |
| `Cursor.Prev` | as above, and `T.rw = false` | as stated |
| `Tx.Size`, `Tx.DB` | `boltTx` | some size; the database |
| `Tx.Stats` | `txDone` | some statistics |
| `DB.Info` | `isBolt db γ`, `txDB`, `boltTx tx γ q T` | a fresh `Info` (`↦`) |
| `DB.Stats` | `isBolt db γ`, `statSlot γ o` | `statSlot γ o` back |

### Backend impact (summary)

| `_kv` axiom | status |
|---|---|
| `Open_kv` | corollary under added premises: the D3 instances, the restricted semantics (D22), a namespace, and `Config.Mlock = false` |
| `DB.Begin_kv` (write), `Tx.Commit_kv`, `Tx.Stats_kv`, `Tx.Bucket_kvw`, `Tx.CreateBucketIfNotExists_kv`, `Tx.DeleteBucket_kv`, `Bucket.Delete_kv`, `Bucket.Cursor_kvw` | corollaries with the same text, plus `[HasExt osFsExt]` |
| `DB.Begin_kv` (read) | not a corollary: a `threadTok` (D1) |
| `DB.Stats_kv` | not a corollary: `statSlot` (D2) |
| `Bucket.Put_kv` | not a corollary: `bboltEntryMax` (D4) |
| `DB.Close_kv` | stays a trust-boundary layer (`dbCloseOk`) |
| `Tx.Rollback_kv`, `DB.Info_kv`, `Tx.Size_kv`, `Tx.DB_kv`, `Tx.Bucket_kvr`, `Bucket.Cursor_kvr`, `Cursor.Seek_kv`, `Cursor.Next_kv` | restated: `boltTx` (with `ro D` where `rtxSnap` was); `isDB db` becomes `isBolt db γ.db`; `rtxStats` dropped |
| `ownWTxG_fill` | restated, non-NaN (D5) |
| `ownWTxG_live`, `ownWTx_live`, `rtxStats_excl` | gone |

**Backend proof changes:**
- about 10 files restated;
- `rtxStats` machinery deleted;
- `New` takes and returns a `threadTok`, with the token flow above;
- `unsafePut` and `UnsafeSeqPut` need the entry bound from mvcc;
- `BNames.db : BoltName`;
- `newBackend` chooses `N`, with `N ## osN`.

### Open items

- (D18: decided in round 5, the fork change.)
- (D20 approved in principle by the user; restated as D20' in round 7, decided by me.)
- The infrastructure items under D20' (error `Error()` specs, `FileMode.String`), and P2's
  step-restricted semantics.
- (Resolved, round 6: `internal/common`'s `DefaultPageSize` fact exists,
  `Proof/go_etcd_io/bbolt/PkgInit.lean:108-112`, through the `os.Getpagesize` axiom.)
- The OsFs change of D22 (the five items under D22), to be made in the repository.
- Filing the drafts in `issues/` and `nonissues/`.

## Frozen spec (round 12)

The statements are `candidate.lean`. It elaborates against `worktree-bbolt-v2` (`44ed0aad76`;
fork `goose-lean-v2` `b3e06648`, Perennial `b3e996d84`). Every predicate and triple carries
`[HasExt osFsExt]`, which is `osFs_semantics`; this was checked with `#check`/`#print`.

### Target and fork

bbolt v1.5.0 as translated from `upamanyus/bbolt` `goose-lean-v2` `b3e06648`. Relative to
upstream, the fork carries:
- `2d39641`: a failed commit whose meta reached the file keeps its pages pending
  (etcd-io/bbolt#1311);
- the crash-safe `init`;
- D17's `splitThreshold` helper (trusted model `splitThresholdOk`);
- D18's `getPageSize` that returns meta read errors;
- D21's `WriteTo` meta parity;
- the logger calls' `%w` → `%v`;
- the no-op `discardLogger`.

### Pure vocabulary

- **Data:** `BktData`, `Data` (top-level buckets only), `BoltEnt`, `bktEnts`, `seekIdx`.
- **Bounds:** `maxKeySize`, `maxValueSize` (reference), `bboltEntryMax = 2^28`, `boltPageSize = 4096`
  (`= osPageSize`), `mapPopulate`.
- **Transactions:** `TxView` (`rw`, `base`, `cur`, `gen`), with `ro`, `wr`, `setBkt`, `dropBkt`.
- **Names:** `BoltName` (`gs`, `ns`; `Inhabited`, `DecidableEq`, `boltName_countable`).
- **Floats:** `float64IsNaN`.
- **Cursor results:** `curAt`.
- **Stats:** `statSlot`.
- **Options:** `OptsM` (`readOnly`, `pageSize`, `openFile`, `logger`, `mlock`, `mmapFlags`),
  `optsZero`, `OptsM.ok`, `loggerPtrOk`.
- **The logger contract** (D20′): `boltLogMethods`, `logVerbs`, `fmtVerbs`, `methodVerbs`,
  `noArgStringSig`, `stringMethodWith`, `fmtErrorOk`, `logArgOk`, `boltLogger` (exposed).
- **Close:** `dbCloseOk`, an environment premise used only by the backend's `DB.Close_kv` layer.

### Predicates (sealed, each over `[HasExt osFsExt]`)

| predicate | kind |
|---|---|
| `isBolt db γ` | persistent |
| `boltState γ q D` | fractional (for a fixed `D`), timeless, agreeing |
| `boltTx tx γ q T` | fractional (for a fixed `T`), timeless, agreeing over one `γ` |
| `txDB tx db`, `txDone tx` | persistent |
| `boltBkt tx b n g` | persistent |
| `boltCur tx c T es pos` | exclusive, timeless |
| `txBytes tx s b` | persistent |
| `fileHolds path D` | exclusive, timeless; holds `osInv`; the well-formedness of D16 (rounds 2–8) |
| `optsAt l dq o` | the options (trusted, D13) |

### Laws

- **Persistence and timelessness:** `isBolt_persistent`, `txDB_persistent`, `txDone_persistent`,
  `boltBkt_persistent`, `txBytes_persistent`, `boltCur_timeless`, `fileHolds_timeless`,
  `boltLogger_persistent`, `curAt_persistent`.
- **`boltState`:** `_timeless`, `_fractional`, `_agree`, `_valid`.
- **`boltTx`:** `_timeless`, `_fractional`, `_agree`, `_valid`, `_nonnull`, `_base`.
- **Others:** `txBytes_acc`, `boltTx_fill` (non-NaN), `fileHolds_new`, `boltState_read_au`,
  `boltState_commit_au`, `boltPageSize_eq_osPageSize`, `optsZero_ok`.

### Trust-boundary axioms (all D13's family: `Options` is axiomatized)

- **Moved unchanged:** `optsVal`, `wp_optsLit`, `wp_optsAlloc`, `wp_optsLoad`, `wp_optsStore`,
  `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger`, `optsAt_discard_persistent`.
- **Restated:** `optsAt_bool`, `optsAt_int`.
- **New:**
  - `optsAt_mlock`, `optsAt_mmapFlags`, `optsAt_nonnull`;
  - the read axioms `optsAt_readOnly_rd`, `_mlock_rd`, `_pageSize_rd`, `_mmapFlags_rd`,
    `_openFile_rd`, `_logger_rd`, `_bool_rd`, `_int_rd`, `_freelist_rd`, `_timeout_rd`;
  - `wp_Options_String`.

Also trusted:
- the `TrustedCode` model `splitThresholdOk` (D17);
- D22's OsFs rule: one aligned OS page written all-or-nothing in-process, under the environment
  hypothesis "`RLIMIT_FSIZE` unlimited or a multiple of the OS page size";
- `hash/fnv`: nothing, if translated with bodies (the chosen route). Otherwise a determinism-only
  spec of `New64a`/`Write`/`Sum64`.

### Triples (`Spec/go_etcd_io/bbolt/<T>__<M>.lean`; each `∀ [HasExt osFsExt] …`)

| function | pre, in short | post, in short |
|---|---|---|
| `Open` | `ThreadBoundLe GF (2^29)`, `ReceiptBoundLe GF (2^62)`; `isPkgInit`, `↑N ## ↑osN`, `fileHolds path D` (holds `osInv`), `optsAt opts dq o` with `o.ok`, the logger nil or `boltLogger` | options back; ok: `γ.ns = N`, `isBolt db γ ∗ boltState γ 1 D`; or an error |
| `DB.Close` | `isBolt` | `True` |
| `DB.Begin(w)` | `isBolt`; read: `threadTok` and a read update | ok: `txDB`; a writer gets `boltTx tx γ 1 (wr D)`, a reader `boltTx tx γ 1 (ro D) ∗ Q D`. Error: the token and the update back |
| `Tx.Commit` | `boltTx tx γ 1 T`, `T.rw`, a commit update `D' = T.base` to `T.cur` | `txDone`; ok: `Q`; error: `Q ∨` the update (D22) |
| `Tx.Rollback` | `boltTx tx γ 1 T` | `txDone`; a reader's `threadTok` back |
| `Tx.Bucket` | `boltTx tx γ q T` (`q = 1` if `T.rw`) | nil, or `boltBkt tx b n (T.gen n)` |
| `Tx.CreateBucket`, `Tx.CreateBucketIfNotExists` | a writer; a name `≤ maxKeySize` | empty name: an error; exists: `ErrBucketExists` (or the handle, for `IfNotExists`); else `setBkt n ∅` and the handle |
| `Tx.DeleteBucket` | a writer | absent: `ErrBucketNotFound`; else `dropBkt n` |
| `Bucket.Get` | any fraction, a current handle | nil, or `txBytes` of the value |
| `Bucket.Put` | a writer, a current handle, `key + value ≤ bboltEntryMax`, the value `↦*□` | a bad key: an error, unchanged; else `setBkt n (m.insert k v)` |
| `Bucket.Delete` | a writer, a current handle, the key owned or `txBytes` | `setBkt n (m.delete k)` |
| `Bucket.Cursor` | any fraction, a current handle | `boltCur … none` |
| `Cursor.Seek`, `First`, `Last`, `Next` | `boltTx` at the cursor's `T` | position and `curAt`. `Last` may hang in a writer whose leaves are all empty (Go bug, noted) |
| `Cursor.Prev` | the same, and `T.rw = false` | as stated |
| `Tx.Size`, `Tx.DB` | `boltTx` | a size; the database |
| `Tx.Stats` | `txDone` | some statistics |
| `DB.Info` | `isBolt`, `txDB`, `boltTx` | a fresh `Info` |
| `DB.Stats` | `isBolt`, `statSlot γ o` | `statSlot γ o` back |

### Backend impact

| `_kv` axiom | status |
|---|---|
| `Open_kv` | a corollary under added premises: the D3 instances, a namespace (D15), `Config.Mlock = false` (D13), a logger that is a pointer (`*zapBoltLogger`) |

**Every `_kv` corollary below gains `[HasExt osFsExt]`** (round 12, review 11 L3). No backend or etcdserver spec has it today: they run under OsFs (D8), so the instance is an added premise of each row, and of every spec above them.
| `DB.Begin_kv` (write), `Tx.Commit_kv`, `Tx.Stats_kv`, `Tx.Bucket_kvw`, `Tx.CreateBucketIfNotExists_kv`, `Tx.DeleteBucket_kv`, `Bucket.Delete_kv`, `Bucket.Cursor_kvw` | exact corollaries |
| `DB.Begin_kv` (read) | not a corollary: a `threadTok` (D1) |
| `DB.Stats_kv` | not a corollary: `statSlot` (D2) |
| `Bucket.Put_kv` | not a corollary: `bboltEntryMax` (D4) |
| `DB.Close_kv` | stays a trust-boundary layer (`dbCloseOk`) |
| `Tx.Rollback_kv`, `DB.Info_kv`, `Tx.Size_kv`, `Tx.DB_kv`, `Tx.Bucket_kvr`, `Bucket.Cursor_kvr`, `Cursor.Seek_kv`, `Cursor.Next_kv` | restated: `boltTx` (`ro D` where `rtxSnap` was); `isDB db` becomes `isBolt db γ.db` (D19); `rtxStats` dropped |
| `ownWTxG_fill` | restated, non-NaN (D5) |
| `ownWTxG_live`, `ownWTx_live`, `rtxStats_excl` | gone |

**Backend proof changes:**
- about 10 files restated;
- the `rtxStats` machinery deleted;
- `New` takes and returns a `threadTok`;
- `unsafePut`/`UnsafeSeqPut` need the entry bound from mvcc;
- `BNames.db : BoltName`;
- `newBackend` chooses `N`, with `N ## osN`;
- `newBoltLoggerZap`'s post is the exposed `boltLogger` (D20′), scoped to zap's standard cores;
- `boltOpenOptionsOk` states `mmapFlags = MAP_POPULATE`.

`backend.Snapshot` becomes provable.

### Decisions

**Taken by the user:**
- D1, D3, D4, D5, D7, D13 and D17;
- D18 (the fork's `getPageSize`);
- D20 in principle, as D20′;
- D22 = (b).

**Decided by me** (each recorded with its basis): D2, D6, D8–D12, D14–D16, D19, D20′ and D21.

### Infrastructure the frozen spec needs (all in this repository)

1. **D22's OsFs rule:**
   - `Impl.lean`'s `PWriteFinish` conjunct, its header text, and its Environment hypothesis;
   - `wp_osPWriteFinish`'s post;
   - `os.File.WriteAt`'s post `j = 0 ∨ j = data.length`, whatever `err`;
   - a test.
2. **`hash/fnv`:** translated with bodies (`New64a`, `sum64a`), with specs proved against a Lean
   FNV-64a (D22, "The `hash/fnv` trust boundary").
3. **D20′'s sources:**
   - `fmtErrorOk` in `Spec/fmt/`, given by `errors.New`, `fmt.Errorf` and the OsFs-backed error
     specs;
   - `(*fs.PathError).Error`, `syscall.Errno.Error` and `FileMode.String` translated with
     bodies.
4. **The backend's restatements** (the table above, each with `[HasExt osFsExt]`), and the `fileHolds` producers on the
   snapshot path, which now also hold `osInv`.

### Open items

- **The issue drafts.** Still unfiled in the repository: `issues/bbolt-cursor-prev-empty-leaf`,
  `issues/bbolt-cursor-last-empty-leaves-hang`, `issues/bbolt-writeto-meta-parity`,
  `nonissues/bbolt-bucket-name-length-unchecked`, `nonissues/bbolt-cursor-prev-after-next-end`,
  `nonissues/bbolt-getpagesize-probes-user-data`.
- **Not specified:** `View`, `Update`, `Batch`, `ForEach`, `WriteTo`, nested buckets, crash
  durability.
- **Reviewed:** rounds 1–11 (`review-11.md`: nothing blocks). Round 12 is documentation only.

## Corrections after the invariant design (2026-11-03, decided by the coordinator)

The invariant design (`bbolt-inv/design.md`, section 1, D-A..D-E) found four laws unprovable
under every representation consistent with the triples, and one documentation error. Decided by
the coordinator after the invariant design and landed with the spec; `candidate.lean` (scratch)
is unchanged, so the text above describes the frozen candidate, and these override it:

- **D-A.** `boltTx_timeless` is false of any representation: `Rollback`/`Commit` take only
  `boltTx`, and their code takes `rwlock`, `metalock`, `mmaplock`, so `boltTx` carries Iris
  invariants, which are not timeless. Replaced by `boltTx_later : isBolt db γ ⊢ ▷ boltTx tx γ q
  T -∗ ◇ boltTx tx γ q T`.
- **D-B.** `osInv` (an invariant) folded into `fileHolds` made `fileHolds_timeless` false; the
  fold's reason (no OsFs resource in the restricted-semantics statements) went with D22 = (b).
  `Open` takes `osInv` separately again (round 8's form), `fileHolds_new` no longer takes it.
- **D-C.** `txBytes`, `boltBkt`, `boltCur` (and so `curAt`) did not name the database, and
  nothing reached from `tx` alone can agree with the ghost names `boltTx tx γ` knows (Perennial's
  allocation gives no meta token; a package fact cannot hold a registry). They take `γ` after
  `tx`: `txBytes tx γ s b`, `boltBkt tx γ b n g`, `boltCur tx γ c T es pos`, `curAt tx γ es i k v`,
  in every law and triple. The general fix, allocation returning a meta token as Iris HeapLang's
  does, is proposed in `notes/perennial-changes.md`.
- **D-F** (2026-11-04, approved by the user, D-C precedent; U5b's finding after batch 17).
  `txDB` takes `γ`: `txDB tx γ db`, in `txDB_persistent`, `DB.Begin`'s post, `Tx.DB`'s and
  `DB.Info`'s pres (and the internal `DB.Begin_err`). `Tx.DB` reads `tx.db`, whose live quarter is
  in `γ`'s transaction registry (`txEntry`); a `db`-only `txDB` could not open it. Backend impact:
  the backend carries `γ.db` beside every `txDB` (`DB.Begin_kv`, `Tx.DB_kv`, `DB.Info_kv`,
  `Tx.Commit_kv` rows: restated with `γ.db`, still corollaries).
- **D-D.** `boltTx_fill` holds only for write transactions (`T.rw = true`): a reader's
  `Tx.Bucket` runs at any fraction and allocates a fresh handle each call, which no entailment
  from `boltTx … 1` finds. The backend writes `FillPercent` only in write transactions.
- **D-E.** D19's "the registry is provable" was wrong (above). The backend's corollary counts in
  "Good for etcd" and "Backend impact" are of the frozen candidate: with D-C the backend's handle,
  cursor and slice predicates (`wBkt`, `rBkt`, the cursors, returned slices) gain `γ.db`, which
  every `_kv` statement over them has in scope, so the "exact corollary" rows stay corollaries of
  restated backend predicates; with D-B `Open_kv` takes `osInv` as before round 9; with D-A the
  backend's `txLive_timeless` axiom has no counterpart (its users take `isBolt db γ.db` for
  `boltTx_later`). The rows are to be re-counted at the backend switch. `fileHolds`' docstring
  gains "every leaf at the same depth" (`rebalance` merges siblings without checking `isLeaf`;
  bbolt's own writes keep it); the statement does not change.

- **D-G** (2026-11-04, approved by the user; batch 38.1 of `notes/bbolt-proof-plan.md`, U11's
  finding). `loggerPtrOk (.ok li) := ∃ t (l : Loc), li.ty = PointerType t ∧ li.v = #l`
  (`Spec/go_etcd_io/bbolt/Options.lean`; was `∃ t, li.ty = PointerType t`). The model's interface
  values pair a type with any value, so a pointer type alone does not make the value a location;
  `Open` stores the logger and bbolt compares it with `discardLogger` (`lg != discardLogger`, a
  pointer comparison), whose proof needs a location (`dbFixed`'s `logPtrTyped`,
  `Inv/LoggerOk.OptsM.ok_logPtrTyped`). Frozen statements whose meaning changes: `OptsM.ok`, so
  `DB.Open`'s and `Options.String`'s pres (stronger premises). Backend impact: the backend's own
  `OptsM.ok` (`backend/BboltOptsDefs`) gains `loggerPtrOk o.logger` (a copy of bbolt's, so as not to import its `OptsM`), so `bbolt.Open_kv`'s
  premise carries it; `backend.newBoltLoggerZap.spec`'s post gains `⌜∃ lc : Loc, l = interface.mkOk
  (PointerType zapBoltLogger.ty) #lc⌝` (Go: `&zapBoltLogger{...}`), from which `newBackend` proves
  the logger-updated options `ok` (`OptsM.ok_withLogger`). Trust-base axioms whose statements change:
  `backend.newBoltLoggerZap.wp_proof` (stronger post: true of Go), `bbolt.Open_kv.wp_proof` and
  `Options.String.wp_proof` (stronger premise: weaker axiom), the backend's package-initialization
  axiom over `boltOpenOptionsOk` (`backend/Init.lean`: the options' `ok` now says their logger is
  nil or a location; `boltOpenOptions`' logger is nil).
