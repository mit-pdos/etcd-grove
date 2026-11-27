# C-I1 swap: the six interim axioms become `CrashLaws.lean`'s theorems

Review 2026-11-27, `axiom` skill (adversarial), of `origin/bbolt-crash-swap/2026-11-26` at `1b3519cfb0`.
The swap commit's parent is `6699f26200`, whose merge base with `origin/bbolt-crash-w7/2026-11-26` is
`60ff9f070a`. The swap diff (`6699f26200..1b3519cfb0`) touches four files: `backend/CrashInterim.lean`,
`backend/CrashLaws.lean`, `dist/crash/MemberCrash.lean` (one proof line) and `notes/etcd-dist-d6.md`.
Earlier reviews: [c-i1-bbolt-crash](c-i1-bbolt-crash.md), [c-i1-takeput](c-i1-takeput.md),
[c-i1-nopath](c-i1-nopath.md), [c-i1-monotone](c-i1-monotone.md).

## What was reviewed

- **Before the swap.** `Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean` at `6699f26200`
  held two `opaque` predicates, `dbCrashKeep` and `dbCrashHole` (bodies `False`, no `go.Semantics`). It also
  held six axioms: `dbCrashKeep_new`, `_take`, `_putSame`, `_putStep`, `_close` and `dbCrash`.
- **After the swap.** `dbCrashKeep` and `dbCrashHole` are definitions:
  `onFs (bbolt.boltCrashRec …)` and `onFs (bbolt.boltCrashHole …)`. Both take `[sem : go.Semantics]`.
  - The six laws are theorems in `backend/CrashLaws.lean`. The `crashLaws` sub-namespace is gone, so they now
    sit in `backend`.
  - `CrashInterim.lean` now only re-exports them, plus `boltCrashWhole_exists`.

## Verdict: **SURVIVES**

No counterexample, no statement drift and no hidden trust. There are two findings, both low (documentation
and a gate), and neither is a soundness issue.

## 1. Statement equality (checked by elaboration)

**Method.** `c-i1-swap/SwapRev.lean` (output in `c-i1-swap/SwapRev.out`) was run on the VM with `lake env lean`,
after `vmlake build` of `CrashInterim` and `MemberCrash` at `1b3519cfb0`.

- It restates the six pre-swap axiom texts verbatim as axioms in `backend.oldStmt`, with the old file's
  `open Iris Iris.BI Classical`, its `section laws` variables and its `local instance gooseInvGS`.
- `dbCrash` gets exactly the two approved edits.
- Each restated type is compared with the theorem's type as `Expr`s, alpha-equivalence (`Expr.eqv`), plus a
  check of the binder info at every binder.

| Law | Result |
|---|---|
| `dbCrashKeep_new`, `_take`, `_putSame`, `_putStep`, `_close` | `eqv=true`, no binder-info difference: identical after elaboration (instance arguments included) |
| `dbCrash` (old text + `[sem : @go.Semantics _ L.goose_go_local_context _]` + `fileHoldsMDur`) | identical except the name of the `hE` autoParam's tactic constant (`oldStmt.dbCrash._auto_1` vs `dbCrash._auto_1`); with that name normalised `eqv=true`, and the two `_auto_1` values (the `by simp` syntax) are `eqv` |

**Where the binders sit.** The `sem` binder is right after `L L'`, as approved. The old axiom's instance
binders were anonymous; the theorem names them `S`/`ok`/`has`. Names do not matter to the type, and no
caller passes them by name.

**Instance resolution.**
- `bbolt.fileHoldsMDur` takes no `go.Semantics` (`#check @bbolt.fileHoldsMDur`). So at `⟨G, L'⟩` it needs no
  instance at `L'`, and no instance is resolved differently there.
- The record `dbCrashKeep (hG := ⟨G, L⟩)` takes the new `sem` at `L`'s local context, as its definition
  requires (`#print backend.dbCrashKeep`).

**Name shadowing.**
- The only `dbCrashKeep`/`dbCrashHole`/`dbCrash*` constants are `backend`'s.
- `crashLaws` was removed rather than kept beside `backend`, so there is no second copy.
- `backend.BoltCrashWhole` moved from `CrashInterim` to `CrashLaws` with the same body (`abbrev` of
  `bbolt.BoltCrashWhole`).
- The only caller of any of the six outside these files is `MemberCrash.lean:1095` (`backend.dbCrash`).

## 2. Is the trust gone?

`#print axioms` (VM, `1b3519cfb0`) gives `[propext, Classical.choice, Quot.sound]` for all of these:
- `backend.dbCrash`, `dbCrashKeep_new`, `_take`, `_putSame`, `_putStep`, `_close`;
- `memberCrash.memberGen_crash_law_holds`;
- `backend.boltCrashWhole_exists`.

This agrees with the swap's own `bbcrash-scratch/swap-axioms.log`. So no `sorry` and no axiom is reached.

**Other escapes.**
- No `implemented_by` or `extern` appears in `Spec/go_etcd_io/bbolt`, `Proof/go_etcd_io/bbolt`, `backend/`,
  `Proof/os` or `GooseLang/Ext/Fs`.
- The only `opaque` there that is not a `def` is `bbolt.dbCloseOk : Prop` (`Api.lean:519`), which none of the
  six statements mention.
- `boltCrashRec`/`boltCrashHole` are `@[no_expose] def`, not `opaque`.

**Vacuity.**
- *The definitions.* `dbCrashKeep = onFs (boltCrashRec …)` is `False` only when `theFs GF = none`, that is when
  there is no `FsCtx`. Building an `FsCtx` needs `FsNoErrAll`, which etcd's restricted semantics proves
  (`etcdstart/FsExts.lean:86`, `etcdFsNoErr`). `dbHalf`, `ownDB` and `txLive` sit behind the same `onFs`, so
  the record is no more vacuous than the backend's ordinary resources.
- *Producing a record.* `boltCrashRec`'s content is a version-indexed half of `boltState`, the crash invariant
  `csInvIR` at `crashN γ.ns`, `cnReg` and a synced mark or a history element. `dbCrashKeep_new` builds it
  from exactly the old axiom's premises, which are all ordinary resources of an opened backend:
  - `dbOpts` (concrete, from `storage.OpenBackend`);
  - `onFs boltIno` (persistent, inside `ownDB`'s `dbRestF`);
  - `dbHalf` (the commit invariant's half);
  - `txLive … (TxView.wr D)` (`Begin`'s writer).

  The proof gets crash mode from `bbolt.crashMode_on` and `FsNoErr` from `c.ne`. It assumes nothing extra.
  The premise list did not change (point 1), so `_new` can be applied wherever the axiom could.
- *A caller of `_new`.* No run calls `_new` yet. `MemberCrash` takes the record from `memberKeepR`, a keep that
  T10 will fill (`notes/etcd-dist-d6.md`'s A1 row says so). This is not a regression.
- *`dbCrash`'s premises.*
  - `hQ`: `BoltCrashWhole I` is `∀ i, I i → …`, so `hA1 : ∀ i0, … BoltCrashWhole (· = i0)` is the same as
    `BoltCrashWhole (fun _ => True)`. `boltCrashWhole_exists` (proved, no axioms) shows that every reachable
    machine crash has an `OsCrash` meeting it (`durCrash`).
  - `Named V'.now i0` comes from `hB1n` (B1's durable name).
  - The mask is `⊤`, which `by simp` discharges.

  None of these is new and none is impossible.

## 3. `dbCrash` concluding `fileHoldsMDur`

**Is the stronger conclusion sound?** It is a theorem whose only trust is the file extension's crash
semantics, so the question is only whether a premise is vacuous (point 2: none is).
- `fileHoldsMDur i D` asks for `osMeta i 1 m`, `osBytes i 0 1 (bs.map durB)`, `m.maps = ∅` and
  `m.size = m.lo = m.hi = |bs|`, plus `boltImage bs D`, the size bound and `boltImageRcpt`.
- That is what the file extension's crash leaves: nothing unsynced, and the size's crash bounds collapsed.
- `boltCrashRec_crash` proves it from `csInvIR_crash_keep`.

**Did the caller change preserve the meaning?**
- `MemberCrash.lean:1097` adds `ihave Hfm := bbolt.fileHoldsMDur_holds … i0 D' $$ Hfm`. `fileHoldsMDur_holds`
  is a plain entailment `fileHoldsMDur i D ⊢ fileHoldsM i D` with no other premise, so the rest of the proof
  sees exactly the old axiom's conclusion.
- `memberGen_crash_law_holds`'s statement is unchanged; the diff adds only that proof line. Its named
  hypotheses (`hQ`, `hA1`, `hB4`, `hB1`, `hB1n`) are as before.
- `dbCrash`'s `crashed` premise is now unused (`iintro H -`). It is still in the statement, so the statement
  is unchanged.

## 4. Other checks

**Top-level statements.**
- `memberGen_crash_law_holds` is referenced by no other proof (only in comments: `ImageOn.lean:168`,
  `SnapDirCrash.lean:4`). No top-level theorem is reached by this change, and none is weakened.
- The six axioms were never in `etc/tcb-baseline.txt` (0 matches at `6699f26200`, `1b3519cfb0` and
  `origin/lean`), so there is no baseline row to remove.

**Finding F1 (low, documentation).** `Proof/go_etcd_io/bbolt/Commit/Step.lean:13-14` cites
"`backend/CrashInterim.lean`, 'Condition'".
- The swap deleted that header section, which said that `Commit`'s update fires no later than the meta
  `pwrite`'s `PWriteStart` (the c-i1-takeput condition).
- The condition is now discharged by the proof itself: `Step.lean`'s `cpFired` fires before the `pwrite`, and
  the laws are theorems. But the pointer is dangling.
- Also stale: `Spec/go_etcd_io/bbolt/ApiCrash.lean:3` ("…`CrashInterim.lean`…are, sealed"), which should now
  name `CrashLaws.lean`.
- Fix: point both at `CrashLaws.lean`, or state the condition in `Step.lean`.

**Finding F2 (low, gate; already present before the swap).** `etc/api-check.py etc/api/backend.txt --check`
fails with "`MemberCrash`: imports a module that is not importable: `backend.CrashInterim`".
- The same error occurs at `6699f26200` (checked locally, source-only), so the swap did not cause it.
- The swap was the natural point to fix it: add `importable …backend.CrashInterim`, and `…CrashLaws` since it
  is imported publicly, to `etc/api/backend.txt`. Or have `MemberCrash` import `CrashLaws` directly.
- The other failures in `bbcrash-scratch/swap-gates.log` come from the merged branches, not this commit:
  - `tcb`: the `sorry` `rnRestartAllocK_law_holds` in `etcdserver/InvWalCrashSteps.lean:641`;
  - `mode`, `axiom-tok`;
  - `iris-premise`/`premise-witness` tracebacks, which are an environment problem (`git ls-files` exits 128
    on the VM).

**Not tried.**
- A Go counterexample program. Nothing is trusted any more, so a panicking program would need a bug in the
  file extension's crash semantics, which is outside this change.
- Rebuilding the whole tree. That relies on the swap's `swap-full.log` (green, 28710 jobs); my own VM build
  covered `CrashInterim` and `MemberCrash` (4575 jobs, green).
