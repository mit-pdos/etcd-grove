# C-I1 with versioned take/put: `dbCrashKeep_take`/`_putSame`/`_putStep`, `dbCrash` with its mask

Review 2026-11-25, `axiom` skill, for the bbolt-crash workstream, on branch `axiom/c-i1-takeput` at
`ac822ef2cd` (etcd_safe line, `etcd-safe-t10`; parent `67150bebc8`, bbolt's versioned state in `f1126633dd`).
Earlier reviews of C-I1: [c-i1-bbolt-crash](c-i1-bbolt-crash.md) (six rounds) and
[c-i1-nopath](c-i1-nopath.md).

## What is reviewed

`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean` at `ac822ef2cd`, against `67150bebc8`:

| law | at `67150bebc8` | at `ac822ef2cd` |
|---|---|---|
| record | `dbCrashKeep γ i0 Dl Dn pd` | `dbCrashKeep γ i0 Dl Dn`, plus the hole `dbCrashHole γ i0 Dl Dn ν` |
| `_announce`, `_clear` | announce `S` with the live writer; clear with a fresh writer | dropped |
| `_half` | lends `dbHalf γ Dn` for one `={E}=∗` step, back at `Dn` or the announced `S` | replaced by the three laws below |
| `_take` | | `dbCrashKeep γ i0 Dl Dn ⊢ ∃ ν, dbHalfV γ Dn ν ∗ dbCrashHole γ i0 Dl Dn ν` |
| `_putSame` | | `dbCrashHole γ i0 Dl Dn ν ∗ dbHalfV γ Dn ν ⊢ dbCrashKeep γ i0 Dl Dn` |
| `_putStep` | | `dbCrashHole γ i0 Dl Dn ν ∗ dbHalfV γ S (ν+1) ⊢ dbCrashKeep γ i0 (if S = Dn then Dl else Dn) S` |
| `_new`, `_close` | with `pd` | the same without `pd` |
| `dbCrash` | `D' = Dl ∨ D' = Dn ∨ pd = some D'`, any mask `E` | `D' = Dl ∨ D' = Dn`, with `hE : ↑(bbolt.crashN γ.ns) ⊆ E` |

The definitions the laws are stated over (not trusted, read to see what can move the version):
- `dbHalfV γ D ν := onFs (bbolt.boltStateV γ ½ D ν)` (`InvBbolt.lean`). `onFs` is `False` unless the run has
  `FsNoErrAll`.
- `boltStateVDef B q D ν := ghostVar B.st (q/2) (D, ν) ∗ ghostVar B.bq q ()` (`Proof/go_etcd_io/bbolt/Inv/State.lean`).
  The client holds ½ of `B.st` in all, as two `dbHalfV`s. bbolt holds the other ½ as two quarters, `metaR`'s and the
  writer's, at `(treeData C, C.txid)`.
- `Tx.Commit.spec`'s update (`Spec/go_etcd_io/bbolt/Tx__Commit.lean`): `∃∃ D' ν, boltStateV γ 1 D' ν`, committed to
  `boltStateV γ 1 T.cur (ν+1)`.

## Verdict: **survives** (no counterexample), **conditional on the commit point moving**

Every law survives the attacks below, but only for a bbolt proof that fires `Tx.Commit`'s update **no later than
the `PWriteStart` step of `writeMeta`'s `writeAt`**. In the fork (`upamanyus/bbolt` @ `7d335aa3`, `tx.go:612-613`)
that step comes after `metalock.Lock()` and before `ops.writeAt`. Today's proof fires later: in
`Proof/go_etcd_io/bbolt/Commit/Step.lean:197`, `au_commit_fire` runs after `PWriteFinish`, in the case where all
4096 bytes landed. With that placement `dbCrash` is false of the model, for the same reason as the 2026-11-24
re-review: the new meta's bytes are crash candidates from `PWriteStart` on (`OsFile.announce`), while the record
still says `(Dl, Dn)`. No client can exploit this today (attack 4), so no Lean counterexample exists. But until
bbolt's crash proof moves `au_commit_fire`, the laws are not provable from bbolt. The header states the move as
already made. It needs rewording (see "Restatement" below).

`take`/`putSame`/`putStep` are sound as stated. The version settles the 2026-11-24 replay finding: a hole at `ν`
goes back only with the half at `ν` (no commit) or at `ν+1` (exactly one commit). Only `au_commit_fire` can produce
`ν+1`, and only from `(Dn, ν)`, the value the hole recorded.

## Attacks tried

1. **A record with a wrong fallback (two commits between `take` and `putStep`, or a `dbHalfV` at `ν+1` obtained
   another way).** `Tx.Commit.spec`'s update needs `boltStateV γ 1`, which is both `dbHalfV`s. The record's half is
   one of them, so a commit always passes through a `take`.
   - After two commits the halves are at `ν+2`. `putStep` needs `ν+1` and `putSame` needs `ν`, and both use one
     `ghostVar` (`boltStateV_agree`), so neither applies.
   - The version moves only in `au_commit_fire` (`Commit/Fire.lean:54`: `(D', ν') ↦ (Dn, ν'+1)`, three-way, so it
     needs bbolt's two quarters). The only other writer of `B.st` is `Open`, which allocates fresh names
     (`Open.lean:898`; `Open.spec`'s `∃ γ`). The general `st_update` in `Inv/State.lean` has no caller.
   - So a half at `ν+1` means exactly one commit, from the value the hole's `take` saw, `(Dn, ν)`.
   - The unversioned update (`commitAU_of_unversioned`, used by `batchTx__commit.lean`) returns `boltState γ 1 S` at
     an unknown `ν'`. A client cannot prove `ν' = ν+1` from it, so it cannot call `putStep`. That limits the client
     but does not break soundness.
   - Empty commits (`S = Dn`): the record stays `(Dl, Dn)`. The physical crash set is `{Dn}`, because the new meta
     and the slot it overwrites both name data `Dn` or older. **Blocked.**
2. **`putSame` after a commit.** This needs `dbHalfV γ Dn ν` while the ghost is at `ν+1`. No fragment of `B.st`
   keeps the old value: `au_commit_fire` combines all of it before the update. **Blocked.**
3. **Two records.** At most two can exist, since each holds a `dbHalfV`. Every commit then takes both halves, so
   both holes are open at the commit, and both `putStep`s move to `(Dn, S)`.
   - A hole whose half went into a new record (`take`, then `_new` with a fresh writer) is still sound. Each record
     holds a current half, and agreement ties every hole to the one ghost history.
   - Two records on different inodes are excluded by `boltIno_agree`. `dbCrash` consumes `i0` from the crash rest
     (`i0 ∉ Dx`), so it can be used only once. `_close` and `Close` need a record, not a hole.
   - **Blocked.**
4. **A crash during the meta `pwrite` while the record still says `(Dl, Dn)`.**
   - *With the plan's placement* (fire after `metalock.Lock()`, before `writeAt`, under `FsNoErrAll`): every record
     takes part in the fire, because the update takes both halves. So once `PWriteStart` has made the new meta's
     bytes candidates, every record says `(Dn, S)`, or else no record exists, only a hole and a half that `dbCrash`
     cannot use.
     - The other slot holds `Dn`'s meta, synced, because the writer holds `rwlock` and the previous commit returned
       after both syncs.
     - Under `BoltCrashWhole`, a torn new slot either fails to validate or is the slot's old meta, at txid `ν−1`.
     - So the crash image is `Dn` or `S`, inside `{Dn, S}`.
     - The fire is never undone. Under `FsNoErrAll`, `NoIoErr` makes `PWriteFinish`'s errno 0. With errno 0, `k` is
       the whole length or a nonzero page-aligned cut, and for one aligned 4096-byte page that means `k = 4096`
       (`Impl.lean`, `PWriteFinish`). So `Step.lean`'s `j = 0` case cannot happen.
   - *With today's placement* (`Step.lean:197`, after `PWriteFinish`): in the window from `PWriteStart` to
     `PWriteFinish` the record is `(Dl, Dn)` at `ν`, and a crash can keep the whole new meta, giving `S`. The laws
     are not provable there.
   - *Why no counterexample.* A client sees the fire only through `Tx.Commit.spec`, which does not say where it
     happens. At a crash inside `Commit` the client must handle both cases (unfired `{Dl, Dn}`, fired `{Dn, S}`), and
     the union contains every real outcome.
     - Turning the window into a panicking program needs a crash-aware proof of `Commit`'s internals that ties the
       fire to a later step.
     - That would be bbolt's crash proof itself, which is required to move the fire.
   - **Sound exactly when** bbolt's crash proof fires the update no later than writeMeta's `PWriteStart`. Any point
     after the writer holds `rwlock` would satisfy C-I1. bbolt's own non-crash invariant requires it to be under
     `metalock`. Without the move, the announcement (or an equivalent) has to come back.
5. **Masks.**
   - `take`, `putSame` and `putStep` are plain entailments, usable at mask `∅` inside the update's accessor. They
     allocate nothing and open nothing, so the hole carries only what the record carries. The model then needs
     `dbHalfV`, which is bbolt's `boltStateVDef` and not trusted, to carry a history lower bound (plan §1).
   - `dbCrash`'s `hE` is an extra premise: the old statement held for every `E`, so the new one is weaker.
     `γ.ns` is bbolt's own namespace (`DBNames = BoltName`), so the premise names the invariant the planned proof
     opens. Its only caller, `MemberCrash.lean:1150`, uses `E = ⊤` with `by simp`.
   - The client's update runs at `⊤ \ ↑γ.ns`, which excludes `crashN γ.ns` (no clash). **No issue.**
6. **Without `FsNoErrAll`** (a fire on landing, error paths with the update left unfired). Then `onFs` is `False`,
   so `dbHalfV` is `False` and no record can be made (`_new` needs `dbHalf`). **Vacuous.**
7. **Holding a hole across physical steps or a crash.** The hole and the record are different opaque predicates.
   While a hole is out, no record exists, and `dbCrash` cannot be used. Moving a hole to another generation would
   need a hole at that generation's `hG`, and no law converts one. **Blocked.**

## Restatement

The laws need no change. Required (docstring, before this goes up):
- `CrashInterim.lean`'s header and its "Why the laws are true" bullet say "the commit point moved before the
  meta's `pwrite`" and "Its commit point … is, under `FsNoErrAll`, just before the meta page's `pwrite` starts".
  Today's proof fires after `PWriteFinish` (`Commit/Step.lean:197`).
- They should say that the laws hold only for bbolt's crash proof that fires `au_commit_fire` no later than
  `writeMeta`'s `PWriteStart` (plan §0 F3). They should also say that this move is what lets the announcement go.
- The plan's §3 still writes `dbCrashKeep … pd` and `take`/`put` with a `commitStep` receipt. Update it to the
  versioned form (`dbHalfV` and the hole's `ν`, with the history lower bound inside `boltStateVDef`).

Recommended: make the move a tracked obligation of the bbolt crash proof, a checklist item in the plan's §2 row
for the commit chain. A future change to `Step.lean` could otherwise keep the fire on landing and still prove
everything the non-crash specs ask.

## Not tried

- A Lean counterexample: none was in reach, since every attack is blocked by `B.st`'s agreement or by the hidden
  fire point.
- Power-loss measurements: the physical argument is the same as in the earlier reviews.
- `fileRcpt`'s receipt across generations, still open from review 3.
