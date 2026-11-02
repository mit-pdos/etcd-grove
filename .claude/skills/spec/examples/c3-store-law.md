# C3's store law: the compaction revision's permit (2026-11-02)

The compactor pilot's C3 (`notes/compactor-pilot-plan.md`) asks that the store's compaction revision
be at most what the compactor's retention permit allows. mvcc's `store` writes it in
`updateCompactRev`, under `s.revMu` with `s.mu` held; a transaction reads it under `s.mu`, the
watchable store's `syncWatchers` under `s.revMu`. Its authority (`crevUB`) is split: a quarter in each
lock's resource (`muInvAt`, `revMuBody`), half in the compaction right the server's apply thread
holds. The earlier plan (M2's S5) wanted a logically atomic `store.Compact` so that a server
invariant could keep a share.

## The first version (candidate 1), in short

The whole of C3: a permit `Perm` beside `revMu`'s share; a reader's `ErrCompacted` answer carrying
`□ Perm c`; the server fixing `Perm` to the compactor's C1 permit; every compaction proposal (the
compactor's and a client's `kv.Compact`) carrying it; a client-level C3 stated in `compactkv`.

## The user's choices

- **No consumer, so the store law only.** No proof needed C3 (the cache re-lists, `compactkv` skips
  its check), and in revision mode its client content is weak. The user chose the reusable core: the
  store keeps the permit, `store.Compact` takes it, readers learn it; the server's permit and the
  client statement later.
- **Client compactions will carry the permit** (for the later stage).
- **The design, approved**: a predicate fixed at creation (a saved predicate, `crevPermIs`), kept
  beside the readers' compaction revision in both locks' resources, in place of S5. A departure from
  "TaDa, not HoCAP" (`PRINCIPLES.md`), said in the Draft: the locks already hold the shares S5 was for.
- **The new premise on `store.Compact`/`updateCompactRev`/`compactLockfree`**, and the permit added
  to the exported `mvcc_NewStore_backend_cmp`'s post, approved.

## Review rounds, and what they changed

- Round 1: the premise missed `compactLockfree` (a restore's resumed compaction); the restore
  question misread Go (`restore()` sets the field from the *finished* record; at the pin every
  restore ends at `-1`, so no option was needed); the recommended restore option (a ghost record in
  the meta keys' name) was unsound (a physical name, replaced at `Restore`; a snapshot's records are
  another member's); the permit's name must be logical (`withPhys` keeps it); the watch side could not
  go in `respOk`, which takes no names.
- Round 2: the watch side's new disjunct of `respRev` could never be selected, since a compaction
  response also satisfies the notified-log disjunct: the permit became **a conjunct outside the
  disjunction**. The permit had no path from `NewStore` to the apply thread: `New` and
  `newWatchableStore` take `Perm` and return it, the build lemmas put it in the compaction right.
- Round 3 (first tier empty): bind the right's `Perm` (the literal `True`), the restatements of
  `NewStore`'s post, `respRev_new`'s hypothesis, a default for the field.

## The approved spec (as built)

```lean
-- mvcc, InvStore.lean
structure StoreNames where ... cperm : GName := 0   -- logical: withPhys keeps it
def crevPermIs (γ : StoreNames) (Perm : Int → IProp GF) : IProp GF :=
  savedPredOwn γ.cperm DFrac.discard (fun c => iprop(□ Perm c))
def crevPermAt (γ : StoreNames) (c : Int) : IProp GF :=
  iprop(⌜c = -1⌝ ∨ ∃ Perm, crevPermIs γ Perm ∗ □ Perm c)
theorem crevPermAt_elim_lc : £ 1 ∗ crevPermIs γ Perm ∗ crevPermAt γ c ⊢ |={E}=> ⌜c = -1⌝ ∨ □ Perm c
-- muInvAt and revMuBody: "#HpM"/"#Hperm" ∷ crevPermAt γ c
-- store.Compact / updateCompactRev / compactLockfree: precondition gains crevPermAt γ (sint.Z rev)
-- NewStore / newWatchableStore / New: take Perm, post gains crevPermIs γ Perm
-- store.Read / store.Write / readView.Range: post gains crevPermAt γ crev (the transaction's)
-- InvWatchStore.lean: respRev γ pre x := (old disjunction) ∗ cmpPermOf γ x, where
def cmpPermOf (γ : WsNames) (x : RespM) : IProp GF :=
  iprop(⌜x.compactRev = W64 0⌝ ∨ (⌜0 < sint.Z x.compactRev⌝ ∗ crevPermAt γ.st (sint.Z x.compactRev)))
-- etcdserver: cmpRight's on arm gains crevPermIs E.γ (fun _ => True); cmp_store_pre gives
-- □ ∀ r, crevPermAt E.γ r
```
