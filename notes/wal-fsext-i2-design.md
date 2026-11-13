# I2 design: concurrent metadata calls, blind directory fds, region ownership over `fsExt`

**Date:** 2026-11-13. **For:** `notes/wal-fsext-plan.md` §4.1 row I2 (§0 item 2, §2.1, §5 Q9, §6 "Q9 additive").
**Read against:** `lean` at `5fa596b038` plus the wal-fsext notes. Abbreviations: FS/ = `GooseLang/Ext/Fs/`,
S/ = etcd `server/v3@…0b50f04262d9/storage/wal/`, FU/ = `client/pkg/v3@…0b50f04262d9/fileutil/`.

## 0. Decisions in one screen

1. **No trusted change.** Nothing in `Impl.lean`, `Tree.lean` or `Paths.lean` changes. The semantics
   already allows overlapping path calls. It already orders crashes by `Follows`, not by a prefix, and
   already lets a directory fd stay open across renames. Only the program logic, which is untrusted,
   forbids these today.
2. **Two modes per generation.** The *legacy* mode is today's whole-history logic. Its statements do
   not change: `osTree`, `osCall`, `osDirFd`, every `wp_os*G`/`wp_osOpen*`/`wp_osDir*`, `crashRest_tree`
   and `TreeCrashed` keep their text. The *shared* mode is new and is entered once, irreversibly, by a
   switching `CallBegin` that consumes `osTree 1 R V`. A generation starts in legacy mode, as now
   (`treeStart`, `treeLeft`). walfs, crashlog, minibolt and `LinuxFs/Proof/os/{Ns,OpenFile}.lean` stay
   in legacy mode untouched. The WAL, and later the composed server, use shared mode.
3. **Claims.** Shared mode's region resource is the *name claim* `osNames j N dq h`. It covers the names
   `N` (a finite set, or the complement of one) of directory inode `j`, with their history `h`. A claim
   held whole lets its holder change those names. A fraction freezes them: that is the "spine" that
   keeps a path resolving. A library's region is the claims it holds. Claims split and merge freely.
4. **Calls hold no view.** A shared call holds a fraction of a *call permission*, `osCallPerm`. A
   directory rename needs all of the permission, which is the semantics' "no other call in flight".
   Shared directory fds hold nothing, so every shared dfd is "blind". A read's exactness comes from the
   claim the reader presents at each step.
5. **One discipline makes crashes tractable: per-name sequentiality.** A step may change a name only if
   its call began after the previous change of that name took effect. The spec premise is
   `h.next ≤ s`. Without this rule a `Follows`-closed crash can leave a tree that is not `TreeWf`, so
   `FsInit` fails and the ghost state cannot be re-initialised (§4.3). With it, every closed set is a
   *consistent cut*. Each name comes back as it was right after its last kept operation.
6. **What a region concludes alone.** At a crash, a region gets a kept set `K` of its own entries. `K` is
   closed under `Follows` restricted to the region, which is exactly the global rule's projection
   (§4.1). `K` contains every entry below a commit bound. Per name, per thread, and for the whole region
   when its calls do not overlap, `K` is a prefix. Cross-region ordering is visible only when the regions'
   claims are taken jointly.

## 1. What the semantics says (the facts the design rests on)

- **Calls.** `CallBegin` records the log's length (FS/Impl.lean:720-724). The call's step resolves its
  path against the tree *at the step* (`st.lookup`, `st.parent`: :454, :601-625, :768-808). The step
  logs `⟨o, start⟩` (`metaDo`, :495-498). So start ≤ index for every entry. Calls overlap freely. The
  only stuck case is a directory `Rename` while any other call is in flight (:770-771). The header
  argues this case away for Linux's component-wise walk (:81-87, :767). A model that skips a step leaves
  its call in flight forever (:715-718).
- **Operations act by inode and name** (`MetaOp.apply`, FS/Tree.lean:76-84). `create j b`, `remove j b`
  and `mkdir j b j'` touch `(j,b)`. `mkdir` also writes the fresh directory `j'`. `rename j b j' b'`
  writes both names and *re-reads* `(j,b)` at replay (a no-op if it is absent).
- **Crash** (`MachineCrash`, :873-885). The crash keeps a set `S` with three properties: it contains the
  committed entries, it is `Closed` under `Follows` (Tree.lean:109-115: `y < x ∧ y < log[x].start`), and
  the tree after the crash is `replay (keptOps S) treeDur`. `commitAll` (:504-506) commits a prefix. The
  committed set starts empty at boot and after a crash (:875, :891), so it is always a prefix `[0,c)`.
- **DirSync** commits everything logged (:727-730). It works on any directory fd, including one on a
  removed directory, and needs no view.
- **DirReadNext** (:739-760) tolerates concurrent changes. `note` (:480-487) clears `untouched` and
  `returned` only for names an operation touches in that directory.

What forbids concurrency today is all in the logic. `wp_metaStep` (FS/TreeSpecsMeta.lean:245) needs
`MetaPre` (:31-38): `calls = {[k := s']}`, `s' = length`, `dfds = ∅`, `Sequential`. `TreeCoh`
(FS/Ghost.lean:432-441) keeps `seq` and every call's `start = length`. `callRes`/`rdRes` (:889-900) make
each call and each dfd hold a fraction of the history. `machineCrash_init` (FS/CrashFiles.lean:66) gets
`FsInit` from `crash_seq` (FS/Crash.lean:100), which needs `Sequential`.

## 2. Ghost state

### 2.1 Modes in the state interpretation

The new names in `OsGS` (Ghost.lean:562) are:

- `γs`: the shared history, an auth of `histMap`, like `γd`.
- `γdfS` and `γcS`: the shared dfds and calls.
- `γperm`: the call permission, a fractional token.
- `γlen`: a `MonoNat` of the log's length (Perennial `Ghost/MonoNat.lean`).
- `γlog`: a `MonoList` of the log entries (`Ghost/MonoList.lean`).
- `γcom`: I1's commit counter, a `MonoNat` of a known-committed prefix. It lives *outside* the mode
  split, so both modes share it. I1 should allocate it this way.

```
treeCtx hL st := (∃ V Γdf Γc, treeWorld …)                              -- legacy, as now
             ∨ (∃ V0 Vs Γdf Γc,                                        -- shared
                  gAuth γd (histMap (R, V0)) ∗ gElem γd () 1 (R, V0) ∗ gAuth γdf ∅ ∗ gAuth γc ∅  -- legacy frozen
                ∗ ⌜FsTreeWf st ∧ TreeCohS st Vs Γdf Γc⌝ ∗ gAuth γs (histMap (R, Vs))
                ∗ gAuth γdfS Γdf ∗ gAuth γcS Γc ∗ callResS Γc)          -- callResS: [∗map] t ↦ (s,q), osCallPerm q
structure TreeCohS st Vs Γdf Γc where
  hist   : Vs = (st.fs.treeDur, st.fs.metaLog)
  starts : ∀ x e, log[x]? = some e → e.start ≤ x
  pss    : PerSlotSeq log          -- §4.3
  dre    : DirRenameExcl log       -- a dir rename x: every later entry z has x < z.start
  calls  : ∀ t, (Γc !! t).map (·.1) = st.proc.calls !! t ∧ ∀ s, … → s ≤ log.length
  fds/ph : Γdf mirrors st.proc.dfds; PhOkS for each read (§2.4)
```

In shared mode the state interpretation owns the *whole* legacy fragment `γd`. A client holding any
legacy fragment (`osTree`, `osCall`, `osDirFd`) therefore proves by validity that the mode is legacy. So
every legacy spec keeps its statement, and its proof gains a two-line case split. The shared mode is
irreversible: no legacy fragment can ever exist in it again.

### 2.2 The shared invariant and the resources

```
osShN := nroot .@ "osfs" .@ "tree"
osSharedInv R := inv osShN (∃ Vs Γn,
   gElem γs () 1 (R, Vs) ∗ gAuth γn Γn ∗ ⌜RootsOk R ∧ NamesCoh R Vs Γn⌝
 ∗ MonoNat.auth γlen |Vs.2| ∗ MonoList.auth γlog Vs.2)

NameSet := only (bs : List GoString) | except (bs : List GoString)
structure NamesH where              -- what a claim knows of its names
  boot : Ents                       -- their entries in the generation's boot tree (Vs.1), restricted to N
  ents : List (Nat × LogEntry × Ents)  -- each entry meeting (j,N): index, entry, the names' entries right after
  cur  : Ents                       -- now
NamesH.next h := (h.ents.getLast?.map (·.1 + 1)).getD 0
NamesH.log h x e c := { h with ents := h.ents ++ [(x, e, c)], cur := c }

osNames j N dq h := gElem γn (j, N) dq h          -- fractional
osCallPerm q     := gElem γperm () (own q) ()
osCallS t s q    := gElem γcS t 1 (s, q)          -- shared call t, begun at log length s, holding q of the permission
osLogLb n        := MonoNat.lb γlen n             -- persistent
osLogEnt x e     := MonoList.idx γlog x e         -- persistent
osCommitLbS n    := MonoNat.lb γcom n             -- persistent; I1's fact (entries < n committed)
osDirFdS fd j ph := gElem γdfS fd 1 (j, ph)       -- ph : DirPhS := idle | reading N r0 rs | done
osPathS R p dq (js : List Ino) :=                 -- the spine: p = joinPath r [c₁..cₘ], (r, j₀) ∈ R
  [∗ list] k ↦ c ∈ cs, ∃ h, osNames jₖ (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir jₖ₊₁)⌝
```

`NamesCoh R Vs Γn` has three parts:

- For each claim `(j,N) ↦ h`:
  - `h.boot = (entsOf Vs.1 j)|N`;
  - `h.ents` lists exactly the log entries whose footprint meets `(j,N)` (§4.3), with the names' entries
    after each;
  - `h.cur = (entsOf Vs.now j)|N`.
- For every directory of `Vs.now` (removed ones included), the `N`s claimed under `j` partition all
  names.
- No other key exists.

The auth `γn` sits in the invariant, not in the state interpretation, so the split and merge lemmas are
plain fancy updates that need no step:

```
osNames_split  : osSharedInv R ⊢ osNames j N 1 h ={↑osShN}=∗ osNames j (N ∩ M) 1 (h|M) ∗ osNames j (N \ M) 1 (h|¬M)   -- M finite
osNames_merge  : the converse; osNames_frac : fractional in dq, agreeing on h
osNames_next   : osSharedInv R ⊢ osNames j N dq h ={↑osShN}=∗ osNames j N dq h ∗ osLogLb h.next
osPathS_lookup : (in a step proof) osPathS R p dq js ∗ coherence ⊢ ⌜st.lookup p = some (.dir (js.getLast))⌝
```

### 2.3 Entering shared mode, and `CallBegin`

```
wp_osCallBeginShare (R V) (q) :
  {osInv ∗ osTree 1 R V}  CallBegin #()
  {t. osSharedInv R ∗ osCallS t |V.2| q ∗ osCallPerm (1 - q)… ∗ osLogLb |V.2|
      ∗ [∗map] j ↦ _ ∈ V.now, osNames j (.except []) 1 (namesInit V j)}
wp_osCallBeginS (q1 q2 n) :
  {osInv ∗ osSharedInv R ∗ osCallPerm (q1+q2) ∗ osLogLb n}  CallBegin #()
  {t. ∃ s, ⌜n ≤ s⌝ ∗ osCallS t s q2 ∗ osCallPerm q1 ∗ osLogLb s}
```

The switch's log `V.2` is legacy-sequential, which implies `PerSlotSeq` and `DirRenameExcl`. The switch
also allocates `osSharedInv`. A client gets `h.next ≤ s` for the step's premise as follows: take
`osLogLb h.next` from `osNames_next`, then call `CallBegin`. Every shared spec needs
`↑osN ∪ ↑osShN ⊆ E`.

### 2.4 Shared dfd reads, with no view held

`DirPhS.reading N r0 rs` records the claim set `N` the reader shows, the log length `r0` when the read
began, and the names of `N` returned. `PhOkS` is a pure fact that every step preserves:

```
(∀ x, r0 ≤ x < |log| → footprint(log[x]) ∩ (j,N) = ∅) →
   ∀ b ∈ N, u b = s b = present st j b ∧ (r b ↔ b ∈ rs)
```

Once something touches `N`, the hypothesis is false for good. An operation that does not touch `N`
leaves `N`'s bits alone (`note`, Impl.lean:480-487). The read spec asks for the claim with
`h.next ≤ r0`, which says that nothing touched `N` since the read began. `rdRes` holds nothing.

## 3. The WP specs (shared mode; FS/ level)

Every metadata spec has the shape `{osInv ∗ osSharedInv R ∗ osPathS R d dq js ∗ claims ∗ osCallS k s q ∗
⌜h.next ≤ s⌝…} step {e. osCallPerm q ∗ osPathS … ∗ claims' ∗ …}`, with `j := js.getLast`. Logging an entry
returns `osLogEnt x ⟨o,s⟩ ∗ osLogLb (x+1)` and `h' = h.log x ⟨o,s⟩ cur'`. On a failure "with or without
the effect" (Impl.lean :783-787 and the like), the post is a disjunction of `h' = h` and the logged form.

```
-- open(d/b, O_CREAT[|O_WRONLY…], no O_TRUNC)   (WAL: createNewWALFile(p,false), S/wal.go:260; file_pipeline.go:78)
wp_osOpenCreateS d b js h k s q fl (hb : NameOk b) (hs : h.next ≤ s) (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
  {… ∗ osNames j (.only [b]) 1 h ∗ osCallS k s q}  Open(tok k, d/b, fl)
  {(fd, e). osCallPerm q ∗ osPathS … ∗ ∃ h', osNames j (.only [b]) 1 h' ∗
     ( (∃ i, h.cur !! b = some (.file i) ∧ h' = h ∧ (e = 0 → osFd fd 1 (openFd i fl)))      -- existed
     ∨ (h.cur !! b = none ∧ ∃ x i, h' = h.log x ⟨.create j b i, s⟩ (<[b := .file i]> h.cur) ∗ osLogEnt … ∗
          osLogLb (x+1) ∗ osMeta i 1 newMeta ∗ (e = 0 → osFd fd 1 ⟨i, …⟩))                   -- created (maybe with e ≠ 0)
     ∨ (e ≠ 0 ∧ h' = h)) }
-- the O_TRUNC variant additionally takes osMeta i 1 m ∗ bytes, as wp_osOpenFile does today.
-- open of an existing file without O_CREAT: a fraction of the claim suffices, no entry.

wp_osUnlinkS  (hi : h.cur !! b = some (.file i)) :
  {… ∗ osNames j (.only [b]) 1 h ∗ osCallS k s q}  Unlink(tok k, d/b)
  {e. … h' ∈ {h, h.log x ⟨.remove j b (.file i), s⟩ (delete b h.cur)}, the second if e = 0}

wp_osRenameFileS  (hN : bs, bt ∈ N₁ ∪ N₂) (hne : bs ≠ bt) (hsrc : cur bs = some (.file i)) (htgt : cur bt ≠ some (.dir _)) :
  {… ∗ osNames j N₁ 1 h₁ ∗ osNames j N₂ 1 h₂ ∗ osCallS k s q ∗ ⌜h₁.next ≤ s ∧ h₂.next ≤ s⌝}   -- N₁ = N₂ allowed via one claim
  Rename(tok k, d/bs, d/bt)
  {e. … both claims logged with o := .rename j bs j bt (.file i) (cur bt), the new cur moving bs to bt}
-- the cross-directory version takes two spines and claims on j and j'.

wp_osRenameDirS  (hq : q1 + q = 1) (hsrc : cur bs = some (.dir J)) (htgt : cur bt = none) :
  {… ∗ osNames j N 1 h ∗ osCallS k s q ∗ osCallPerm q1}  Rename(tok k, d/bs, d/bt)
  {e. osCallPerm 1 ∗ … logged with .rename j bs j bt (.dir J) none}
-- No other call is in flight: whole_alone for γperm. Claims under J are inode-keyed and move with it.
-- No other holder can keep a spine through (j,bs), because the full claim excludes it. Onto an empty
-- directory: also takes osNames J_old (.except []) 1 hOld with hOld.cur = ∅ (its footprint).

wp_osMkdirS  (hn : h.cur !! b = none) :
  {… ∗ osNames j (.only [b]) 1 h ∗ osCallS k s q}  Mkdir(tok k, d/b)
  {e. … ∨ ∃ x J, h' = h.log x ⟨.mkdir j b J, s⟩ (<[b := .dir J]> h.cur) ∗
        osNames J (.except []) 1 ⟨∅, [(x, ⟨.mkdir j b J, s⟩, ∅)], ∅⟩ ∗ …}

wp_osRmdirS  (hb : h.cur !! b = some (.dir J)) (he : hJ.cur = ∅) (hs : h.next ≤ s ∧ hJ.next ≤ s) :
  {… ∗ osNames j (.only [b]) 1 h ∗ osNames J (.except []) 1 hJ ∗ osCallS k s q}  Rmdir(tok k, d/b)
  {e. … both logged with .remove j b (.dir J); J keeps its (empty) claim}

wp_osOpenDirS :  {osInv ∗ osSharedInv R ∗ osPathS R p dq js ∗ osCallS k s q}  Open(tok k, p, O_RDONLY)
  {(fd, e). osCallPerm q ∗ osPathS … ∗ (e = 0 → osDirFdS fd (js.getLast) .idle)}      -- blind: holds nothing

wp_osDirSyncS (n) :  {osInv ∗ osDirFdS fd j ph ∗ osLogLb n}  DirSync fd
  {e. osDirFdS fd j ph ∗ (⌜e = 0⌝ -∗ osCommitLbS n)}            -- needs no claim and no view
wp_osDirCloseS :     {osInv ∗ osDirFdS fd j ph}  DirClose fd  {e. emp}

wp_osDirReadNextS (hph : ph = .idle ∨ ph = .reading N r0 rs ∧ h.next ≤ r0) :
  {osInv ∗ osSharedInv R ∗ osDirFdS fd j ph ∗ osNames j N dq h}  DirReadNext fd
  {(b, done, e). osNames j N dq h ∗ ∃ r0 rs, ⌜ph ≠ .idle → (r0, rs) as in ph⌝ ∗
     ( (e = 0 ∧ done = 0 ∧ NameOk b ∧ (b ∈ N → (h.cur !! b).isSome ∧ b ∉ rs) ∗ osDirFdS fd j (.reading N r0 (rs ++ [b])))
     ∨ (e = 0 ∧ done = 1 ∧ (∀ b ∈ N, (h.cur !! b).isSome → b ∈ rs) ∗ osDirFdS fd j .done)
     ∨ (e ≠ 0 ∗ osDirFdS fd j (.reading N r0 rs)) )}
-- A name outside N is only NameOk and may repeat (POSIX). This suffices for readWALNames (the WAL holds
-- its directory's names) and for purge (FU/purge.go:60, which locks and re-checks what it finds).

wp_osLstatDirS : the spine plus a fraction of the claim on the last name gives the isDir result.
```

The `os`-level counterparts (`os.OpenFile`, `Rename`, `Remove`, `Mkdir`, `Readdirnames`, a dir's `Sync`
and `Close`) are each a second triple, `specS`, next to the existing one. `os.OpenFile.specCreate` is the
precedent. Each threads `osCallPerm` fractions through one `CallBeginS` per attempt
(LinuxFs/TrustedCode/os.lean:166-172, :563-575, :601-630).

## 4. Crashes

### 4.1 What a region concludes alone (the soundness question of the brief)

Let `I_R` be the indices of the entries in a region's claims. Let `S` be the crash's kept set.

**Claim A: projection.** `K := S ∩ I_R` is closed under `Follows` restricted to `I_R`. This is
immediate: `Follows` is a relation on global indices, and closure holds pairwise.

**Claim B: no hidden chains.** A chain `x →Follows z →Follows y` through an outside entry `z` gives
nothing new. We have `y < z.start ≤ z < x.start`, using `start ≤ index` (§1). So `Follows x y` holds
directly.

**Claim C: tightness.** Every `K' ⊆ I_R` that is closed in `R` and contains `I_R ∩ [0,c)` is
`S ∩ I_R` for some legal `S`. Take `S := K' ∪ [0,c) ∪ {y ∉ I_R | ∃ x ∈ K', y < x.start}`. That set is
closed by Claim B, and its new members in `R` already lie in `K'`. So "`R`-closed and containing the
commit bound" is exactly what `R` can know alone. It is not "a prefix of `R`'s entries".

**Claim D: commits.** Commits are global. `committed` is a prefix `[0,c)` (§1). Any library's
`DirSync` gives `osCommitLbS n`, and that covers every region's entries below `n`.

**Claim E: what does depend on other regions.** Whether `x ∈ R` is kept *forces* `y ∈ R'` whenever
`y < x.start`. Region `R'` sees that forcing only through a fact both regions can name. Two such facts
work: `osLogLb (y+1)` held when `x`'s `CallBegin` ran, which gives `y < x.start`, and a joint application
of the region lemma to `R ∪ R'`. Alone, `R'` must allow `y` dropped.

**Prefixes, derived.**

- *Per name:* by `PerSlotSeq`, `K ∩ ops(b)` is a prefix of `b`'s operations.
- *Per thread:* if a thread's entries `T ⊆ I_R` each began after its previous one returned, then `K ∩ T`
  is a prefix of `T`.
- *Whole region:* `K` is a prefix of `I_R` iff `R`'s calls never overlapped. Legacy `Sequential` is the
  case `R` = everything.

The WAL meets the per-thread case, not the whole-region one. The pipeline's create of `1.tmp`
(file_pipeline.go:77-78) overlaps the main thread's rename of `0.tmp` (S/wal.go:936), and later the
server's purge unlinks (FU/purge.go:76) overlap cut's renames. Plan §2.3 ("TreeCrashed keeps a prefix, so
the remaining files are a suffix") and §2.4 item 3 must be re-argued as follows:

- the kept renames form a prefix of cut's renames, because one thread does them;
- the kept unlinks form a prefix of purge's, oldest first;
- an unlinked file's rename precedes the unlink's start (purge's `ReadDir` saw it), so it is kept with it.

So the surviving `.wal` files are still a contiguous run. The conclusion holds, and the argument changes.

### 4.2 The crash lemmas

```
TreeCrashedC V V' := ∃ S, Closed V.2 S ∧ (∀ y, S y → y < |V.2|) ∧ V' = (replay (keptOps V.2 S) V.1, [])
treeCrashed_C   : TreeCrashed V V' → TreeCrashedC V V'
treeCrashedC_seq: Sequential V.2 → TreeCrashedC V V' → TreeCrashed V V'

-- crashRest (CrashTok.lean:166): its body gains the mode. Legacy: as now (TreeCrashed V V').
-- Shared: gAuth γs (histMap (R, Vs)) ∗ gElem γd () 1 (R, V0) ∗ the old γcom auth ∗
--   ⌜TreeCrashedC Vs V' ∧ PerSlotSeq Vs.2 ∧ DirRenameExcl Vs.2 ∧ [0, c) ⊆ S⌝.
-- The new generation's history (treeLeft, :157) stays whole and legacy, as now.
crashRest_tree   -- statement unchanged; in shared mode its premise contradicts the stashed γd fragment

crashRest_treeS (Q L L' D V') :                  -- new
  crashRest … D false V' -∗ ⌜∃ Vs, TreeCrashedC Vs V'⌝ ∗ osTree (L := L') 1 R V' ∗ crashRest … D true V'

crashRest_region (Q L L' D tt V') (cl : List (Ino × NameSet × DFrac × NamesH)) (n) :  -- new
  crashRest … -∗ (osSharedInv R, opened: its body) -∗ ([∗list] c ∈ cl, osNames (L:=L) c…) -∗ osCommitLbS (L:=L) n -∗
  ⌜RegionCrashed cl n V'⌝ ∗ (everything back)
RegionCrashed cl n V' := ∃ K ⊆ idx cl,
    (∀ x ∈ K, ∀ y ∈ idx cl, y < (ent cl x).start → y ∈ K)       -- R-closed (Claim A)
  ∧ (∀ y ∈ idx cl, y < n → y ∈ K)                                -- commits (Claim D)
  ∧ ∀ c ∈ cl, ∀ b ∈ c.N, V'.now.entry c.j b = valAfterKept c.h K b
valAfterKept h K b := b's entry in the Ents recorded with the last (x, e, E) ∈ h.ents with x ∈ K and b touched by e; else h.boot !! b
```

The client lemmas go in `CrashRegion.lean`, all pure: `regionCrashed_prefixName`,
`regionCrashed_prefixThread`, `regionCrashed_hb` (from `y < x.start`), `regionCrashed_commit`, and
`regionCrashed_mono` (a sub-list of claims concludes the restriction).

`crashRest_take_runs_keep` and `crashRest_take_tok_keep` keep their statements. Their
`Named V'.now i → fo.isSome` combines with `RegionCrashed`: if a claimed name holds `.file i`, then `i` is
named and its file is kept.

How a client's crash invariant uses claims, as in `cfInv` (LinuxFs/Proof/os/CrashFile.lean:131) but per
region:

- The library's invariant holds half of each claim, and the holder thread the other half.
- The invariant states `∀ K, RegionCrashedFor h⃗ K → Good (valAfterKept h⃗ K)`. Each shared step updates
  the claim's history and re-proves this "Good under every R-closed `K`" for the new entry. That proof
  usually needs only the per-name prefix and the happens-before edges the library itself created.
- At the crash, `crashRest_region` produces the `K`, the new generation starts in legacy mode, and the
  top level switches it to shared mode and hands each library the new claims for its names.

The WAL's `walInv` "share of the tree" (plan §2.1) is exactly its claims:

- the WAL directory's `.except ["0.tmp","1.tmp"]`, held by the main thread;
- `.only ["0.tmp"]` and `.only ["1.tmp"]`, held by the pipeline, or parked in `walInv` between hand-offs;
- spine fractions for `member` and `member/wal`.

### 4.3 Why per-name sequentiality, and the consistent-cut theorem

**Footprints.** `fp(create/remove j b) = {(j,b)}`. `fp(mkdir j b J) = {(j,b)} ∪ (J,*)`.
`fp(rename j b j' b' n old) = {(j,b),(j',b')} ∪ (J_old,*)` when it replaces a directory, and
`fp(remove j b (.dir J)) = {(j,b)} ∪ (J,*)`. `PerSlotSeq log` says: for every entry `x` and every earlier
`y` with `fp(y) ∩ fp(x) ≠ ∅`, `y < x.start`. The step premise `h.next ≤ s` maintains it, because the
claim's `ents` lists every earlier entry meeting the step's footprint. For `mkdir`, `J` is fresh, since it
is `≥ nextIno` and every inode in the log is below `nextIno` (`FsTreeWf`, Ghost.lean:354-364).

**Necessity.** Here is a counterexample without the rule. Directory `d/sub` (inode `J`) holds only `f`.

1. Thread B runs `CallBegin`, so `start = n`.
2. Thread A unlinks `d/sub/f`: entry `y = n`.
3. Thread B's `rmdir d/sub` steps: `J` is empty now, entry `x = n+1`, start `n`.

`Follows x y` fails (`y ≮ n`), so a crash may keep `{x}` and drop `y`. The replay removes `sub` but
leaves `f` in the unreachable `J`. That violates `TreeWf`'s second clause (Tree.lean:139-145), so the
crash state is not `FsInit` (Impl.lean:889-896) and `os_local_crash` (CrashTok.lean:333) cannot
re-initialise. Similarly, a kept `rename` whose source's `create` was dropped replays as a no-op
(Tree.lean:81-83), so "name `b` holds what the rename put there" would be false.

Linux has neither outcome: jbd2 puts the unlink's handle in a transaction no later than the rmdir's. The
model is only coarser than Linux here. That is sound, but the logic must exclude these logs. Under the
rule, B's step needs `osNames J (.except []) 1 hJ` with `hJ.next = y+1 ≤ s`, which is impossible after
an early `CallBegin`. The os models do `CallBegin` right before the step, with the claim held from the
spec's precondition, so real code is unaffected.

**Theorem `closed_cut` (TreeCut.lean, pure).** Assume:

- `starts`, `PerSlotSeq`, `DirRenameExcl`, and `FsTreeWf`'s prefix well-formedness (Ghost.lean:356);
- `S` is closed.

Then:

1. every kept operation reads the same values on its footprint as in the run;
2. each slot of `replay (keptOps S) treeDur` equals its value right after its last kept operation;
3. that tree is `TreeWf` with all its named files in `files`.

*Proof sketch.* (1) is by induction on index. The previous operations on each footprint slot are kept
(per-slot prefix) and replayed faithfully, and other operations do not write the slot. (2) follows from
(1). For (3), a file or directory sits at the end of its location chain. A chain's kept part is a prefix,
since each move touches the slot it leaves, so every node is named at most once. Directory renames are
`Follows`-chained (`DirRenameExcl`), so the kept ones are a prefix. Therefore every directory that
exists in both the real tree just before the first dropped directory rename and the replay sits at its
real position. The extra directories (an `rmdir` dropped) are leaves or hang under positions that the
kept chain fixes, and a removed directory is empty because its footprint covers all its names. So the
replay is acyclic, reachable or removed-and-empty, and the `rename` preconditions (`¬ IsUnder`, empty
target) hold in the replay. `osCrash_rel` (CrashFiles.lean:97) in shared mode gets `FsInit` from this
theorem, not from `crash_seq`.

### 4.4 Soundness of the specs against the semantics, per rule

- **Progress.**
  - Each spec's step exists because the spine fractions and the full claim fix `lookup`, `parent`,
    `TreeName`, `EmptyDir` and `RenameOk`, so no one else can change them.
  - `CallBegin` always finds a fresh token (`exists_fresh2`, TreeSpecs.lean).
  - The only concurrency-stuck case, a directory `Rename`, is excluded by `osCallPerm 1`.
  - Open-with-`O_TRUNC` checks `BusyAt`, which the file's `osMeta 1` excludes (`tokRes_meta_whole`).
- **Independence.** The new entry writes only `fp(o)`, so every other claim's `cur` is unchanged. This is
  a pure lemma, `apply_frame`. Shared dfds' `PhOkS` survive by §2.4.
- **Linearization.** The step is the linearization point: `metaDo` is atomic. The start matters only to
  `Follows`, and the specs expose it as `s` with `osLogLb` bounds.
- **Concurrent data steps.** `pwrite` and the like are `TreeFrame` (`wp_os_step`, World.lean) and touch
  neither the tree nor dfds.
- **DirSync.** The fd's mere existence suffices (Impl.lean:727). The shared dfd's coherence needs only
  `df.ino ∈ tree` (`FsTreeWf.dfds`), and removed directories stay in the tree (Tree.lean:80).

## 5. Migration

**Kept as is (statements and proofs):**

- `LinuxFs/Proof/os/{Ns,OpenFile,CrashFile,CrashSt*,CrashOps,Crash*}.lean`;
- walfs (`SegLog*`, `DirSwap*`, `DSTree`, `Boot`), crashlog, minibolt (bboltfs).

They live in legacy mode, and every extension statement they use is unchanged.

**Re-proved inside FS/ (internal):**

- `World.lean`: `treeWorld` becomes the legacy branch, plus a new `wp_fs_stepM` that is mode-generic.
  `wp_fs_stepT` keeps its name but gains a legacy-witness premise (any `γd`/`γdf`/`γc` fragment). It is
  used only in FS/ (TreeSpecs, TreeSpecsMeta, TreeSpecsOpen, TreeSpecsDirFd). Before changing it, check
  that the bbolt-port branch does not call it.
- About 20 legacy specs get a two-line mode split each.
- `treeCtx_frame`, `os_local_init` (legacy start) and `os_local_crash`/`osCrash_rel` gain the mode.
- `crashRest`'s body gains the mode; `crashRest_tree`'s statement is unchanged.

**Composition caveat (Q9).** Additive keeps the bbolt port building. But one process (the etcd server)
runs in *one* mode, so once the WAL needs shared mode, bbolt's few path calls must use the shared `os`
triples: `OpenFile(db, O_RDWR|O_CREATE)` and the flock open. Tell the bbolt agent to state its file's
ownership so that it can later take an `osNames j_snap (.only ["db"])` claim and a spine. Re-proving
those calls is small.

**New modules:**

| Module (FS/ unless noted) | Content | Lines |
|---|---|---|
| `TreeCut.lean` | footprints, `PerSlotSeq`, `DirRenameExcl`, `closed_cut` (1)-(3), `apply_frame` | 900-1300 |
| `NamesGhost.lean` | `NameSet`, `NamesH`, `NamesCoh`, split/merge/log/mkdir lemmas, `PhOkS` | 500 |
| `Ghost.lean`, `World.lean` (edits) | new `OsGS` names, `treeCtx` modes, `TreeCohS`, `wp_fs_stepM` | +450 |
| `TreeShared.lean` | `osSharedInv`, the switch, `CallBeginS`, `osPathS`, `osLogLb`/`osLogEnt`, split/merge, `LstatDirS` | 550 |
| `TreeSharedMeta.lean` | `wp_metaStepS` (`MetaPreS`/`MetaPostS`), unlink, rmdir, mkdir, rename file, rename dir | 800 |
| `TreeSharedOpen.lean` | open existing, create, `O_TRUNC`, dir | 600 |
| `TreeSharedDirFd.lean` | `DirSyncS` (with I1), `DirCloseS`, `DirReadNextS`, `FdKind` | 450 |
| `CrashFiles.lean`, `CrashTok.lean` (edits) | modes, `TreeCrashedC`, `crashRest_treeS`, `crashRest_region`, `osCrash_rel` via `closed_cut` | +500 |
| `CrashRegion.lean` | the client lemmas of §4.2 | 300 |
| legacy re-proofs (TreeSpecs*, CrashTok) | mode splits | +250 |
| `LinuxFs/Spec/os/*` `specS` + `LinuxFs/Proof/os/{NsS,RenameS,RemoveS,MkdirS}.lean` | `os`-level shared triples | 1000 |

**Estimate:** about 7k lines, **4 agent-weeks (3.5-5)**. The plan's I2 row says 3-4; `closed_cut` is the
uncertain part.

**Order:**

1. **`TreeCut.lean` first.** It is pure, the highest risk, and can start now in parallel with I1. Begin
   with the counterexample above as a `#eval`/`example` to pin `PerSlotSeq`'s form.
2. **The mode split in `Ghost`/`World`/`CrashTok`, with the legacy re-proofs.** Land it alone: no client
   statement changes, and the build stays green for the bbolt agent.
3. **Shared ghost:** `NamesGhost`, `TreeShared`, the switch and `CallBeginS`.
4. **Meta specs, then Open, then DirFd.** DirSync's `osCommitLbS` comes once I1 has put `γcom` outside the
   mode split.
5. **Shared crash:** `crashRest_region`, `osCrash_rel`.
6. **`os`-level `specS` triples.**
7. **Optional de-risking client** before the WAL: a two-goroutine "tmp pipeline" in `examples/osfs/walfs`
   that mirrors `file_pipeline.go`, with a crash theorem over `crashRest_region`.

**Risks:**

1. `closed_cut`'s proof is the biggest risk. The rename-replaces-directory case and removed directories
   are the delicate parts. Fallback: restrict shared-mode renames to absent targets or files, which is
   all the WAL needs (S/wal.go:333, :936), and drop the replaced-directory clause.
2. I1 interplay: `γcom` must be mode-independent.
3. The semantic coarseness of §4.3 (`Follows` without name dependencies) is harmless but surprising.
   Record it in `notes/fs-semantics-v2.md` as an observation, not a change. Strengthening `Follows` with a
   per-name clause would be a trusted change and would make the discipline unnecessary only for
   `FsInit`, not for the per-name prefix.
4. `osCallPerm` threading: every library, and the pipeline goroutine, must hold a fraction, and the
   WAL's `Create` must collect all of it at its directory rename (plan §3 "Create needs a 'no other path
   call in flight' resource" is exactly `osCallPerm 1`).
5. Mode irreversibility: a program cannot mix legacy-specified and shared-specified libraries. This is
   the composition caveat above.

## Review and decisions (2026-11-13)

Independent review: `notes/wal-fsext-i2-review.md`, verdict READY WITH CHANGES (no soundness
counterexample; `closed_cut`'s paper argument holds). The coordinator's decisions (the user away):
- **M1 adopted**: the `os`-level shared specs (`os.Rename`, `os.Remove`, `os.OpenFile(O_CREATE)`, the
  multi-step calls with `EINTR` retries) are logically atomic (or crash-aware, as `LinuxFs/Spec/os/Crash.lean`),
  so a crash invariant holding half of a claim can update it at the step.
- **M2**: the claim that the server's purge is covered is withdrawn: purge's safety rests on OFD locks
  (`client/pkg/fileutil/purge.go:55-90`), which wait for the user's lock decision (plan §6 Q1).
- **M3 adopted**: a legacy-mode resource excluding shared resources; the full call permission minted at
  the mode switch; the shared invariant in the directory-sync spec; the crash fact's kept set under its
  quantifier.
- **M4**: a directory rename needs the whole call permission; in a composed program the boot sequence
  holds it (WAL `Create`, `cleanupWAL`, `renameWALUnlock` run before other libraries start) and splits it
  after; a gate for C6 (recorded in the plan).
- **Minors adopted**: reuse I1's `osCommitLb`/`crashCommit` (add the shared form); the mode switch at any
  extension step; blind directory reads with no claim; no-effect failure specs; `os.RemoveAll`'s
  `unlinkat`/`openat` (the trusted-model drafts model it by path over the extension's steps, or report it);
  the per-slot crash rule revisited; a rendezvous channel spec for the pipeline's `N.tmp` hand-off.

## Implementation log

Branch `wal-i2` (off `wal-int`). Modules, FS/ = `GooseLang/Ext/Fs/`:

- `TreeCut.lean` (pure defs): `MetaOp.slots`, `MetaOp.Writes` (slots, and every name of the
  directory a `mkdir` makes), `MetaOp.IsDirOp`, `Starts`, `PerSlotSeq`, `DirOpExcl log s0`,
  `OpOk`, `LogValid T0 log s0`, `prefTree`, `lastKept`, `slotAfter`.
- `TreeCutProof.lean`: **`closed_cut` proved** (no `sorry`).
- `NamesGhost.lean` (pure): `NameSet` (with `inter`/`diff`/`Same`), `NamesH`, `restrictN`,
  `NamesH.valAfter`, `Claim`, `RegionCrashed`, `DirPhS`.
- `CrashRegion.lean`: **`regionCrashed_of_cut` proved**: a closed `S` with the commit bound and
  `closed_cut`'s slots gives `RegionCrashed` for every list of claims whose histories are the log's.
- `TreeShared.lean`: the API: resources (`osNames`, `osCallPerm`, `osCallS`, `osLogLb`,
  `osLogEnt`, `osDirFdS`, `osSpine`/`osPathS`, `osSharedInv`, `osLogged`, `osNamesAfter`), the
  claims as a function of the history (`namesOf`, m7), `NamesCoh`, laws, `wp_osShare` (the switch as
  a combinator around any extension step, m2), `wp_osCallBeginS`, every FS-level shared spec, and
  `crashRest_region`/`crashRest_treeS`. **All `sorry`.**
- `Ghost.lean`: `OsGS` gains `γs γdfS γcS γperm γn γlen γlog`, allocated (empty) in `os_local_init`;
  nothing else changed yet.

Deviations from the design:

1. **Directory operations need the whole call permission** (`mkdir`, `rmdir`, a directory's rename,
   a rename replacing a directory): `wp_osMkdirS`/`wp_osRmdirS`/`wp_osRenameDirS` take
   `osCallS k s0 1`. The log discipline is `DirOpExcl`: such an entry began when it took effect
   and every later call began after it. This replaces the footprints `(J,*)` of §4.3 (and the
   `PerSlotSeq` of directory operations): a kept directory operation keeps everything before it, a
   dropped one drops everything after, so the replay's directory structure is one of the run's trees
   (`T a`, `a` past the last kept directory operation) and only file operations need the per-slot
   argument. It is the §5 risk-1 fallback, strengthened, and costs the WAL nothing (its `MkdirAll`,
   `Rename(tmp, dir)`, `RemoveAll` run in `Create`/`cleanupWAL` at boot, M4). A server whose
   libraries `mkdir` concurrently at run time would need the footprints back.
2. **`DirOpExcl log s0` and `LogValid T0 log s0` exempt the legacy prefix** (`x < s0`, the log's
   length at the switch): the legacy log is `Sequential`, so its entries are exclusive, and its past
   operations' applicability (`OpOk`) is not recorded by the legacy invariant. `LogValid` (each file
   operation applicable to its tree, a create's inode new) is a new invariant fact of the shared mode.
3. **`closed_cut`'s conclusion**: `TreeWf` of the replay; each slot = `slotAfter` (right after its
   last kept writer); every named file named in some tree of the run (so in `files`, via
   `FsTreeWf.hist`); the replay's directory keys those of a tree of the run (for `nextIno`).
4. `osLogLb` is a `MonoNat` (`γlen`) and `osLogEnt` a persistent ghost-map element (`γlog`), not a
   `MonoList` (m7). The DirSync spec takes `osSharedInv` (M3). Claims are keyed by `(j, N)` with
   `N` a list-based `NameSet`; `osNames_rekey` changes a key to another of the same names (m3).
5. A blind read (`wp_osDirReadNextBlind`) reads with the empty claim set `.only []` (m3).
6. Not yet stated: the `os`-level logically atomic specs (M1, `LinuxFs/Spec/os/`), the
   `O_TRUNC` open, the cross-directory rename's spine variant beyond `wp_osRenameFileS`.

Still to do, in order: the mode split (`treeCtx`'s shared branch with `TreeCohS` = `Starts`,
`PerSlotSeq`, `DirOpExcl _ s0`, `LogValid _ _ s0`, calls/dfds coherence; the legacy branch owning the
shared authorities and the whole `γperm` token, M3), `crashRest`'s shared branch and `osCrash_rel` via
`closed_cut`, the laws, the step specs, the `os` wrappers, the two-region test.

### Implementation log, second session (2026-11-13)

Done (no `sorry`): the mode split, the switch, `CallBegin`, the crash lemmas, some laws.

- `Ghost.lean`: `treeCtx := (treeLegacy ∨ treeShared) ∗ commitRes`. `treeLegacy` is the old body plus
  `legacyHolds` (the shared authorities empty, the log's length `0`, the whole `γperm` element: M3).
  `treeShared` holds the legacy history frozen and whole (`γd` auth + element 1, `γdf`/`γc` empty), the
  shared history's authority (the state's), `γdfS`/`γcS` and `callResS` (each call's permission
  fraction). `TreeCohS st s0 Γdf Γc`: `Starts`, `PerSlotSeq`, `DirOpExcl _ s0`, `LogValid _ _ s0`,
  `s0 ≤ len`, dfds/calls mirrored, `PhOkS` (a shared read's bits are the state's while nothing from
  `r0` on wrote a name of `N`), `callsLe`, `whole` (a call holding all of the permission began now),
  `after` (every call began after every directory operation and every legacy entry).
- `World.lean`: `wp_fs_stepT` takes a legacy resource `W` with `LegacyWit W` (`legacyWit_tree`,
  `_call`, `_dirFd`; `treeCtx_legacy`): **its statement changed** (internal to FS/; 13 call sites
  edited, each passes its `osTree`/`osCall`/`osDirFd`; also `wp_fs_stepTC`). `wp_fs_stepM`: the
  mode-generic lifting, whose continuation may open invariants across the step (`E \ osN → ∅ → ...`).
- `CrashTok.lean`: `crashRest`'s `crashCommit` became `crashMode` = `(crashCommit ∗ γs auth empty) ∨
  crashShared` (the legacy history whole, the shared history's authority, the kept closed set with the
  commits and slots, `commitRes`). `os_local_crash` in the shared mode updates `γd` to the crashed tree
  (so `TreeCrashed V V'` holds trivially) and gets `FsInit` from `osCrash_relS` (`CrashFiles.lean`,
  via `closed_cut`). `crashRest_lb` gained the case split.
- New modules: `TreeSharedRes` (the resource definitions, moved out of `TreeShared`, names unchanged),
  `TreeSharedSwitch` (`wp_osShare'` via `wp_ext_acc`, `wp_osCallBeginS'`), `TreeSharedCrash`
  (`crashRest_region'`, `crashRest_treeS'`), `TreeSharedLaws` (`osNames_next'`). `TreeShared.lean`
  keeps every statement and proves them from these. `CrashRegion` now imports `TreeSharedRes`.
- The LinuxFs leaves (walfs, crashlog, bboltfs Results) build on the mode split (checked at
  `e4542a9983`).

Deviations (for the WAL invariant's author):

7. **`osNames_split` was unsound**: a split producing an empty part gives the key `.only []`; two
   such splits gave two whole elements of one ghost-map key, so `False`. Fixed by a definition
   change, not a statement change: `osNames j (.only []) dq h := ⌜h = NamesH.empty⌝` (the claim on no
   name is no resource; `namesOf V j (.only []) = NamesH.empty`). Laws: `osNames_of_ne`,
   `osNames_except`, `osNames_auth`.
8. **`wp_osMkdirS`'s post named an auto-bound `o`** (`⟨∅, [(x, o, ∅)], ∅⟩`, i.e. any entry: unprovable).
   Now `(⟨.mkdir j b J, s0⟩ : LogEntry)`. `autoImplicit` is off in the `TreeShared*` modules.
9. **`osPathS_frac` is unprovable as stated** (right to left needs one split of the path among the
   roots, which needs `RootsOk R`; `osPathS` does not record it). Proposed: add `RootsOk R` to
   `osPathS`'s pure part and a law `osPathS_root` (from `osSharedInv`); not done yet.

Still `sorry`: `osNames_split`/`merge`/`rekey`, `osPathS_frac`/`child`, every extension-level step spec
(Unlink, Rename ×4, Mkdir, Rmdir ×2, LstatDir, OpenCreate, OpenDir, DirSync, DirClose, FdKind,
DirReadNext, blind DirReadNext), the `os`-level logically atomic specs, the two-region test.

### Implementation log, third session (2026-11-13)

Done (no `sorry`), each statement in `TreeShared.lean` unchanged and proved from a new module:

- `TreeSharedClaims`: `osNames_split`/`merge`/`rekey` (through `CohEx`, the claims' coherence with
  some names of one directory unclaimed: `osNames_del` gives a whole claim back to the authority,
  `osNames_ins` claims unclaimed names; `namesOf_restrict`, `namesOf_congr`, `namesOf_next_union`);
  `osPathS_frac`/`child`; the new laws `osPathS_root` (a root of `R` is a path, from the shared
  invariant) and `osPathS_rootsOk`. `osNames_frac`/`agree` moved here (statements unchanged).
- `TreeSharedDirFd`: `wp_osFdKindDirS`, `wp_osDirCloseS`, `wp_osDirSyncS`.
- `TreeSharedStep`: `osNames_entry` (a claim's names hold in the state what it knows),
  `osSpine_walk`, `osPathS_lookup` (a spine names its directory in the state), `wp_callEndS` (a
  step that only ends its call, given the state facts the caller's resources give).
- `TreeSharedCallEnd`: `wp_osLstatDirS`, `wp_osUnlinkS_none`, `wp_osRmdirS_none`,
  `wp_osRenameAbsentS` (over `wp_callEndS`).
- `TreeSharedOpenDir`: `wp_osOpenDirS`.

Deviation:

10. **Proposal 9 adopted** (coordinator's decision): `osPathS` records `RootsOk R` in its pure part
    (`TreeSharedRes.lean`), so two spines of one path agree (`root_split_unique`); new law
    `osPathS_root`.

Found, for the next session (not yet done):

11. **`PhOkS` needs `∀ b, s b = true → NameOk b`** (a shared read's seen names are valid). Without
    it `wp_osDirReadNextBlind`'s `NameOk b`, and `wp_osDirReadNextS`'s for a name outside `N`, are
    unprovable: after an entry touches the directory, `PhOkS` says nothing of the bits, and `note`
    adds `o.adds` names to `s`. The fix is a definition change in `Ghost.lean` (`PhOkS`'s reading
    case gains the clause; `PhOkS.congr` and the step lemmas keep it: `o.adds` names are entries of
    the new tree, valid by `FsTreeWf`), which rebuilds everything above `Ghost.lean`.
12. **`NamesCoh` needs "every claimed directory is a directory of the tree"** (`∀ j N h, Γn !! (j,
    N) = some h → j ∈ V.now`) for `wp_osMkdirS`: the new directory's claim `(J, .except [])` is
    inserted, which needs the key free; nothing records that no stale key on a fresh inode exists.
    True of every map built so far (`claimsInit`, split/merge/rekey on an existing key; removed
    directories stay in the tree). A definition change in `TreeSharedRes.lean`; `CohEx` and
    `namesCoh_init` gain the clause.
13. **The logging steps** (`Unlink`, the three file `Rename`s, `OpenCreate`; then `Mkdir`, `Rmdir`,
    the directory `Rename`) want one generic lemma, `wp_logStepS`, as `wp_callEndS` is for the
    no-effect ones: the step logs `e = ⟨o, s0⟩` at `x = |log|` (or only ends the call); its
    obligations are (a) `FsTreeWf` of the new state (the legacy `fsTreeWf_meta` and the
    `named_*`/`mem_*` lemmas of `TreeSpecsMeta`); (b) `TreeCohS`: `Starts` from `callsLe`,
    `PerSlotSeq` from the presented claims (`h.next ≤ s0`, every earlier writer of a claimed slot in
    `h.ents`), `DirOpExcl` from `after`, `LogValid` (`OpOk` from the claims' `cur`; a create's inode
    is `nextIno`, named nowhere by `FsTreeWf.hist`), `whole` for the other calls (no other call holds
    all of the permission while this one holds `q > 0`: two `γperm` elements of `callResS`), `ph`
    (with 11: an entry writing a name of `N` falsifies the hypothesis for good; one that does not
    leaves `N`'s bits, `note`); (c) the ghost updates: `γs` (auth and the invariant's element),
    `γlen` (auth, `osLogLb (x+1)`), `γlog` (`logMap (log ++ [e]) = <[x := e]> (logMap log)`), and
    the presented whole claims to `h.log x e (restrictN N cur')`, every other claim unchanged
    (`namesOf V' j N = namesOf V j N` when `e` writes no name of `N` in `j`: `prefTree` of a
    longer log agrees below its length, and `MetaOp.apply` leaves unwritten slots).

Still `sorry` in `TreeShared.lean`: `wp_osUnlinkS`, `wp_osRenameFileS`, `wp_osRenameFileS1`,
`wp_osRenameDirS`, `wp_osMkdirS`, `wp_osRmdirS`, `wp_osOpenCreateS` (13), `wp_osDirReadNextS`,
`wp_osDirReadNextBlind` (11). Not begun: the `os`-level logically atomic specs (M1), the two-region
test.

### Implementation log, fourth session (2026-11-13)

Done (no `sorry`), each `TreeShared.lean` statement proved from a new module unless noted:

- Notes 11 and 12 adopted (definition changes). `PhOkS` (`Ghost.lean`): a shared read's case gains
  `∀ b, s b = true → NameOk b`. `NamesCoh` (`TreeSharedRes.lean`) gains `dirs` (every claimed
  key's directory is in `V.now`); `CohEx` gains `dirs` and `udir` (an unclaimed name's directory is
  in the tree); `namesCoh_init` and the split/merge/rekey proofs carry them. The LinuxFs leaves
  (walfs, crashlog, bboltfs Results) rebuilt on the change.
- `TreeSharedLog`: **`wp_logStepS`**, the generic logging step (note 13). A step of the call `k`
  that ends it (no effect) or logs `o` (`LoggedFrom st st' k s0 o`: the files as they were, the
  next inode perhaps taken), with whole claims `cl : List ClaimW` (directory, names, history, the
  names' entries after the step). Obligations: every claim written, every slot of `o` in a claim,
  `h.next ≤ s0 ∨ q = 1`, `IsDirOp → q = 1`, added names valid, and (per state, from `F` through
  `P` and `ClaimsAt`) the tree after `o` well formed, naming no new file, its directories the old
  ones and `o.newDirs` (fresh), `OpOk` for a file operation, the claims' entries after `o` as given.
  `hprog`/`hpost` also get the sole-call fact (`q = 1 → every call in flight is k`), which a
  directory rename's step needs. Post: the claims unchanged, or `osLogged x ⟨o,s0⟩`, each claim
  `h.log x ⟨o,s0⟩ cur'`, and for a `mkdir` the new directory's claim with `cur = ∅`,
  `next = x + 1`. Pure parts: `namesOf_snoc_written`/`_other`, `treeCohS_log` (the shared
  coherence after a logged entry: `Starts`, `PerSlotSeq` from the claims, `DirOpExcl` from `after`
  and `whole`, `LogValid`, `PhOkS` through `note` with note 11), `namesCoh_log`, `callResS_excl`
  (two calls' permission fractions: neither is whole).
- `TreeSharedMeta`: `wp_osUnlinkS`, `wp_osRenameFileS` (two claims), `wp_osRenameFileS1`,
  `wp_osRenameDirS` (both over `wp_osRename1S`, a rename within one claim), `wp_osRmdirS` (the
  emptied directory's claim passed through `F`).
- `TreeSharedRead`: `wp_dirReadS` (the generic step of a shared read: per outcome a new phase
  keeping `PhOkS`) and `wp_osDirReadNextBlind`.

Definition and statement changes:

14. `ClaimsAt` (new, `TreeSharedLog`) is what a logging step's obligations get of the claims:
    their entries, nothing outside their names in `cur`, and two claims of one directory under
    distinct keys disjoint (the last makes `wp_osRenameFileS`'s `s ≠ t` provable: the
    semantics' `s = t` rename succeeds with no effect, which the two-claim post excludes).
15. **`wp_osDirReadNextBlind` takes `osSharedInv R` and `↑osShN ⊆ E`** (statement change; it had
    neither). The generic read step opens the shared invariant; every shared client holds it.
16. **`wp_osMkdirS`'s post is unprovable as stated**: the new directory's claim
    `⟨∅, [(x, e, ∅)], ∅⟩` asserts its `ents` has exactly one entry, but nothing records that no
    earlier log entry has a slot on the fresh inode (`LogValid` covers file operations from `s0`
    only; a legacy entry or a directory operation is unconstrained). Proposed: the post gives
    `∃ hJ, osNames J (.except []) 1 hJ ∗ ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝` (what `wp_logStepS`
    proves; what a client needs: empty, and no later call conflicts). Not yet changed.
17. **`Mkdir` and `OpenCreate` need `wp_logStepS` generalised over the step's next inode**: their
    entry (`mkdir j b J`, `create j b i`) names `st.fs.nextIno`, which the logic does not track, so
    `o` and the claims' new entries cannot be fixed before the step. Plan: `o : Nat → MetaOp` and
    `cur' : Nat → Ents`, instantiated at `st.fs.nextIno` (inside the proof, `generalize` the
    application before the `mkdir` case split), the post `∃ x n`; the current statement a
    corollary with constant functions. `OpenCreate` also changes the files' world (a new file and
    fd: not `FilesSame`), so it needs the legacy open's world update (`TreeSpecsOpen`) as well.

Still `sorry` in `TreeShared.lean`: `wp_osMkdirS` (16, 17), `wp_osOpenCreateS` (17),
`wp_osDirReadNextS` (over `wp_dirReadS`; needs a pure `WN n` of the log's length in the generic
post, for the fresh read's `h.next ≤ r0'`, and the claim's `h = namesOf` to show nothing wrote `N`
since `r0`). Not begun: the `os`-level logically atomic specs (M1), the two-region test.

### Implementation log, fifth session (2026-11-13)

Done (no `sorry`): every statement of `TreeShared.lean` is now proved (its header says so).

- `TreeSharedLog`: **`wp_logStepSW`**, the general logging step, and two corollaries.
  `wp_logStepSN` is note 17: the operation `oF n` and the claims' new entries `curF n` are
  functions of the step's fresh inode `n` (the state's `nextIno`; inside the proof `generalize`d
  after the state is known, the post `∃ n x`). `wp_logStepS` is the old statement, `wp_logStepSN`
  with constant functions (its callers in `TreeSharedMeta` unchanged). `wp_logStepSW` adds a
  change of the files' world: `hworld` (the caller's update of `osWorld` from the step's
  `HeapRendered`/`MapsFresh`, giving `G n w logged` to the post), and `hpost` returns `EndedT`
  (the call ended, as the tree sees it: the fds may have changed) or `LoggedT` (`LoggedFrom`
  without `FilesSame`) with `FsTreeWf` of the new state, which the caller now proves. Its `htree`
  dropped the `TreeWf`/"names no new file" conjuncts (only `FsTreeWf` needed them, now the
  caller's) and takes the step and `LoggedT` (an `open(O_CREAT)` of an existing file is not
  logged, and `OpOk` of its `create` is false).
- `TreeSharedMeta`: **`wp_osMkdirS'`** over `wp_logStepSN` (claim entries `<[b := .dir n]> h.cur`;
  `ClaimsAt.out` makes the restriction drop).
- `TreeSharedRead`: **`wp_osDirReadNextS'`**. `wp_dirReadS` gained a pure fact `WN n` of the log's
  length in its post (`hwn`, from `Q`); the blind read passes `True`. With `Q st := h = namesOf ..`
  (`osNames_auth`): a fresh read's `r0' = n` and `h.next ≤ n` (`namesOf_next_le`); a resumed read
  sees no write of `N` since `r0` (`noWrite_of_next`, from `lt_namesOf_next` and `h.next ≤ r0`), so
  `PhOkS`'s clause applies; the end needs a claimed entry's name valid (`present_of_entry`, from
  `TreeWf`).
- `TreeSharedCreate` (new): **`wp_osOpenCreateS'`** over `wp_logStepSW`. `openCreateStep_cases`
  classifies the step (no effect; the file there opened; a file created, with or without its fd),
  used by `hpost`, `hworld` and `htree`. `fsTreeWf_created` (the legacy `create_facts`' tree part
  with directory fds, which a create only notes), `fsTreeWf_addFd`, `osWorld_created` (the new
  file's `OsMeta` minted, the heap unchanged; then `osWorld_filesSame` or `osWorld_addFd`).
  The gift `ocGift`/`ocFd`: created (logged) `osMeta n ∗` maybe the fd; not logged, the file there
  and maybe its fd, or a failure.
- `TreeSharedTest` (new): **the two-region test**. `twoRegion_par`: two claims (`b1`, `b2`) of one
  directory, each with its own call and a spine fraction, give two separate WPs of
  `open(O_CREAT)` (what forking the two threads needs). `twoRegion_crash`: a region whose create is
  logged below the commit bound concludes from `crashRest_region` (with both claims, the other's
  history arbitrary) that its file is in the crashed tree (`valAfter_last`).

Statement changes:

18. **Note 16 adopted**: `wp_osMkdirS`'s post gives the new directory's claim as
    `∃ hJ, osNames J (.except []) 1 hJ ∗ ⌜hJ.cur = ∅ ∧ hJ.next = x + 1⌝`.
19. `wp_dirReadS` (internal to FS/) takes `WN`/`hwn`; `wp_logStepSW` is new, `wp_logStepSN` and
    `wp_logStepS` keep their statements as corollaries. No other `TreeShared.lean` statement changed.

Not begun: the `os`-level logically atomic specs (M1; another agent, `LinuxFs/`).

Coordinator additions (for the `os` layer, branch `wal-osau`):

20. **`wp_osOpenFileS`** (new, `TreeShared.lean`, proof `wp_osOpenFileS'` in `TreeSharedCreate`):
    `open(2)` of a name holding a file, without `O_TRUNC` (any access mode, with or without
    `O_CREAT`), with a fraction of a claim whose `N` contains the name; logs nothing (over
    `wp_fs_stepM` directly, as `wp_osOpenDirS`); the fd is `openFd i fl`. The statement is the one
    `wal-osau` had with `sorry` in `LinuxFs/Proof/os/SharedExt.lean` (that copy can go).
21. **`wp_osOpenCreateS` takes the flags** (statement change): `fl` with `OpenFlagsOk fl.toNat`,
    `O_CREAT` set, `O_TRUNC` clear, in place of the fixed `flCreat`; the fds it gives are
    `openFd i fl` (the WAL creates with `O_WRONLY|O_CREATE`). `openCreateStep_cases`, `ocFd`,
    `ocGift` take `fl`; the two-region test passes `flCreat`.
