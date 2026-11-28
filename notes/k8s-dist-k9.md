# k8s-dist K9: `SharedModel`'s Go code against K4's Lean model (scope, 2026-11-28)

Stage K9 of `notes/k8s-dist-lean-plan.md` (§3, §4). Branch `k8s-dist-k9/2026-11-28`, off
`k8s-dist-k4/2026-11-27` (`2a71df1164`, queued for lean). K4 proved `fullComplete : FullComplete`
(`Proof/.../examples/k8s/dist/SharedSearch.lean`): every run of the semantic model (`SRun`) is a run of
the full mode's search (`SearchRun A`), for anchors `A` naming every revision the history shows
(`AnchorsOk`). K9 proves that the Go search (`examples/k8s/etcd3/export.go`) computes that search, so
that `CheckShared` (`examples/k8s/dist/store.go:205`) never answers `Illegal` on a history that
linearizes in the semantic model.

## 0. What K9 delivers, and what it does not

- **Completeness (what `Robust` needs).** `RunStore` panics only on `CheckShared`'s `Illegal`, which only
  the full mode returns (the loop runs Lazy, Eager, Full and stops at Full). So the theorem needs: if the
  history (in some real-time-consistent order) is an `SRun` from the seeded store, the full mode's
  porcupine model accepts it. Chain: K8 gives the `SRun`; `fullComplete` gives a `SearchRun A`; K9's
  `searchRun_accepts` (§2.9) gives that the full mode's sequential model accepts the same sequence;
  porcupine's proved spec (`Spec/github_com/anishathalye/porcupine/CheckOperationsTimeout.lean`) then
  excludes `Illegal`.
- **Soundness of an `Ok`** (each mode's search only explains a history the semantic model explains) is
  **not** needed for `Robust` and K4 did not prove it. K9's specs give, for free, the weaker "Ok ⇒ the
  history linearizes in the mode's own sequential model" (porcupine's spec). Proving the search sound
  against `SRun` would be a separate pure stage; not planned.

## 1. The functions (`export.go`, 987 lines; `wc` of each body)

"Similar" = the in-process driver's proved function (`Proof/.../examples/k8s/etcd3/<fn>.lean`) that
the new one copies or wraps.

| Function | Lines | Similar (proved) | Spec (§2) | Notes |
|---|---|---|---|---|
| `SharedModel` (Init/Step/Equal closures) | 50 | `Model` (`Model.lean`: the closure pattern, `isModel_of_step`) | §2.1 | the hub |
| `settle` | 46 | `closure` (the driver's pending closure, worklist) | §2.2 | worklist over `cfgSet` |
| `cfgSet.add`, `pendEqual` | 17 + 14 | `configEqual`, `inputEqual`, `storeEqual` | §2.3 | dedup |
| `histHashes.intern`, `canonical`, `canonLocked` | 18 + 6 + 13 | none (new: hash-consing under `hh.mu`) | §2.3 | |
| `mix`, `strHash`, `storeHash` | 6 + 9 + 34 | none | returns some `w64` | arithmetic only |
| `histHashes.skipTo` | 29 | `advance`, `appendHist` | §2.4 | the `gaps` cache |
| `target` | 61 | none; `targetL` is its Lean (K4-7 checked line by line) | §2.5 | |
| `bound`, `landings`, `shows` | 28 + 34 + 56 | none | §2.5 | `sort.Search` (Perennial spec) |
| `stepIdx` + memo | 18 | `step` (`step.lean`) | §2.6 | memo: G11 |
| `watchOkIdx`, `watchListOkIdx`, `initialPrefixOkIdx`, `reliableOkIdx`, `wantEventsIdx` | 26+19+19+16+19 | `watchOk`, `watchListOk`, `initialPrefixOk`, `reliableOk`, `wantEvents` (line for line) | §2.6 | `histAt` through `hview` |
| `viewFrom`, `hview.at` | 16 + 8 | `histAt` | §2.6 | |
| `HistoryRevs` | 87 | none | §2.7 | maps, `sort.Slice` (G13) |
| `rvOfMsg`, `decodeItemRVs` | 14 + 25 | `decodeObj`, `parseRV`, `preMsg` | §2.7 | round-trip lemmas |
| `SeedShared` | 22 | `seed`, `seedOne` | §2.8 | its `cli.Put` half is K8/K12's |
| `Floor`, `NoForeign`, `PastRead`, `PinnedRead` | 9 + 20 + 17 + 6 | `pastRead`, `failureFree` | §2.8 | used by `RunStore` (K8, K12) |
| `CheckShared` (`dist/store.go`) | 8 | `realCheck`'s call of porcupine | §2.9 | |

About 700 Go lines. Out of K9: the thin exported wrappers of driver functions (`Model`, `NewCache`,
`RealCheck`, `FailureFree`, `NewStoreOnly`, `IsWrite`, `Rejections`, `SetFeatures`: each one call of a
proved function, K12's), `Serve`/`Record` (K10, `Apply` split), `SeededAt`/`SeedRevs`/`Encode*`/
`AcceptAll`/`CrossCheckWatches` (tests only).

### Go changes K9 needs (a Go session; none changes a proved function)

- **G11 (needed).** `SharedModel`'s `memo map[wkey]bool` is read and written by `stepIdx` with no lock.
  porcupine's `stepSpec` (`Proof/github_com/anishathalye/porcupine/Defs.lean:111`) is a persistent
  triple (the checker may call `Step` from several goroutines), so the closure's captured state can only
  be shared through an invariant, and a plain map's operations are not atomic. Fix: a
  `type wmemo struct { mu sync.Mutex; m map[wkey]bool }`, `stepIdx` locking around the lookup and around
  the store (not around `watchOkIdx`). `histHashes` is unchanged (it already locks `hh.mu`).
- **G12 (needed).** `stepIdx` reads the package variable `crossCheck` (and panics on a mismatch). Move the
  cross-check to the test (`TestReplayHistory` can call `watchOk` and `watchOkIdx` through an
  `export_test.go` wrapper) so that the program code reads no mutable package variable. (Alternative:
  keep it and have the package's `Init` freeze `crossCheck ↦□ false`, leaving `CrossCheckWatches`
  unverifiable; worse.)
- **G13 (needed).** `HistoryRevs` sorts with `sort.Slice` (reflectlite's swapper: no spec at Perennial
  `148615524`). Use `slices.Sort` on the `[]uint64`s (`Spec/slices/Sort.lean`, `[]uint64`). `sort.Search`
  in `landings` has Perennial's proof (`Perennial/Proof/sort/Search.lean`) and stays.

Then `etc/goose.py --project k8s-apiserver` re-translates.

## 2. The specs (Lean drafts)

Abstract values: `GCfg`, `HSt`, `GSt` and `cfgOwn` (`MDefs.lean`); `stepL`, `kstepL`, `mstepL`,
`watchOkL` (the driver's); `skipToL`, `targetL`, `landingsFull`, `SettleL`, `SearchRun` (K4's). All
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/<fn>.lean`, the shared definitions in a defs
module `Proof/.../examples/k8s/etcd3/SharedDefs.lean` (imports `MDefs` and `k8s/dist/SharedSearch`).

### 2.0 Well-formed configurations

```lean
/-- A configuration the search holds: the history one store per revision, its last the store. -/
def HWf (h : HSt) : Prop := h.hist.length = uint.nat h.st.rv ∧ h.hist.getLast? = some h.st
```

`HWf` is preserved by `foreignL`, `advanceL` and `kstepL`; `skipToL`'s Go needs it (the `gaps` cache
is keyed by the history only, the appended stores' items are taken from the configuration's store,
which `HWf` makes the history's last). Every revision the search reaches is below `2^63` (ioOk, §2.1),
so `make`s of `n - lo + 1` (`viewFrom`) and `a + 1` (`landings`) do not overflow.

### 2.1 `SharedModel` (the hub)

```lean
structure RevsL where
  anchors : List w64          -- sorted, nonzero
  byKey : GoString → List w64
  fastByKey : GoString → List w64

/-- Go's `landings` (exact, as a list). -/
def landingsL (R : RevsL) (rv : w64) (w : Input) (b : w64) (full : Bool) (x : Input) (y : Output) : List Nat

/-- Go's `settle`: `SettleL` with `landingsL` (and `bound`'s `b`). -/
inductive GoSettle (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output) : GCfg → GCfg → Prop
  | refl | drop … | land (i l) : … → l ∈ landingsL R c.st.st.rv (pendAt c i) b full x y → …

/-- One step of mode `mode` from `c` (Go's `Step`, per configuration). -/
def GoStep (R : RevsL) (mode : Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg) : Prop :=
  let lazy := stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x y
  if mode = 0 ∧ lazy ≠ [] then e ∈ lazy
  else ∃ d, GoSettle R (boundL x y) (mode = 2) x y c d ∧
    e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y

/-- The sequential model: a set of configurations; a step fails when no configuration survives. -/
def sharedM (g0 : HSt) (R : RevsL) (mode : Nat) : SeqModel (Set GCfg) OpV where
  init := {⟨g0, []⟩}
  step S io := match decOp io with
    | none => none
    | some (x, y) => let S' := {e | ∃ c ∈ S, GoStep R mode c x y e}
                     if S'.Nonempty then some S' else none

/-- `rep k v S`: `v` is a `state` whose configurations are exactly `S` (duplicates allowed),
each well-formed and `Bounded` (as `stRepB`). -/
def sharedRep (g0 : HSt) (n : Nat) (v : GoInterface) (S : Set GCfg) : IProp GF :=
  iprop(∃ sl cs gs, ⌜v = boxSt sl ∧ (∀ g, g ∈ S ↔ g ∈ gs) ∧ ∀ g ∈ gs, HWf g.st ∧ Bounded n g⌝ ∗
    sl ↦*□ cs ∗ [∗list] c;g ∈ cs;gs, cfgOwn c g)

def sharedS (g0 : HSt) (R : RevsL) (mode : Nat) : ModelSpec GF (Set GCfg) where
  M := sharedM g0 R mode
  rep k := sharedRep g0 (k + …)
  ioOk i o := iprop(∃ x y, ⌜i = boxIn x ∧ o = boxOut y ∧ RevsBelow (2^63) x y ∧ GenInA x⌝)

abbrev Seeded__SharedModel.spec : Prop :=
  ∀ (s : Seeded) (g0 : HSt) (r : Revs) (R : RevsL) (mode : w64),
  {{ isPkgInit … ∗ seededOwn s g0 ∗ revsOwn r R ∗ ⌜HWf g0 ∧ uint.nat mode ≤ 2 ∧ bounds g0⌝ }}
    Seeded.SharedModel #s #r #mode
  {{ (m : Model), RET #m; ⌜m.Partition' = func.nil ∧ m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗
      initSpec (sharedS g0 R (uint.nat mode)) m.Init' ∗ stepSpec (sharedS g0 R (uint.nat mode)) m.Step' ∗
      isEqHash (sharedS g0 R (uint.nat mode)) m }}
```

`RevsBelow` (every revision the input or output names below `2^63`: true of etcd's `int64` revisions;
discharged in K10 at the codec) and `GenInA` (the generator's inputs: `PreRV` of length 0 or 8, which
`rvOfMsg` needs, §2.7) are the premises the history must give. `Equal`'s spec needs only "one pointer ⇒
one history" (`histOwn` is persistent: `histOwn h hs ∗ histOwn h hs' ⊢ ⌜hs = hs'⌝`), not canonicity:
hash-consing is for speed and the specs never rely on it.

### 2.2 `settle`

```lean
abbrev settle.spec : Prop :=
  ∀ hh r R c g b full x y,
  {{ isPkgInit … ∗ hhOwn hh ∗ revsOwn r R ∗ cfgOwn c g ∗ ⌜HWf g.st ∧ RevsBelow (2^63) x y ∧ bounds g⌝ }}
    settle #hh #r #c #b #full #x #y
  {{ sl cs gs, RET #sl; sl ↦*□ cs ∗ ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗
      ⌜(∀ e, e ∈ gs ↔ GoSettle R b full x y g e) ∧ ∀ e ∈ gs, HWf e.st ∧ bounds e⌝ }}
```

Loop invariant of the worklist: every element of `set.list ++ work` is `GoSettle`-reachable from `c`;
`c ∈ set.list ++ work`; every element of `set.list` has its `GoSettle` successors in `set.list ++ work`.
`cfgSet.add` returning `false` means an equal configuration is in the list (one history pointer, equal
store, equal pending list), so dropping it keeps the invariant; duplicates it lets through do no harm.

### 2.3 Hash-consing (`hhOwn`), `intern`, `canonLocked`, `canonical`, `cfgSet.add`

```lean
/-- `hh`'s lock, and under it: every node in `is` and in `canon` is a history node with some history
(persistent), `canon[k]`'s nodes have `k`'s `prev` and `n`; `gaps[base][i]` is `base`'s history with
`i + 1` foreign stores appended. -/
def hhOwn (hh : Loc) : IProp GF := ∃ γ, is_lock γ (hh.mu) (hhInv hh)

abbrev histHashes__intern.spec : ∀ hh prev hs st s n,
  {{ hhInv-fields owned ∗ histOwn prev hs ∗ storeOwn st s ∗ ⌜uint.nat n = hs.length + 1⌝ }}
    hh.intern prev st n
  {{ c, RET #c; hhInv-fields owned ∗ histOwn c (hs ++ [s]) }}
abbrev histHashes__canonLocked.spec : … histOwn h hs … {{ n, RET #n; … histOwn n hs }}
abbrev histHashes__canonical.spec : {{ hhOwn hh ∗ histOwn h hs }} … {{ n, RET #n; histOwn n hs }}
abbrev cfgSet__add.spec : {{ cfgSetOwn s gs ∗ cfgOwn c g }} s.add c
  {{ b, RET #b; cfgSetOwn s gs' ∗ ⌜b = false → g ∈ gs ∧ gs' = gs⌝ ∗ ⌜b = true → gs' = gs ++ [g]⌝ }}
```

(`intern`/`canonLocked` hold `hh.mu`: their specs take the invariant's contents, `canonical` the lock.)

### 2.4 `skipTo`

```lean
abbrev histHashes__skipTo.spec : ∀ hh c g t,
  {{ hhOwn hh ∗ cfgOwn c g ∗ ⌜HWf g.st ∧ uint.nat t < 2 ^ 63⌝ }} hh.skipTo #c #t
  {{ c', RET #c'; cfgOwn c' ⟨skipToL g.st (uint.nat t), g.pend⟩ }}
```

`HWf` gives a non-nil history (`rv ≥ 1`: the seeded store's revision is at least 2) and that the cached
gap stores' items are the configuration's.

### 2.5 `target`, `bound`, `landings`, `shows`

Exact: `target` returns `targetL x y rv` (as `w64`, all values below `2^63`), `bound` `boundL x y`,
`shows` `showsL x y key r`, `landings` `landingsL R rv w b full x y` (a list of `w64`; with `sort.Search`
on the sorted `anchors`). `targetL` is K4's; `boundL`, `showsL`, `landingsL` are new Lean functions,
read off the Go.

### 2.6 `stepIdx`, the `*Idx` watch checks, `viewFrom`, `hview.at`

`stepIdx` has `step`'s spec (`step.lean`: `r ↦* cs ∗ [∗list] c';g' ∈ cs; stepL g x (plainOut y), cfgOwn
c' g'`) plus `memoOwn m` (G11's lock; invariant: `m[k] = v → v = watchOkL k.in ⟨k.evs, k.fail⟩ H(k.hist)`,
`H` the history `histOwn` gives the pointer; `watchOk` reads only `WFailed` and `WEvents` of the output and
only the history and revision of the configuration). Each `*Idx` has its counterpart's spec; the one new
lemma: `viewFrom h lo`'s `at r` is `histAt h r` (every revision has its node, `HWf`).

### 2.7 `HistoryRevs`, `rvOfMsg`, `decodeItemRVs`

```lean
abbrev HistoryRevs.spec : Prop :=
  ∀ (sl : GoSlice) (ops : List Operation) (xs : List (Input × Output)),
  {{ isPkgInit … ∗ sl ↦*□ ops ∗ ⌜OpsAre ops xs ∧ ∀ p ∈ xs, GenInA p.1⌝ }}
    HistoryRevs #sl
  {{ (r : Revs) (R : RevsL), RET #r; revsOwn r R ∗
      ⌜R.anchors.Pairwise (· < ·) ∧ (∀ a ∈ R.anchors, a ≠ 0) ∧ AnchorsOk (0 :: R.anchors.map uint.nat) xs⌝ }}
```

(`OpsAre`: each operation's input and output are `boxIn x`, `boxOut y`.) Lemmas: `rvOfMsg (preMsgL x o)
= o.ResourceVersion` in the RV branch when `x.PreRV` has length 0 or 8 (the pattern has no comma and is
longer than 8, so its first occurrence is the object's); `decodeItemRVs (encItemsL os)` gives `os`'
keys and revisions (the `encodeItems`/`decodeObj` round trip).

### 2.8 `SeedShared`, `NoForeign`, `PastRead`, `PinnedRead`, `Floor`

`SeedShared`'s pure half: the returned `Seeded` holds `g0` with `HWf g0`, its items' revisions at most
`g0.st.rv`, `g0.st.rv ≥ 2` (`FullComplete`'s two seed premises); the `cli.Put` half (which revisions
the cluster gives) is K8's dist client spec. `NoForeign`, `PastRead`, `PinnedRead`, `Floor`: exact Lean
functions, consumed by K8 (`NoForeign ⇒` the in-process `realCheck` argument) and K12.

### 2.9 `CheckShared` and the result

```lean
/-- K9's theorem (pure, linking `fullComplete`): every `SRun` from the seeded store is accepted by the
full mode's sequential model, in the same order. -/
theorem searchRun_accepts (g0 : HSt) (R : RevsL) (xs : List (Input × Output)) (c' : GCfg) :
    HWf g0 → SeedItemsLe g0 → R.anchors.Pairwise (· < ·) →
    AnchorsOk (0 :: R.anchors.map uint.nat) xs → (∀ p ∈ xs, RevsBelow (2^63) p.1 p.2) →
    SRun g0 ⟨g0, []⟩ xs c' → ∃ S, (sharedM g0 R 2).run (xs.map encOp) = some S

abbrev CheckShared.spec : Prop :=
  ∀ s g0 r R ops xs timeout,
  {{ isPkgInit … ∗ seededOwn s g0 ∗ revsOwn r R ∗ sl ↦*□ ops ∗ ⌜OpsAre ops xs ∧ ioOk-premises ∧ HWf g0⌝ }}
    CheckShared #s #r #sl #timeout
  {{ res mode, RET (res, mode); ⌜res = Illegal → mode = Full ∧
       ¬ ∃ lin, porcupine.Linearizes (sharedM g0 R 2) (histOf ops) lin⌝ }}
```

`searchRun_accepts` uses `fullComplete` with `A = List.range (g0.st.rv + 1) ++ R.anchors`, and
`SettleL A ⊆ GoSettle R b true` along the run: a landing of `landingsFull A [] [] rv` is `rv + 1`, or an
anchor `a ≥ rv` or `a + 1` above `rv + 1`; the seed's revisions `a ≤ g0.st.rv ≤ rv` give only `rv + 1`
(the search's revision never decreases), and the others are Go's anchors (`a + 1 < 2^64` by
`SettleL.land`'s bound, below). The search's extra landings (`byKey`, the answer's own revision) only
add configurations. K12 composes: K8's `SRun` (in a real-time order) ⇒ `searchRun_accepts` ⇒ porcupine's
`CheckOperationsTimeout` spec ⇒ `CheckShared` is not `Illegal`.

## 3. K4-7's mismatch (`OpAnchors`) and a second one: both fixed in K4's Lean (K9-1, `361664181e`)

- **`OpAnchors`'s watch clause narrowed to `e.t < 4`** (was `e.t ≠ 4`). Recommendation and what was done:
  narrow, rather than show such operations never occur. Showing they never occur fails anyway: a
  *skipped* watch (`x.Skip`) with a bad event (type 5 or more) passes `watchOkL` (a skipped watch
  constrains nothing), so it can be in an `SRun`, and `OpAnchors` asked its revision while Go's
  `HistoryRevs` (`ev.Type < WError`, and `WBookmark` by `num`) does not anchor it. The proof used the
  clause once (`HRel.watchOk`, `SharedWatch.lean:579`), after `watchOkL` had excluded type 5 or more
  (`h5'`), so `e.t < 4` follows from `e.t ≠ 4 ∧ e.t < 5`: a one-line change. `FullComplete`'s premise
  is weaker, its statement stronger; not a top-level statement.
- **`SettleL.land` takes `l < 2 ^ 64`.** Go's `landings` adds `a + 1` in `uint64` (an anchor `2^64 - 1`
  wraps to 0 and is dropped), so a Lean landing at `2^64` would have no Go counterpart. K4's construction
  lands at `canonL ≤ R`, `R` the cluster's revision + 1 `< 2^64` (`NoWrap`): `by omega`.

Build of record: below ("Handoff K9-1").

## 4. Order, riskiest first, and estimate

1. **The hub: `hhOwn`, `intern`/`canonLocked`/`canonical`, `cfgSet.add`, `skipTo`, `settle`'s worklist,
   `SharedModel`'s closures and `sharedRep`.** New ghost structure (a lock invariant over three maps of
   pointers), the exact-set representation, the worklist closure invariant. If the set representation
   does not fit porcupine's `ModelSpec`, everything else moves. (1.5-2 sessions.)
2. **`stepIdx` + memo (after G11/G12), the `*Idx` watch checks, `viewFrom`.** Copies of proved proofs
   with `histAt` replaced by the view; `watchOk`'s proofs are long (several hundred lines each), so the
   risk is volume, not design. (1 session.)
3. **`target`, `bound`, `landings`, `shows`** exact against Lean functions; `sort.Search`. (0.5-1.)
4. **`HistoryRevs`** (after G13), `rvOfMsg`/`decodeItemRVs` round trips. (1.)
5. **`searchRun_accepts`** (pure, over `fullComplete`), **`CheckShared`**, `SeedShared`'s pure half,
   `NoForeign`/`PastRead`/`PinnedRead`/`Floor`. (0.5-1.)

**Estimate: 4-6 sessions**, plus a short Go session for G11-G13 and the re-translation (they do not block
step 1: `histHashes`, `skipTo`, `settle` and `cfgSet` are untouched by them). Builds are moderate: the
etcd3 package's `MDefs` cone, not the driver's `Inv.lean`.

## Handoff K9-1 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **Scope done**: §1 lists the functions (about 700 Go lines), §2 drafts their specs in Lean, §4 gives the
  order and the estimate (4-6 sessions, plus a Go session for G11-G13). **G11** (an unlocked `memo` map in a
  persistent `Step`), **G12** (`crossCheck`, a package variable read in program code) and **G13**
  (`sort.Slice` has no spec) are Go changes K9 needs before it can prove `stepIdx` and `HistoryRevs`. They
  are not made yet and need a KGO session. They do not block step 1 (the hub).
- **K4 tweaks** (`361664181e`, §3): `OpAnchors`'s watch clause is now `e.t < 4`, and `SettleL.land` now
  requires `l < 2 ^ 64`. Neither is a top-level statement.
  Build of record: fk-lean2, `fklean1-check.sh`, target `...k8s.dist.SharedComplete` at `0befb48da1`, exit 0 (SharedWatch, SharedSettle and SharedComplete recompiled; the first try failed on a syntax error in the edited line, fixed). `fullComplete` still has no `sorry`.
- **`SharedGo.lean`** (`bd99e48765`, pure): `SettleWith`/`SearchRunWith` (K4's search with any landings),
  `SearchRunN` + `fullCompleteN` (K4's run starts each operation at or above the seed's revision), and
  `searchRunN_with` (K4's run is a run with any landings that contain K4's). **Not built yet**: the coordinator
  stopped the session before its build. The next session builds it first, target
  `Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedGo`, on fk-lean2 with
  `/shared/tmp/fklean1-check.sh`. Likely fixes: the `rcases`/`word` chain in `kstepL_rv_ge`, and whether
  `induction` regeneralizes `hn` in `settleL_with`.
- **No `sorry`** and no axiom on the branch.
- **Next steps (K9-2)**: build `SharedGo`. Then the hub, §4 step 1: `SharedDefs.lean` (`HWf`, `RevsL`,
  `hhOwn`, `sharedM`/`sharedS`), and the specs and proofs of `intern`, `canonLocked`, `canonical`,
  `cfgSet.add`, `skipTo` and `settle`. Ask KGO for G11-G13.

## Handoff K9-2 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **`SharedGo.lean` builds** (fk-lean2, target `...k8s.dist.SharedGo`, exit 0) with no change: K9-1's
  feared fixes (`kstepL_rv_ge`, `settleL_with`) were not needed. No `sorry`, no axiom on the branch.
- **`SharedDefs.lean`** (defs, `Proof/.../k8s/etcd3/`): `HWf`, `gapsL` (the foreign stores `skipTo`
  appends: items unchanged, revision `histLen + 1`), `ikey`/`ckey` as map keys (classical `DecidableEq`,
  `IntoValInj` from the translation's field projections), `canonNode`, `gapsOwn`, `hhInv`/`hhOwn`
  (§2.3's lock invariant), `cfgSetOwn`, and `histOwn_agree_len` (one node holds one history, from the
  nodes' recorded lengths; what `cfgSet.add` and `skipTo` need instead of canonicity). Design choices:
  `is` carries no invariant (`canonLocked` walks the caller's own history, so it never needs to know what
  a node in `is` holds); a `canon[k]` node records only `k`'s `prev` and `n` and some store (`intern`
  compares stores with `storeEqual`); `gaps[base]` records `base`'s history `hs` and node `i`'s history
  `hs ++ gapsL s |hs| (i+1)`; `canon` and `is` are both `nil` or both made (`intern` makes both).
- **Specs written and built** (`Spec/.../k8s/etcd3/`): `pendEqual`, `mix`, `strHash`, `storeHash` (some
  `w64`: no spec relies on a hash value), `histHashes.{intern, canonLocked, canonical, skipTo}`,
  `cfgSet.add`. Not yet written: `settle` and `SharedModel` (§2.1-2.2: need `RevsL`, `revsOwn`,
  `landingsL`; take `GoSettle R b full x y := SettleWith (landingsL R b full x y)` from `SharedGo`, so
  that `searchRunN_with` applies directly).
- **Proofs built** (`Proof/.../k8s/etcd3/`): `pendEqual`, `mix`, `strHash`, `histHashes__canonical`
  (over `canonLocked`'s spec). Build of record: fk-lean2, targets the nine specs and four proofs, exit 0
  at the commit before this note. Left (step 1): `storeHash`, `intern`, `canonLocked`, `skipTo`, `cfgSet.add`,
  then `settle`'s worklist and `SharedModel`. None is in `etc/link-lean-first-k8setcd3.txt` yet (add
  them with their callees and rerun `etc/gen-link.py --k8setcd3` once the set is complete).
- **Proof notes** (learned the hard way): the package's `IsPkgInit` needs `variable [reg :
  EtcdGrove.k8s.CompactorRegistry]`; `defer` needs `wp_apply wp_with_defer as %defer defer` first;
  `for i := range a` loads `a[i]` itself (so `a[i]` is loaded twice: `configEqual`'s pattern); a loop
  condition `i < len(s)` on a string comes out of `wp_if_destruct` as `#(decide …) = #true` over
  `BitVec.ofNat` while the goal keeps `W64 ↑len` (`strHash`: `BitVec.ofInt_natCast`); no
  `by_contra`/`List.reverseRecOn` (no Mathlib). Maps: `wp_map_lookup1/2`, `wp_mapInsert`,
  `wp_map_make1`, `pure_wp_map_nil_lookup1` (a lookup in a `nil` map: `canonLocked`'s first `is[n]`).
- **Merges**: neither `k8s-dist-k4/2026-11-27` nor `k8s-dist-g11/2026-11-28` was on lean at hand-off; not
  merged. STATUS.md not updated (nothing landed; add the K9 entry when the stage lands).

## Handoff K9-3 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **Merges**: none. K4 had not landed on lean (`k8s-dist-k4/2026-11-27` still gating), and its fetched head
  (`2a71df1164`) was already in this branch, so per the brief nothing was merged; the Perennial pin stays
  `148615524` (lean is at `e5c2d6f62`: the next session that merges lean needs the pin's Perennial build on
  fk-lean2, as KGO-4/K5-6 did).
- **Proved and built** (fk-lean2, each target exit 0): `storeHash`, `histHashes.intern`,
  `histHashes.canonLocked` (with `wp_hh_is`, the `is[n]` lookup under `hhInv`, and `take_succ_snoc`).
  Linked: `etc/link-lean-first-k8setcd3.txt` gains `mix strHash storeHash pendEqual histHashes__intern
  histHashes__canonLocked histHashes__canonical`; `Link.lean` regenerated (`etc/gen-link.py --k8setcd3`).
  Build of record: fk-lean2, target `...k8s.etcd3.Link` at `16fa883947` (the link commit), exit 0 (12207 jobs).
- **`SharedDefs.lean` changes**: `ikey_safeMapKey`/`ckey_safeMapKey` (field-by-field `==`, as
  `client_go/util/consistency`'s keys); `arrayLiteralSize1` (shared by the proofs; one name per namespace,
  since `Link` imports every proof); `cfgSetOwn`'s buckets now record, for each index, that the list's
  configuration there has the key's history (`∃ d, cs[i]? = some d ∧ d.hist' = k.hist'`): `cfgSet.add`
  compares only stores and pending writes, trusting the bucket for the history, so its `false` case
  (`g ∈ gs`) needs this (then `histOwn_agree_len` gives the same history).
- **Left (step 1)**: `cfgSet.add` (plan: join after the `buckets == nil` check as in `intern`; take the
  bucket out of the map with the two restore wands of `intern`'s `Hsl`; `&&` of `storeEqual`/`pendEqual`;
  after appending, `bigSepM_mono` re-proves every bucket's indices against `cs ++ [c']` with
  `List.getElem?_append_left`); `skipTo` (holds `hh.mu`, `canonLocked`, then `gaps[base]` grown by `intern`
  of foreign stores: `gapsOwn`'s list is `hs ++ gapsL s |hs| (i+1)`); then `settle` and `SharedModel`
  (§2.1-2.2; `RevsL`, `revsOwn`, `landingsL`; Go's settle as `SettleWith (landingsL …)` from `SharedGo`).
  Not started: KGO-5's `stepIdx`/`crossCheck`/sorting (branch `k8s-dist-g11/2026-11-28`).
- **Proof notes** (new): `wp_apply spec $$ [$H]` (with `$`) frames the precondition; `$$ [H]` leaves it as a
  first goal. `wp_join (Q := fun v => …)` binds a loop condition's `if:` (`canonLocked`'s `n != nil && !is[n]`)
  so the loop's exit is proved once. `wp_join R with [hyps]`: only the listed hypotheses reach the cases, so
  list the pointers the bound code loads (`hh`). `ipersist` needs a WP goal (a basic update). `iStructNamed Hp`
  splits `p ↦□ hn` into field points-tos before `wp_auto` loads a field. `iframe` leaves persistent
  hypotheses (`□H`): `iframe #` or `iexact`. A slice literal: `wp_apply (wp_slice_literal (l := [..]))` and
  `simp only [arrayLiteralSize6]` (a `rfl` lemma) to name the slice. Loop conditions come out of
  `wp_if_destruct` sometimes as `sint.Z j < …` and sometimes as `#(decide …) = #true` (read the goal).
- **No `sorry`**, no axiom. WIP commits on the branch are build iterations (squash before landing, or keep).

## Handoff K9-4 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **Merges**: lean at `4b456e0c9f` (K4 landed; both K4 premise changes kept: `OpAnchors`'s `e.t < 4`,
  `SettleL.land`'s `l < 2 ^ 64`; no conflict), then `k8s-dist-g11/2026-11-28` as fetched (`c650569b19`,
  G11-G13; not yet on lean), clean. The Perennial pin is now `e5c2d6f62`: fk-lean2 has it built
  (`/home/ubuntu/eg/perennial-e5c2d6f62`, `pbuild-e5c2d6f62.sh`, exit 0), and the branch's fk-lean2 worktree
  has rebuilt onto it (5256 jobs for the targets below), so the next builds are incremental.
- **`hhInv` split** (`SharedDefs.lean`): `hhInv hh := hhCanon hh ∗ hhGaps hh`; `canon`/`is` in `hhCanon`,
  `gaps` in `hhGaps`. `intern`'s and `canonLocked`'s specs now take `hhCanon` (they never touch `gaps`).
  Why: `skipTo` calls `intern` while it holds `gaps[base]` outside the map. With the old spec,
  `intern` would hand back an `hhInv` with a fresh `gaps` map, possibly `nil`, and then
  `hh.gaps[base] = g` could not be proved panic-free. `canonical`'s proof splits `hhInv` after `Lock`
  and joins it again before `Unlock`.
  **Built** (fk-lean2, at `25ddd45730`): `SharedDefs`, `histHashes__intern`, `histHashes__canonLocked` and
  `histHashes__canonical` all compile with the split.
- **`cfgSet.add`** (`Proof/.../etcd3/cfgSet__add.lean`, WIP): the proof is started: the `buckets == nil`
  join and the `canonical` call. The build at `25ddd45730` failed on two trivial errors, not yet fixed:
  (1) `bucketIdx`/`bucketIdx_snoc` need `variable [GooseExts]` (wrap them in `section pure variable
  [GooseExts] … end pure`, as in `histHashes__skipTo.lean`); (2) `BigSepL.bigSepL2_length` is not the
  name (find the `[∗list] _;_` length lemma; or take the length from `ownSlice_len` of `Hcs`). After those,
  check the goal at the trailing `done`. The plan for the rest: `buckets[k]`'s slice comes out of the map
  with two restore wands, as in `intern`'s `Hsl`. The insert wand should already be stated against
  `cs ++ [c']` (use `buckets_snoc`, written in the file, on the rest of the map). Then the range loop
  (`pure_wp_slice_for_range` turns it into a `wp_for`, invariant as in `intern`), and the `&&` of
  `storeEqual`/`pendEqual`. A match gives `gd = g`: equal store, equal pending writes, and
  `d.hist' = k.hist' = c'`, so `histOwn_agree_len` gives the same history. Otherwise append `len(list)`
  to the bucket and `c'` to the list.
- **`skipTo`** (`Proof/.../etcd3/histHashes__skipTo.lean`, WIP, not built yet): the pure lemmas
  `gapsL_succ` and `repeat_foreignL_gaps` (`skipToL`'s history is `hs ++ gapsL s |hs| j`, under `HWf`).
  The proof covers the `t ≤ rv` return (`skipToL_le`) and the `nil` history (impossible: `HWf`'s last
  store, then `typedPointsto_not_null`), then stops at `done`. The plan for the rest:
  1. `Lock`, split `hhInv`, `canonLocked` gives `base`.
  2. The `gaps == nil` join, as in `cfgSet.add`.
  3. Take `gaps[base]` out with one insert wand (`∀ sl', gapsOwn base sl' -∗ [∗map] … <[base := sl']> G'`).
     Its `hs` is `c`'s history by `histOwn_agree_len`, so its last store is `c`'s store by `HWf`.
  4. Loop invariant: `g ↦ gsl ∗ gsl ↦* ns ∗ cap ∗ [∗list] i ↦ n ∈ ns, histOwn n (hs ++ gapsL s |hs| (i+1))
     ∗ hhCanon hh ∗ ⌜|hs| + |ns| < 2^63⌝`. The body is `histLen` and `intern`, then append.
  5. `map.insert`, then load `g[t-rv-1]` *before* applying the insert wand (the wand consumes
     `gsl ↦* ns`).
  6. `Unlock`; the result follows from `repeat_foreignL_gaps`.
- **Left (step 1)**, after `cfgSet.add` and `skipTo`: `settle`'s spec and proof, then `SharedModel`'s.
  `settle` needs `landings` (and `shows`, `sort.Search`, a closure) specified and proved first, or at
  least `landingsL` defined from the Go. `SharedModel` also needs `bound`, `target` and `stepIdx`
  (step 2). Then link the new proofs (`etc/link-lean-first-k8setcd3.txt`: `histHashes__skipTo`,
  `cfgSet__add`, with `histLen` among their callees; `etc/gen-link.py --k8setcd3`).
- **No `sorry`**, no axiom. The two WIP files end in `done`, so they do not build; neither is in `Link`.
  The WIP commits are build iterations.

## Handoff K9-5 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **Merges**: none (lean not fetched again; KGO-5's `k8s-dist-g11` already merged in K9-4).
- **Proved and linked**: `cfgSet.add` (`cfgSet__add.lean`) and `histHashes.skipTo` (`histHashes__skipTo.lean`),
  both in `etc/link-lean-first-k8setcd3.txt` (`histHashes__skipTo: histHashes__canonLocked histHashes__intern
  histLen`, `cfgSet__add: histHashes__canonical storeHash storeEqual pendEqual`), `Link.lean` regenerated.
  Build of record: fk-lean2, target `Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Link` at
  `328373cafc`, exit 0 (12214 jobs). No specs changed.
- **New defs module `SharedLand.lean`** (pure Lean twins read off the Go): `RevsL`, `objKeyL`,
  `decItemRVsL` (`decodeItemRVs`, as `decWEventsL`), `showsL`, `landOkL` (`landings`' `add` test),
  `landingsL` (Go's order; `sort.Search` over the sorted anchors is `dropWhile (· < rv)`), `GoSettle R b full
  x y := SettleWith (fun c w => (landingsL R c.st.st.rv w b full x y).map uint.nat)`, `SettleOk` (bounds), and
  `revsOwn r R` (anchors `↦*□`, sorted; `keyRevsOwn` for `byKey`/`fastByKey`: `↦$□` map, `[]` off the map).
- **New specs** (`Spec/.../k8s/etcd3/`): `shows` (returns `showsL`), `landings` (returns a fresh slice
  of `landingsL R c.st'.rv' …`), `settle` (the result's configurations are exactly `GoSettle`'s from `g`, each
  `HWf`; premise `HWf g.st ∧ SettleOk R y g`). `settle`'s `SettleOk` is a DRAFT guess at the bounds the proof
  needs (skipTo's `t < 2^63`, `l - 1` with `l ≥ 1`). Checked with `etc/lean-check.py` on fk-lean2 (0 errors);
  built (fk-lean2, targets the three specs and `etcd3.Link` at `f34b269629`, exit 0, 12227 jobs); no proofs yet,
  not in `Link`.
- **Edit loop that worked** (much faster than a build per edit): copy the file into fk-lean2's worktree
  `/home/ubuntu/eg/wt/k8s-dist-k9/2026-11-28` and run `etc/lean-check.py -a FILE` there (script
  `scratchpad/rcheck.sh` of this session: `scp` then `ssh … python3 etc/lean-check.py`). Always pass `-a`:
  without it the check sometimes returns at once with "NOT YET CHECKED". Don't run it while a `fklean1-check.sh`
  build of the same worktree is going.
- **Proof notes** (new): a range loop whose value variable shares the index's name (`for _, i := range`) leaves
  `i✝`: `rename_i iu_ptr` (renames only the LAST inaccessible: `rename_i a b` also renames `inst✝`), then
  `irename: (iu_ptr ↦ zero_val w64) => iu`. A slice index `s[e]` comes out as `if 0 ≤ sint.Z e ∧ … then …
  else Panic`: prove the bound and `simp only [Hb, _root_.and_self, ↓reduceIte]` before
  `wp_load_slice_index`. A loop invariant's persistent part (`[∗list] … histOwn`) comes back spatial after
  `wp_for`: `icases Hl with #Hl` before a `wp_join … with [...]`, else the join's branches see the stale one.
  `iframe` splits `[∗list] _;_ ∈ cs ++ [x]; gs ++ [g]` itself, leaving the singleton
  (`BigSepL2.bigSepL2_singleton`). In `SharedLand` `||` on `Bool` clashes with Iris's notation: `Bool.or`.
- **Left (step 1)**: prove `shows` (needs `decodeItemRVs`' spec and proof: a loop over `parseRV`/`decodeObj`,
  `decItemRVsL`'s twin; and `decodeWEvents`' spec), `landings` (closure `add` over a captured slice,
  `sort.Search` with a closure: Perennial's spec), then `settle` (worklist invariant, §2.2), then
  `SharedModel` (`bound`, `target`, `stepIdx`; `targetL` exists, `boundL` not yet). Link each when proved.
- **No `sorry`**, no axiom, no statement/premise/trusted-text change.

## Handoff K9-6 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **Merges**: lean at `2018327946` (Perennial pin `e2eda8223`, built on fk-lean2 as `perennial-e2eda8223`
  with `pbuild-e2eda8223.sh`). The merge rebuilds nearly everything (new pin): the first Link build after it
  is long (bbolt, etcd server); lean-check of one etcd3 file rebuilt its cone in ~45 min.
- **Build of record**: fk-lean2, targets `etcd3.Link`, `Spec…landings`, `Spec…settle` at `6bb8fcae8b`, exit 0
  (12231 jobs).
- **Proved and linked**: `decodeItemRVs` (new spec: `decItemRVsL`, each item `item.mk (objKeyL o) o false`,
  owned) and `shows` (`showsL`). `decWEventsL_t` moved from `watchOk.lean` (a proof) to `SharedLand.lean`.
- **Spec changes (branch only)**: `cfgSet.add` drops its premise `gs.length + 1 < 2^63` (the appended
  slice's `ownSlice_len` gives it; settle could not supply it); `SettleOk` revised to what settle needs:
  every landing `l` R or the answer names has `l + |pend| + 1 ≤ 2^63` (anchors `a + |pend| + 2`), the
  configuration's `rv + |pend| + 1 ≤ 2^63`, `items + |pend| < 2^63`, pending inputs are writes.
- **Drafts, not built** (`notes/k9-drafts/`, move back to `Proof/.../etcd3/` to continue):
  `settle.lean.txt`: pure part complete but unchecked (`settleSuccs`, `SettleWith` trans/closure,
  `hwf_*`, `landingsL_mem`, `SGood`, `sgood_succ`, `SetInv` init/skip/add/done) and the WP proof drafted
  on `closure.lean`'s template (outer worklist loop, `cfgSet.add`, inner loop over `d.pend`, no-effect push,
  landing loop over `skipTo`/`mstep`/`advance`), never checked. `landings.lean.txt`: `dropWhile_eq_drop`,
  `ancF`, skeleton. Plan for `landings`' closure `add`: persist the read-only local cells, state its triple
  as a persistent Iris hypothesis (`predImplements` style, `wp_start` inside), `wp_apply` it at the four
  calls; `sort.Search` as in Perennial's `SearchInts` (`RecV` → `#(func.mk ..)` rewrite, `I` = the cells).
  Link lines then: `landings: shows =_root_.Perennial.sort.wp_Search`, `settle: cfgSet__add mstep removeAt
  landings histHashes__skipTo advance`.
- **Proof notes**: `wp_if_destruct` on a Go string/uint equality `subst`s the variable (`key`, `r` vanish):
  state facts as `∀ k rr, k = … → rr = … → showsL x y k rr = true`. A `word` inside such a branch can make
  a kernel error (`_proof_1_N` applied to the wrong arguments): prove the fact before the branch or as a
  top-level lemma (`sint_lt3_iff`). Avoid dependent `os[i]'h` in loops (kernel mismatch): `list_elem`.
  A context cell named `in` breaks `wp_for` (`iNamed`): `irename : (in_ptr ↦ x : IProp GF) => Hin` first.
  An Iris hypothesis whose type is a `match` on `hd`: `isimp only [hd] at Hd`. `simp` turns `W64 5` into
  `5#64`, so `simp [hk5]` misses: `simp only [showsL, if_neg hk5, …]`.
- **Left**: finish and check `settle` and `landings` from the drafts, link them; then `boundL`/`bound`,
  `target`, `SharedModel`.
- **No `sorry`** in built files, no axiom, no top-level statement/premise/trusted-text change.

## Handoff K9-7 (2026-11-28, branch `k8s-dist-k9/2026-11-28`)

- **K9-6's build of record** (fk-lean2, `c11353076f`, `Link` and the step-2 specs): passed, 12231 jobs.
- **Proved and linked**: `settle` (`23f7173ca8`, from the K9-6 draft) and `landings` (`bcfe1ca71d`), both
  in `etc/link-lean-first-k8setcd3.txt` and `Link.lean`. Build of record at `bcfe1ca71d` on fk-lean2
  (`etcd3.Link`, `etcd3.Results`): passed, 12286 jobs. `notes/k9-drafts/` is gone (both drafts moved).
- **How `landings` is proved**: the closure `add` is a persistent Iris triple (`Hadd`) proved once, after
  `generalize hf : (func.mk BAnon (BNamed "r") _ : GoFunc) = f at *`. Its pre/post thread the cells it
  reads (`in`, `out`, `w`: loading a field from a persistent struct `↦□` does not work) and `ls`; `next`,
  `full`, `b` are persisted. `sort.Search` follows Perennial's `SearchInts` (`RecV` → `#(func.mk ..)`,
  `I` = the `revs` and `c` cells, `ancF`, `IsMonoPred` from `Hsorted`). The search's `i ≤ n` is not in
  `Search`'s post: it follows from `Hoob` and `Hlt`. The `if in.Key == w.Key && ...` statement has five
  leaves. With `full`, everything after it is proved once: `wp_bind (If _ _ _)`, then
  `iapply wp_wand (Φ := ⌜v = executeVal⌝ ∗ state)`.
- **Proof notes**: the kernel error (`_proof_1_N` applied to the wrong arguments) came from two `word`s
  in different `wp_if_destruct` branches, one where an `obtain ⟨.., rfl⟩` had substituted a variable.
  Hoisting the second fact before the branch as an implication fixed it (`settle`'s `Hw0`; `landings`'
  `Hgt`/`Hn`/`Hb0`/...). To find the culprit, turn ranges of `word` into `sorry` and bisect.
  `iStructNamed` leaves a `"_" ∷ True`; remove it with `irename : ("_" ∷ True : IProp GF) => J; iclear J`.
  `wp_load_slice_index ... as _` leaves an unnamed copy, which breaks `wp_for`'s `iNamed`: name it and
  `iclear` it. `wp_if_destruct` on a Go `bool` variable splits `false` first.
- **Left**: `bound` and `target` have no specs yet (`targetL` exists in `dist/SharedSearch.lean`; there is
  no `boundL`). Write `boundL` and `bound.spec`, then `target.spec`, prove both and link them; then
  `SharedModel`.
- **No `sorry`** in built files, no axiom, no top-level statement, premise or trusted-text change.
