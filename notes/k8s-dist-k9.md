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
