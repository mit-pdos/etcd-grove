# k8s 7g step 1: the trust-boundary texts of the maintainers' checker (2026-11-17)

**Reviewed 2026-11-17** (`notes/axiom-review/k8s-7g-trust.md`): all survive and their axioms are
added, except `SuggestsClientDelay.spec`, refuted with the existing `HasStatusCause.wp_proof`
(`apiErrOk` does not hold the details); fix (a) and T land as their own stage; V then applies here,
with M2.

Hard stop (trust base). Every text below is written and elaborates (`etc/lean-check.py -a`); **no
axiom file is added**. Each spec's file header says why it is faithful and names its Go tests.
Go evidence: `examples/k8s/etcd3/trustspecs_test.go` (package `etcd3`) and
`examples/k8s/etcd3/correctness/cmpdiff_test.go`, all green (`/shared/tmp/k8s7g/step1-go.out`).

**2026-11-18 (resumed after apierrors-fix and the pin bump): V applied in place and
`SuggestsClientDelay.spec` restated, both PENDING the independent attack** (hard stop; texts in
`Proof/k8s_io/apimachinery/pkg/api/errors/View.lean`, `plainLeaf` and `apiErrAt`'s `.plain` arm, with
M2's header; `Spec/k8s_io/apimachinery/pkg/api/errors/SuggestsClientDelay.lean`, statement unchanged,
header restated over the fixed `apiErrOk`). T landed with apierrors-fix (`IsTooManyRequests.spec`, pre
`nil ∨ apiErrOk`). New Go test `TestPlainWrapperTypedNil` (M2). No axiom file for
`SuggestsClientDelay` yet. The ~6 proofs that build or destructure `apiErrAt _ .plain`
(`Calls.lean` `clientErr_notTooLarge`/`sentV_plain`, `call.lean`, `watchChan__syncPaginated`,
`store__GetList`, `handleCompactedErrorForPaging`, `interpretListError`) are repaired after the attack.

**2026-11-18, attack passed** (`/shared/tmp/k8s7g-attack/report.md`; decided by etcd-grove-03): V and
`SuggestsClientDelay.spec` SURVIVE (18 Go attacks) and are accepted. Applied: R2 (View.lean's header:
a persistent WP does not mean `Unwrap` reads only read-only state; every allowed result is nil or a
leaf, which answer the same), R4 (the details disjunct of `SuggestsClientDelay.spec` states
`st.Details' ≠ null`). R3 (no view for wrappers of depth ≥ 2 or `Unwrap() []error`) is coverage only.
R1 (`fmt.Errorf`'s model reachable through `wp_func_call`, bypassing `etc/errorf-wrap-check.py`) goes
to a separate audit; no 7g proof steps into `fmt.Errorf`'s model. The axiom
`apierrors.SuggestsClientDelay.wp_proof` is added
(`Proof/k8s_io/apimachinery/pkg/api/errors/SuggestsClientDelay.lean`).

**2026-11-18 (night): clause 4 of `reflect.DeepEqual.spec_k8s`, PENDING the independent attack**
(hard stop; option (B), decided by etcd-grove-03; no proof uses it yet). `Spec/reflect/DeepEqualK8s.lean`,
the fourth conjunct (header: "4." and "Clause 4"): `DeepEqual(Response{o1, e1}, Response{o2,
*StatusError at l})`, with deep views of `o1`, `e1`, `o2` (any `dq`), any `l` (null too) and no
ownership of the `*StatusError`, returns `false` and gives the views back. Why: the `Object` field is
compared on the held cells, then `Err`: nil against non-nil, or differing dynamic types (no `DeepV` is a
`*StatusError`), without reading the `*StatusError`. One orientation only (the model's expected
response first, as `Step`, `validateGet`, `validateList`, `equalListResponse` call it). The axiom
`reflect.DeepEqual.wp_proof_k8s` (`Proof/reflect/DeepEqualK8s.lean`, docstring updated) now states it.
Go test: `examples/k8s/etcd3/trustspecs_test.go` `TestDeepEqualTooLarge` (20000 random pairs from
`TestDeepEqualViews`' generators; too-large errors with retry 0 and 2, a zero `*StatusError`, a typed nil
`*StatusError`; the second object independent, mutated, or the same pointer; `false` in both orders, no
panic): PASS.

**2026-11-18, clause 4 attack passed** (`/shared/tmp/k8s7g-attack2/report.md`; decided by etcd-grove-03):
clause 4 SURVIVES (11 attacks, Go under `-race`) and is ACCEPTED. m2 applied (the spec's header: no
`DeepV` being a `*StatusError` is what makes clause 4 true; a constructor for one must revisit it). m1
recorded: one orientation only (model's response first), which every use is.

**2026-11-19 (night 10b): IsNil attack passed** (`/shared/tmp/isnil-attack/report.md`; decided by etcd-grove-03):
`b = false → s ≠ slice.nil` SURVIVES and is ACCEPTED. Minor 1 applied (header: `slice.nil` is the only REACHABLE
slice with a nil `Data`; the model has other null-pointer slices, `⟨null, 0, c⟩` from slicing a nil array pointer,
so "ptr null → `slice.nil`" is never a law). Minor 2 recorded: on reachable states `b = decide (s = slice.nil)`
would hold; the post leaves `b` open for non-nil empty slices (a harmless weakening; no change). Also accepted
(Freeze list): `listIs` (GetList's success post) and `finalizeList`'s post strengthened in place to
`∃ pl s, … ⌜s ≠ slice.nil⌝ …`; `listAt` unchanged.

**2026-11-19 (night 10): MakeSlice attack passed** (`/shared/tmp/makeslice-attack/report.md`; decided by
etcd-grove-03): `s ≠ slice.nil` SURVIVES and is ACCEPTED. Minor 2 applied (header: implied by `s.cap = m` for
`m > 0`; amounts to `s.ptr ≠ null`; only `[]Obj`). Minor 1 recorded: cap-0 results share `&zerobase`, so no
freshness or distinctness of the location may ever be claimed for capacity 0.

**2026-11-19 (night 10): `reflect.Value.IsNil.spec` gains `b = false → s ≠ slice.nil`, PENDING the independent
attack** (hard stop; no proof uses the new conjunct; `finalizeList` reads `hb.1`). `Spec/reflect/Value__IsNil.lean`
(header: "False only of a non-nil slice"); the axiom `Proof/reflect/Value__IsNil.lean` is unchanged. Why:
`finalizeList`'s `if v.IsNil() { v.Set(MakeSlice(t, 0, 0)) }` must leave the items non-nil on the `false`
branch too, and the old post said nothing there. Faithful: `IsNil` of a slice is `Data == nil`; Go's nil slice
is the model's `slice.nil` and the only slice with a nil `Data`; a non-nil `Data` (`&zerobase` included) is a
non-null location (as in the MakeSlice attack, item 4). Go test: `examples/k8s/etcd3/trustspecs_test.go`
`TestIsNilFalseNonNil` (IsNil iff `== nil` over nil, empty literal, make 0 / cap 4 / 2, reslices to 0,
MakeSlice 0 0): PASS.

**2026-11-19 (night 9): `reflect.MakeSlice.spec` gains `s ≠ slice.nil` in its post, PENDING the independent
attack** (hard stop; option 1, decided by etcd-grove-03; no proof uses the new conjunct yet; the one existing
user, `ListContract.lean`, reads only `Hs.1`). `Spec/reflect/MakeSlice.lean` (header: "Never nil"); the axiom
`Proof/reflect/MakeSlice.lean` is unchanged. Why: the real model's list is never nil and `reflect.DeepEqual`
tells a nil `Items` from an empty one, so `RawRel` needs `GetList`'s `Items` non-nil for an empty list, which is
`finalizeList`'s `reflect.MakeSlice(t, 0, 0)`. Faithful: `MakeSlice` sets `Data: unsafe_NewArray(elem, cap)`,
and `mallocgc` of zero bytes returns `&zerobase`, never nil (`reflect/value.go`, `runtime/malloc.go`, go1.27).
Go test: `examples/k8s/etcd3/trustspecs_test.go` `TestMakeSliceZeroNonNil` (length 0, capacities 0, 1, 5:
`IsNil` false, `!= nil`, len/cap, not `DeepEqual` to a nil `[]Obj`): PASS. To use it after the attack:
`listContractOk'`'s MakeSlice-0 clause, `finalizeList`, `GetList.spec`'s post (strengthened 7e store posts, for
the Freeze list).

## 1. New trust-boundary specs (files written)

| Spec | File | Axiom to come | Go tests |
| --- | --- | --- | --- |
| `reflect.DeepEqual.spec_k8s` (4 clauses: two interface values; two `correctness.Response`; two `map[string]runtime.Object`; clause 4, 2026-11-18: a deep `Response` against one with a `*StatusError` error, `false`) over `k8sDeep.deepRep`/`mapRep` | `Spec/reflect/DeepEqualK8s.lean`; vocabulary `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Deep.lean` (`DeepV`, `deepRep`, `itemsRep`, `remRep`, `mapRep`) | `reflect.DeepEqual.wp_proof_k8s` | `TestDeepEqualViews` (60000 random pairs, the three shapes), `TestDeepEqualTooLarge` (clause 4), `TestDeepEqualNamedCases`, `TestDeepEqualFacts` |
| `cmp.Diff.spec_eventRefs` (no options, two `[]eventReference`: `""` iff same nil-ness and equal elements) | `Spec/github_com/google/go_cmp/cmp/Diff.lean` | `cmp.Diff.wp_proof_eventRefs` | `TestCmpDiffEventRefs`, `TestCmpDiffEventRefsRandom` |
| `maps.Keys.spec_objMap` (returns `f`; `slices.Sorted(f)` gives the map's keys at that time, strictly increasing by `go.GoStringLt`) | `Spec/maps/Keys.lean` | `maps.Keys.wp_proof_objMap` | `TestMapsKeysSorted` |
| `maps.Clone.spec_strBool` | `Spec/maps/Clone.lean` | `maps.Clone.wp_proof_strBool` | `TestMapsCloneEqual` |
| `maps.Equal.spec_strBool` | `Spec/maps/Equal.lean` | `maps.Equal.wp_proof_strBool` | `TestMapsCloneEqual` |
| `meta.SetList.spec_objList` (`Items` := fresh non-nil slice of the objects' structs, `nil` error) | `Spec/k8s_io/apimachinery/pkg/api/meta/SetList.lean` | `meta.SetList.wp_proof_objList` | `TestSetListObjList` |
| `reflect.MakeSlice.spec` (existing, 7e-2): `s ≠ slice.nil` added to the post (2026-11-19) | `Spec/reflect/MakeSlice.lean` | `reflect.MakeSlice.wp_proof` (exists) | `TestMakeSliceZeroNonNil` (and 7e-2's `examples/k8s7e2attack` `TestMakeSlice*`) |
| `apierrors.SuggestsClientDelay.spec` (over `apiErrAt` views; `delayV`) | `Spec/k8s_io/apimachinery/pkg/api/errors/SuggestsClientDelay.lean` | `apierrors.SuggestsClientDelay.wp_proof` | `TestSuggestsClientDelay`, `TestStorageErrorNotAPIStatus` |

`slices.Sorted` has no spec of its own: `maps.Keys.spec_objMap` states what it returns on `Keys`'s
iterator (the only use). No other names-only callee needs a spec (scope §1.2's existing specs, and
proposals V and T below).

## 2. Changes to existing trust text (proposed, NOT applied)

The checker calls `storage.IsTooLargeResourceVersion` (hence `apierrors.IsTimeout`,
`HasStatusCause`), `apierrors.IsTooManyRequests` and `SuggestsClientDelay` on `nil` and on
`*storage.StorageError`s (every NotFound, KeyExists, InvalidObj output). Today's view `.plain`
covers neither: it is a non-nil **leaf** (no `Unwrap`), and `*StorageError` has `Unwrap() error`.
Scope §1.2 said these specs exist; they do not cover these errors.

**V. Extend `.plain` in place** (`Proof/k8s_io/apimachinery/pkg/api/errors/View.lean`; changes the
meaning of the existing axioms `IsTimeout.wp_proof`, `HasStatusCause.wp_proof`): nil, or a leaf, or
a non-`APIStatus` wrapper whose `Unwrap` (persistently) returns nil or a leaf. Generic (no
dependency on `k8s.io/apiserver`); `*StorageError` meets it by a lemma from its translated `Unwrap`
body (step 3).

Checked to elaborate in a scratch module (`/shared/tmp/k8s7g/step1-ScratchV.lean`, as `apiErrAtV`;
`plainLeaf` goes in View's `section leaf`, beside `leafErrTy`).

```lean
/-- `errors.As` finds no `APIStatus` in `err` without unwrapping it: nil, or a non-nil leaf whose
type is outside `APIStatus`'s type set. -/
def plainLeaf (err : GoInterface) : Prop :=
  err = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, err = GoInterface.ok ii ∧
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
    leafErrTy ii.ty

  | .plain => iprop(⌜plainLeaf err⌝ ∨ ∃ ii : GoInterfaceOk,
      ⌜err = GoInterface.ok ii ∧
        go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
        GoSemanticsFunctions.methodSet ii.ty !! go!"Unwrap" =
          some (go.signature.Signature [] false [go.error]) ∧
        GoSemanticsFunctions.methodSet ii.ty !! go!"As" ≠
          some (go.signature.Signature [go.any] false [go.bool])⌝ ∗
      □ ∀ Φ : val → IProp GF, (∀ e : GoInterface, ⌜plainLeaf e⌝ -∗ Φ #e) -∗
          WP (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #())) {{ Φ }})
```

Faithful (`errors/wrap.go` `As`): `nil` → `false`; a type outside `APIStatus` is not assignable to
the target; no `As` method; `Unwrap() error` (the method set holds one signature per name, so not
`Unwrap() []error`) → its result, `nil` (stop, `false`) or a leaf (no match, nothing to unwrap).
Go: `TestStatusChecksPlain` (`IsTimeout`, `HasStatusCause`, `IsTooLargeResourceVersion`,
`IsTooManyRequests` false on nil, NotFound, KeyExists, InvalidObj, `errors.New`, the sentinel),
`TestStorageErrorNotAPIStatus`. Cost: the ~12 files that build or destructure `apiErrAt _ .plain`
(`iright`/`ileft`); `IsTimeout`/`HasStatusCause` headers updated.

**T. `apierrors.IsTooManyRequests.spec` in place** (checked in the same scratch module) (today "some boolean", no precondition; a
hypothesis of client-go's cache `Link`, "boundary pending approval"):

```lean
abbrev IsTooManyRequests.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ apiErrOk err }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests)) (Val #err))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st _ => decide (st.Reason' = go!"TooManyRequests") || decide (st.Code' = W32 429)
      | .plain => false⌝ }}
```

Needed: `Model.Step` panics ("Errors on writes not supported by the model") when a write's output
has no object and `IsTooManyRequests` is true; with "some boolean" no-panic is unprovable. Go:
`TestIsTooManyRequests`.

**Finding (soundness, an existing hypothesis):** today's `IsTooManyRequests.spec` (no
precondition) is **false**: on a typed nil `*StatusError` (bare or wrapped) Go panics in
`Status()` (`ReasonForError`'s `err.(APIStatus)` succeeds, `e.ErrStatus` dereferences nil), as
found for `IsTimeout` on 2026-11-10. `TestIsTooManyRequests` checks the panic. It is a hypothesis
(`h_errors_IsTooManyRequests` in `Proof/k8s_io/client_go/tools/cache/Link.lean`), not an axiom, so
the reflector results holding it are conditional on a false premise (vacuous as stated). T adds the
precondition; the reflector's two call sites (`Reflector__watch.lean:379`,
`isWatchErrorRetriable.lean:44`) would then need `apiErrOk` of the watch error.

## 3. Facts the proofs need that are not trust text (steps 3 and 5)

- `errors.New` returns `*errorString` holding the message (for `deepRep (.errString s)` and for
  `plainLeaf`): Perennial's `errors.New.spec` hides it; `wp_New_errorString` (Perennial
  `errors-facts`, pending) or a local proof from Perennial's translated body.
- `storage.NewInvalidObjError.spec`'s post `∃ e` → the inner error's `errors.New(msg)` (proved spec,
  stronger post: a form decision).
- The `*StorageError` instance of V's wrapper (its `Unwrap` body, goose's method sets).

## 4. Trust-base delta of step 1 (when the axioms are added)

+7 axioms (the table in §1) +1 generated (`cmp`'s `opaqueInitsOk`, decided at step 0), 0 `sorry`;
V and T change two existing axioms' meaning and one hypothesis in place. Scope §4 estimated +6 to
+10.

### Step 3 changes to trust text (STOP 2, decided by etcd-grove-03, 2026-11-17)

For the joint independent attack of all 7g trust texts before the step-6 Freeze:

- (a) `maps.Keys.spec_objMap` (`Spec/maps/Keys.lean`, axiom `maps.Keys.wp_proof_objMap`) **in place**:
  the post is `(f : GoFunc), RET #f` (was `(f : val), RET f`, which may be a panic value, so no
  caller could step `let "$a0" := f`); the nested WP runs `Sorted` on `#f`. Stronger post; Go:
  `maps.Keys` returns a func literal (`maps/iter.go`). New Go test `TestMapsKeysNoPanic` (nil, empty,
  non-empty map: no panic, non-nil func).
- (b) `apimeta.ListAccessor.spec` (`Spec/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean`, a named
  hypothesis of client-go's cache `Link`, "boundary pending approval") **widened in place** to a
  conjunction: the reflector's typed-list row unchanged, and a second row for the driver's `*ObjList`
  (any pointer, nil included, precondition only `isPkgInit`: returns the same interface value and a
  nil error, `meta.go:69-86` first case `List`). The two reflector callers use `.1`. The file imports
  the driver's `Code` module (for `ObjList.ty`). New Go test `TestListAccessorObjList`.

## 5. For the attack

- `deepRep` is a fixed definition (no predicate parameter); each claim reads only cells it holds.
- The iterator of `maps.Keys.spec_objMap` reads the map when `Sorted` runs: the nested WP takes
  the map points-to then (the "function of mutable state" check).
- Nil-ness of slices is the model's `= slice.nil` (what `== nil` decides), of pointers `= null`.
- Not covered: typed nil pointers in interfaces, other dynamic types, other map/slice types, `nil`
  maps.

## 6. Freeze list: changes to the 7g statement after step 3

- **The driver's output records a failed precondition's message** (option (C) of the step-4 STOP, decided by
  etcd-grove-03, 2026-11-18). Reason: the stale-precondition counterexample (`questions.md`, "Step 4 STOP"):
  without the message, an update A whose precondition fails (PreRV "9") overlapping an update B of the same key
  (RV 1 -> 2) has the same plain output at either state, so the driver's model may linearize B before A, while
  A's real response (from its commit, "... ResourceVersion in object meta: 1") fails the maintainers' `Step` at
  the state with RV 2. Changed text (examples/k8s/etcd3/k8setcd3.go): `Output.ErrMsg` (filled only on
  `EInvalid`, from the store error's inner error, `se.Unwrap().Error()`), `invalidObj(key, msg)`,
  `preMsg(in, o)` (`Preconditions.Check`'s message: the UID's mismatch first, else the resource version's),
  `outEqual` compares `ErrMsg`. Lean: `invalidObjL key msg`, `invalidOutL`, `preMsgL`, `mdeleteL`/`mupdateL`.
  Go evidence: `TestInvalidMsg` (`invalidmsg_test.go`).
- **The store's spec vocabulary carries the message** (consequence, proved, not trusted): `KErr.invalidObj key
  msg`, `KPreF` (`ok`, `msg`), `ObjCodec.preF`, `respIs`'s `invalidErrMsg` case; the specs of
  `GuaranteedUpdate`, `Delete`, `conditionalDelete` take `c.S.preF pr`. A stronger post: no premise added.
  **Accepted by etcd-grove-03 (2026-11-18)** as a change to vocabulary frozen at 7e; for review at the 7g Freeze.
- **`outEqual.spec` restated as equality of the plain fields** (step 5, decided by etcd-grove-03, 2026-11-18): its
  `decide (a = b)` over the whole `Output` is false once `Raw` differs, which Go's `outEqual` ignores.

**2026-11-19 (night 11 decided by etcd-grove-03):** the IsNil threading, `listContractOk`'s `UpdateList` clause on
`metaAt` only (Freeze list: a premise of the 7e-frozen `GetList.spec`), `RawOk.lean`, `listOut`'s spec, `valsOk`,
the InvSteps `hval` premises and `call.spec`'s new post ACCEPTED. Too large: option (b), strengthen
`apierrors.tooLargeErrIs` with `Code = 504 ∧ RetryAfterSeconds = 0` if every producer is
`NewTooLargeResourceVersionError(_, _, 0)`. **Night 12 STOP:** it is not: `watchChan.startWatching` (retry
`Jitter(1s, 3.0).Seconds()`) and cacher `waitUntilFreshLocked` (retry 1) call it too, so
`NewTooLargeResourceVersionError.spec`'s post would have to change (questions.md "Night 12 STOP", options b1/b2).
