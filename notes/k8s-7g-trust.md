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

## 1. New trust-boundary specs (files written)

| Spec | File | Axiom to come | Go tests |
| --- | --- | --- | --- |
| `reflect.DeepEqual.spec_k8s` (3 clauses: two interface values; two `correctness.Response`; two `map[string]runtime.Object`) over `k8sDeep.deepRep`/`mapRep` | `Spec/reflect/DeepEqualK8s.lean`; vocabulary `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Deep.lean` (`DeepV`, `deepRep`, `itemsRep`, `remRep`, `mapRep`) | `reflect.DeepEqual.wp_proof_k8s` | `TestDeepEqualViews` (60000 random pairs, the three shapes), `TestDeepEqualNamedCases`, `TestDeepEqualFacts` |
| `cmp.Diff.spec_eventRefs` (no options, two `[]eventReference`: `""` iff same nil-ness and equal elements) | `Spec/github_com/google/go_cmp/cmp/Diff.lean` | `cmp.Diff.wp_proof_eventRefs` | `TestCmpDiffEventRefs`, `TestCmpDiffEventRefsRandom` |
| `maps.Keys.spec_objMap` (returns `f`; `slices.Sorted(f)` gives the map's keys at that time, strictly increasing by `go.GoStringLt`) | `Spec/maps/Keys.lean` | `maps.Keys.wp_proof_objMap` | `TestMapsKeysSorted` |
| `maps.Clone.spec_strBool` | `Spec/maps/Clone.lean` | `maps.Clone.wp_proof_strBool` | `TestMapsCloneEqual` |
| `maps.Equal.spec_strBool` | `Spec/maps/Equal.lean` | `maps.Equal.wp_proof_strBool` | `TestMapsCloneEqual` |
| `meta.SetList.spec_objList` (`Items` := fresh non-nil slice of the objects' structs, `nil` error) | `Spec/k8s_io/apimachinery/pkg/api/meta/SetList.lean` | `meta.SetList.wp_proof_objList` | `TestSetListObjList` |
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
