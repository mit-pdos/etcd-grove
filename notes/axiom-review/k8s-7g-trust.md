# k8s 7g step 1: the maintainers' checker's trust-boundary texts (2026-11-17)

**Reviewed** (branch `k8s-7g` at `11962185aa`; index and texts: `notes/k8s-7g-trust.md`):
`reflect.DeepEqual.spec_k8s` (over `k8sDeep.deepRep`, `Proof/.../k8s/etcd3/Deep.lean`),
`cmp.Diff.spec_eventRefs`, `maps.Keys.spec_objMap` (with `slices.Sorted`), `maps.Clone.spec_strBool`,
`maps.Equal.spec_strBool`, `meta.SetList.spec_objList`, `apierrors.SuggestsClientDelay.spec`
(proposed), and the proposed in-place changes V (`.plain` widened to nil and non-`APIStatus`
wrappers) and T (`IsTooManyRequests.spec` over views, under `apiErrOk`). An independent attack run by
etcd-grove-03 (the `axiom` skill); its Go counterexample: `/shared/tmp/k8s7g-attack/gocx/attack_test.go`
(`TestLaterView`).

**Verdict.**
- **Survive:** `DeepEqual.spec_k8s`, `cmp.Diff.spec_eventRefs`, `maps.Keys`/`Clone`/`Equal`,
  `meta.SetList`, V and T. Their axioms are added on `k8s-7g` (`Proof/reflect/DeepEqualK8s.lean`,
  `Proof/github_com/google/go_cmp/cmp/Diff.lean`, `Proof/maps/{Keys,Clone,Equal}.lean`,
  `Proof/k8s_io/apimachinery/pkg/api/meta/SetList.lean`). M2 for V: its header must say that the
  `□ WP` premise on `Unwrap` is where typed-nil receivers (nil embedded ones included) are excluded.
- **Refuted (Go side):** `SuggestsClientDelay.spec` as proposed, and the **existing axiom
  `apierrors.HasStatusCause.wp_proof`**: `apiErrOk`'s `*StatusError` branch holds the struct `↦□`
  but not `*st.Details` and its causes, and the post (`□ ∀ w, apiErrAt err w -∗ …`) applies to a
  view the client builds after the call. Go: `HasStatusCause` returns false, the client then adds
  the cause to the details and persists them, builds the view, and the proof concludes `true`; the
  program's `if !b { panic }` panics. The same of `SuggestsClientDelay` with `RetryAfterSeconds`.
- **Fix (a), chosen by the user:** `apiErrOk`'s `*StatusError` branch also holds the details and
  causes `↦□` (`statusDetailsAt`), so every later view agrees (also removes M1, the unheld read).
  It lands with T as a separate soundness stage; `SuggestsClientDelay.spec` is restated over the
  fixed `apiErrOk` on `k8s-7g` after it lands.
