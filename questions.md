# Stage 7b: questions and decisions pending the user

Per `notes/spec-first-plan.md` ("Proceed with a veto", "Questions do not block"): each entry is
decided by the agent with its recommendation and work continues; the user may veto. Hard stops are
marked.

## D1. `GuaranteedUpdate.spec` with a cached object: the scope premise, extended to `tryUpdate` (pending the user; a premise on an exported statement)

Review round 1 (F1): the cached no-op path (`store.go:552-575`) re-reads and returns or rewrites
without re-running the preconditions or `tryUpdate` on the re-read state, so the spec is false
unless, for a cached object, (i) there is no RV precondition (the user's choice (a), so far only in
the traffic) and (ii) `tryUpdate` does not depend on the resource version (the registry's `Update`
does: the same bug, `issues/k8s-etcd3-cached-noop-skips-preconditions.md`, "Impact").
- **Decided by the agent:** a pure conjunct of `GuaranteedUpdate.spec`'s precondition,
  `⌜∀ o r, ca = some (o, r) → p.rv = none ∧ ∀ n, f o n = f o (uint.nat r)⌝`; the driver discharges
  it (`genFrom` sends no RV precondition with a cached object; `updD` ignores the revision).
- Alternative: only (i) and a narrower (ii), `f o r = .ok o' → c.S.encode o' = c.S.encode o →
  ∀ n, f o n = .ok o'` (only the no-op matters). More precise, harder to read.
- Depends on it: `store.GuaranteedUpdate.spec`, the driver's `call` glue.

## D2. Cached objects of another key: a history keyed by revision (decided by the agent, pending the user)

Review round 1 (F2): `genFrom` (as `TestCorrectness`) attaches the client's cached object to an
operation on any key, so the driver must give `versionAt c K r o` for a key `K` other than the
cached object's. True (each revision changes one key here), but the history `(key, rev) ↦ value`
cannot say a revision did not change `K`.
- **Decided by the agent:** the history keyed by revision, `rev ↦□ changes` (each key the revision
  wrote, `some value`, or deleted, `none`; distinct keys), so `kvSeen σ` is "each key-value of `σ`
  is among its revision's changes". A witness for a revision whose changes are only key `k` gives
  `versionAt` for every other key vacuously. Store specs unchanged in form (`kvSeen`, `versionAt`);
  `History.lean`, `Seed.lean`, the driver's invariant change. Keeps the test's traffic.
- Alternative: `genFrom` attaches a cached object only to an operation on its own key (as
  `CacheDelegator` does in production): a deviation from the approved traffic.

## D3. `meta.Accessor.spec`: one spec, generalized (decided by the agent, pending the user)

`Spec/k8s_io/apimachinery/pkg/api/meta/Accessor.lean` exists (the DaemonSet track's named
hypothesis, for its four API pointer types, "boundary pending approval"). `Preconditions.Check`
needs it for any type in `metav1.Object`'s type set. `meta.Accessor` is now translated (7b).
- **Decided by the agent:** generalize the existing spec in place (no second family): `∀ ii,
  typeSetContains ii.ty metav1.Object.ty = true → Accessor(.ok ii) = (.ok ii, nil)`, proved from
  the body; `RealPodControl.createPods` (its one user) gives the type-set fact for
  `*apps.DaemonSet`. The DaemonSet's `?` hypothesis becomes a proved callee.
- Alternative: keep the DaemonSet's spec and give `Check` a separate lemma (a second family: not
  allowed without the user).

## N1. `fmt.SprintfNamed`: a hazard the axiom attack noted (no action proposed in 7b)

The `axiom` skill found the extended list sound (`notes/audit.md`). It noted that the named branch
of `fmt.SprintfArgOk` does not ask the value to have its type's shape (a `LeaseID` holding a
non-`w64` would make the post `False`); unreachable by Go's typing. Narrowing it is a change to a
trusted statement (a hard stop): left for the user, not done.
