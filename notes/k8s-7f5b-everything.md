# k8s 7f-5b H2: `storage.Everything` (trust-base texts for review)

Decided by etcd-grove-02, 2026-11-16 (worktree `questions.md`, "H2"): (a) + (b) + (c). `createWatchChan`
(`watcher.go:176-179`) replaces an empty predicate by the global `storage.Everything`, which `transform`
then reads through `wc.internalPred` (`filter`: `Empty()`, then `Matches` only if not empty; `acceptAll`:
`Empty()`). Today `fields.Everything.spec` says nothing of its result and the storage package fact
records nothing of `Everything`, so its `Empty()` is unprovable.

Go at the pins (k8s.io/apimachinery `0b7d352f711c`, k8s.io/apiserver `9c4ec15b8038`):

- `fields/selector.go:76` `func Everything() Selector { return andTerm{} }`; `:190` `andTerm.Empty`:
  `t == nil` or `len == 0` gives `true`.
- `storage/interfaces.go:101` `var Everything = SelectionPredicate{Label: labels.Everything(), Field:
  fields.Everything()}`; `selection_predicate.go:149` `Empty() = !ShardingEnabled() && labelFieldEmpty()`,
  `ShardingEnabled` false for a nil `ShardSelector`.
- Evidence: `examples/premisefix/watcherctx/everything_test.go` (`TestFieldsEverythingEmpty`,
  `TestStorageEverythingValue`), passing with `-race`.

## (a) `fields.Everything.spec` (trusted: the axiom `fields.Everything.wp_proof`), old → new

Old (`Spec/k8s_io/apimachinery/pkg/fields/Everything.lean`):
```lean
abbrev fields.Everything.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.fields.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.fields.Selector), RET #s; True }}
```
New (as `labels.Everything.spec`, without its `MatchesNothing` clause):
```lean
abbrev fields.Everything.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.fields.Everything)) (Val #()))
  {{ (s : k8s_io.apimachinery.pkg.fields.Selector), RET #s; ∃ i : GoInterfaceOk, ⌜s = interface.ok i⌝ ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }} }}
```

New file header (review finding 1):
```
`fields.Everything()` (`k8s.io/apimachinery/pkg/fields`, `selector.go:76`, names-only here): it
returns `andTerm{}` (a non-nil, length-0 value of the slice type `andTerm`); the spec says it
returns a non-nil `Selector` whose `Empty()` is `true` (`andTerm.Empty`, value receiver,
`selector.go:190`: `true` on `nil` or length 0, before its loop; pure, so the triple is
persistent), for `storage.Everything` (`storageInit`, 2026-11-16, k8s 7f-5b H2). Evidence:
`examples/premisefix/watcherctx/everything_test.go`. The trust boundary: an axiom,
`Proof/k8s_io/apimachinery/pkg/fields/Everything.lean`. Lean-first (no Rocq counterpart).
```

## (b) The storage package fact (`storageInit`, `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`)

Proved by the generated `Proof/k8s_io/apiserver/pkg/storage/Init.lean` (`etc/gen-init.py`'s SPECIAL for
`k8s_io.apiserver.pkg.storage`: keep the two `Everything.wp_proof` posts, `ipersist HEverything` after the
translated initializer's store), not assumed; its text is in the statement of every result through
`isPkgInit`. Old:
```lean
abbrev storageInit : IProp GF :=
  iprop(∃ rw tl : GoString, globalAddr k8s_io.apiserver.pkg.storage.RequestWatchProgress ↦□ rw ∗
    globalAddr k8s_io.apiserver.pkg.storage.tooLargeResourceVersionCauseMsg ↦□ tl)
```
New:
```lean
/-- **`storage.Everything`'s value** (persistent): no shard selector, and a label and a field selector
whose `Empty()` is `true` (`labels.Everything()`, `fields.Everything()`). -/
def everythingOk (p : k8s_io.apiserver.pkg.storage.SelectionPredicate) : IProp GF :=
  iprop(⌜p.ShardSelector' = GoInterface.nil⌝ ∗
    (∃ i : GoInterfaceOk, ⌜p.Label' = interface.ok i⌝ ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }}) ∗
    (∃ i : GoInterfaceOk, ⌜p.Field' = interface.ok i⌝ ∗
      {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }}))

abbrev storageInit : IProp GF :=
  iprop(∃ (rw tl : GoString) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate),
    globalAddr k8s_io.apiserver.pkg.storage.RequestWatchProgress ↦□ rw ∗
    globalAddr k8s_io.apiserver.pkg.storage.tooLargeResourceVersionCauseMsg ↦□ tl ∗
    globalAddr k8s_io.apiserver.pkg.storage.Everything ↦□ p ∗ everythingOk p)
```
The read-only points-to is taken at initialization from the whole points-to. No code writes
`storage.Everything`: in the translation, its one reader is `etcd3/watcher.go:178` (`etcd3.lean:9633`, a
load); in all of k8s.io at the pins (tests included) and in `examples/`, every use copies it (`grep` for
assignments and `&storage.Everything`: none). The untranslated side is the only part of (b)'s soundness
the logic does not check (review finding 2).

## (c) Internal (a form): `selPredOkW`

`transform`/`filter`/`acceptAll` take `selPredOkW S p sel emp` (`selPredOk` with the `Matches` triple only
when `emp = false`), with a law from `selPredOk` and one for `Everything` (`sel := fun _ => true`,
`emp := true`) from `everythingOk`, proving `SelectionPredicate.Empty` on it from the code
(`ShardingEnabled` short-circuits on the nil selector; `labelFieldEmpty` calls the two `Empty`s).

## Review

`/shared/tmp/k8s7f5b/axiom-review-everything.md` (an independent `axiom`-skill review, 2026-11-16): READY WITH
CHANGES, no counterexample; (a) and (b) unchanged. Findings (both minor, documentation): (1) the spec file's header
(new header above); (2) (b)'s soundness note named an untranslated reader (reworded above). Both applied.
