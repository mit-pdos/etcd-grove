/-
`EnsureNamedFieldsAreMembers` at an optional type: `ensureNamedOpt S ty s`, the set `s` with
every declared field of a map type that has a path below it made a member, the type along the
paths starting at `ty` (`none`: the empty `schema.TypeRef{}`, which resolves to the zero atom: no
field is named). `ensureNamed S t s` (`typed/Defs.lean`) is its instance at `some t`
(`ensureNamed_opt`). Draft (2026-11-19, notes/smd-plan.md).

It imports `typed/Defs.lean` for `namedAlong`/`childType`, which are about paths and schemas only:
they belong in `fieldpath` (or `schema`); requested in the Draft's report, with `ensureNamed`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

/-- `s` and the named fields along its paths, the type along them starting at `ty`. -/
def ensureNamedOpt (S : Schema) (ty : Option TypeRef) (s : PathSet) : PathSet :=
  FSet.union s (FSet.bind (namedAlong S [] ty) s)

/-- At a named type, `ensureNamed`. -/
def ensureNamed_opt.law : Prop :=
  ∀ S t s, ensureNamed S t s = ensureNamedOpt S (some t) s

/-- The children part: the paths below `e` of the result are those of the child's set at the
child's type (`SetNodeMap.EnsureNamedFieldsAreMembers`' recursion). -/
def ensureNamedOpt_under.law : Prop :=
  ∀ S ty s e, (ensureNamedOpt S ty s).under e = ensureNamedOpt S (childType S ty e) (s.under e)

/-- The members part: a one-element path of the result is one of `s`, or a declared field of the
map type at `ty` with a path of `s` below it. -/
def ensureNamedOpt_tops.law : Prop :=
  ∀ S ty s e, e ∈ (ensureNamedOpt S ty s).tops ↔ e ∈ s.tops ∨ (e ∈ s.heads ∧
    ∃ n fs el rel, e = .field n ∧ ty.bind (fun t => S.find t.name) = some (.map fs el rel) ∧
      (lookupKV n fs).isSome)

end smd
end EtcdGrove
end Perennial
