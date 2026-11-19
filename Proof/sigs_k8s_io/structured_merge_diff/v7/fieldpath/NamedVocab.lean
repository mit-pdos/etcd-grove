/-
`EnsureNamedFieldsAreMembers` at an optional type: `ensureNamedOpt S ty s`, the set `s` with
every declared field of a map type that has a path below it made a member, the type along the
paths starting at `ty` (`none`: the empty `schema.TypeRef{}`, which resolves to the zero atom: no
field is named). `ensureNamed S t s` (`typed/Defs.lean`) is its instance at `some t`
(`ensureNamed_opt`). Draft (2026-11-19, notes/smd-plan.md).

`childType`, `typeAlong`, `namedAlong` and `ensureNamed`, about paths and schemas only, are here
(moved from `typed/Defs.lean` at the Draft's integration, 2026-11-19, so that `fieldpath` does not
import `typed`).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

/-- The type of a set's child node (`SetNodeMap.EnsureNamedFieldsAreMembers`): a map's field
(or its element type), a list's keyed item; otherwise none. -/
def childType (S : Schema) (t : Option TypeRef) (pe : PE) : Option TypeRef :=
  match t.bind (fun t => S.find t.name), pe with
  | some (.map fs e _), .field n => fieldType fs e n
  | some (.list e _ _), .key _ => some e
  | _, _ => none

/-- The type at a path, as `EnsureNamedFieldsAreMembers` descends. -/
def typeAlong (S : Schema) (t : Option TypeRef) : Path → Option TypeRef
  | [] => t
  | pe :: p => typeAlong S (childType S t pe) p

/-- The prefixes `acc ++ q'` of `acc ++ q` that end in a declared field of a map type (the type
along `acc` being `ty`) and have a path below them (`q'` a strict prefix of `q`). -/
def namedAlong (S : Schema) (acc : Path) (ty : Option TypeRef) : Path → List Path
  | [] => []
  | pe :: r =>
    (if r.isEmpty then [] else
      match ty.bind (fun t => S.find t.name), pe with
      | some (.map fs _ _), .field n => if (lookupKV n fs).isSome then [acc ++ [pe]] else []
      | _, _ => []) ++ namedAlong S (acc ++ [pe]) (childType S ty pe) r

/-- **`ensureNamed S t s`**: `s` and every declared field of a map type with a path of `s` below
it (`Set.EnsureNamedFieldsAreMembers`): `q = p ++ [.field n]` is added when some `q ++ r`
(`r ≠ []`) is in `s` and the type along `p` is a map declaring `n` (`ensureNamed_mem`). -/
def ensureNamed (S : Schema) (t : TypeRef) (s : PathSet) : PathSet :=
  FSet.union s (s.bind (namedAlong S [] (some t)))

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
