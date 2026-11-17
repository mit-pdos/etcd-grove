/-
`delete(m, k)` on a map of the named type `pidSet` (`hashMap.delSpan`'s
`delete(f.freemaps[size], start)`): Perennial's map semantics unfolds `go.delete` only at a literal
map type (`MapSemantics.delete_map`, `[go.MapType key_type elem_type]`), where `len` takes any
type whose underlying type is a map (`len_map`, `[t ↓u go.MapType ..]`). So the call goose emits,
`delete [pidSet.ty]`, has no semantics, and no WP of it is provable. `PidSetDeleteUnfold` is the
missing rule at `pidSet` (the literal map type's unfolding, at the named type); the proofs that
need it take it as a hypothesis, until Perennial's `delete_map` is generalized as `len_map` was
(a Perennial change to propose: `notes/perennial-changes.md`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- **`delete(m, k)` on a `pidSet`** (what `hashMap.delSpan` needs). Until stage S1 of
`notes/bbolt-integration-plan.md` (2026-11-17) the unfolding of `delete` at `pidSet` to its
underlying map type, a gap of Perennial's semantics and a hypothesis of bbolt's linked results;
Perennial's `delete_map` now takes any `t ↓u go.MapType ..`, and `pidSetDelete_holds` proves it. -/
def PidSetDeleteUnfold : Prop :=
  ∀ (l : Loc) (m : GMap w64 Unit) (k : w64),
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [pidSet.ty])) (Val #l)) (Val #k))
    {{ RET #(); l ↦$ (GMap.delete k m) }}

/-- `delete` at `pidSet` is `delete` at its underlying map type (Perennial's
`wp_mapDelete_underlying`). -/
theorem pidSetDelete_holds : PidSetDeleteUnfold (GF := GF) := fun l m k =>
  wp_mapDelete_underlying (t := pidSet.ty) (key_type := go_etcd_io.bbolt.internal.common.Pgid.ty)
    (elem_type := go.StructType []) l m k

/-- `delete(m, k)` on a `pidSet`. -/
theorem wp_mapDelete_pidSet (hdel : PidSetDeleteUnfold (GF := GF)) (l : Loc) (m : GMap w64 Unit)
    (k : w64) :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [pidSet.ty])) (Val #l)) (Val #k))
    {{ RET #(); l ↦$ (GMap.delete k m) }} :=
  hdel l m k

end

end bbolt
end EtcdGrove
end Perennial
