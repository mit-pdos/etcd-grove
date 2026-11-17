/-
`delete(m, k)` on a map of the named type `pidSet` (`hashMap.delSpan`'s
`delete(f.freemaps[size], start)`). Perennial's `delete_map` now takes any type whose underlying
type is a map (`[t ↓u go.MapType ..]`, Perennial `542338360`, as `len_map` does), so
`wp_mapDelete_underlying` gives the WP at `pidSet` (`pidSetDelete_holds`). Until stage S1 of
`notes/bbolt-integration-plan.md` (2026-11-17) `PidSetDeleteUnfold` was the missing unfolding,
taken as a hypothesis of bbolt's linked results; it is now the WP itself, proved; the proofs still
take it as an argument (`FLCallees`), given by `pidSetDelete_holds`.
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
