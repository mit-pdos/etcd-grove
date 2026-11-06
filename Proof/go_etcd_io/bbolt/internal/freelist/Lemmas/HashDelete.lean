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

/-- `delete` at `pidSet` unfolds as at its underlying map type. -/
def PidSetDeleteUnfold : Prop :=
  #(functions go.delete [pidSet.ty]) =
    #(functions go.delete [go.MapType go_etcd_io.bbolt.internal.common.Pgid.ty (go.StructType [])])

/-- `delete(m, k)` on a `pidSet`. -/
theorem wp_mapDelete_pidSet (hdel : PidSetDeleteUnfold (GF := GF)) (l : Loc) (m : GMap w64 Unit)
    (k : w64) :
    {{ (l ↦$ m : IProp GF) }}
      (App (App (Val #(functions go.delete [pidSet.ty])) (Val #l)) (Val #k))
    {{ RET #(); l ↦$ (GMap.delete k m) }} := by
  unfold PidSetDeleteUnfold at hdel
  rw [hdel]
  exact wp_mapDelete l m k _ _

end

end bbolt
end EtcdGrove
end Perennial
