/-
`maps.Clone(m)` (names-only here) on a non-nil `map[string]bool` (the D30g patch's
`maps.Clone(s.NeedsRewrite)` in `Model.Clone`): a fresh map with the same entries; `m` only read.
Stated at this one map type (`spec_strBool`; the map points-to is not indexed by the Go type). Its
axiom will be `maps.Clone.wp_proof_strBool` (k8s 7g, `notes/k8s-7g-trust.md`), until Perennial
translates `maps` (`notes/perennial-changes.md`, "Generic maps and slices iterators").

Faithful (go1.27.3, `maps/maps.go`): `Clone(m)` returns `nil` if `m == nil` (excluded: the points-to
holds a cell at `m`, `ownMap_not_nil`), else `clone(m)` (the runtime's `maps.clone`), a new map with
`m`'s entries; the caller owns it alone (no other reference to it exists). Go evidence:
`examples/k8s/etcd3/trustspecs_test.go` `TestMapsCloneEqual` (5000 random maps: the same entries; a
write to the clone is not seen in `m`; an empty non-nil map's clone is non-nil). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Base
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev maps.Clone.spec_strBool : Prop :=
  ∀ (m : Loc) (M : GMap GoString Bool) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.maps ∗ m ↦${dq} M }}
    (App (Val #(functions _root_.Perennial.maps.Clone
      [go.GoType.MapType go.string go.bool, go.string, go.bool])) (Val #m))
  {{ (m' : Loc), RET #m'; m ↦${dq} M ∗ m' ↦$ M }}

end spec

end EtcdGrove
end Perennial
