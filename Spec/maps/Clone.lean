/-
`maps.Clone(m)` on a non-nil `map[string]bool` (the D30g patch's `maps.Clone(s.NeedsRewrite)` in
`Model.Clone`): a fresh map with the same entries; `m` only read. Stated at this one map type
(`spec_strBool`), as the checker's proofs use it. Proved (2026-11-23, `Proof/maps/Clone.lean`) from
Perennial's translation of `maps` and its generic spec (`maps.wp_Clone`, Perennial `70706ce5e`);
until then a trust-boundary axiom (k8s 7g, `notes/k8s-7g-trust.md`). The `isPkgInit pkg_id.maps`
premise is no longer needed by the proof; it stays so that callers' statements are unchanged.
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
