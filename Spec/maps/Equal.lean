/-
`maps.Equal(m1, m2)` on two non-nil `map[string]bool` (the D30g patch's
`maps.Equal(s.NeedsRewrite, other.NeedsRewrite)` in `Model.Equal`): whether they have the same
entries; both only read. Stated at this one map type (`spec_strBool`). Proved (2026-11-23,
`Proof/maps/Equal.lean`) from Perennial's translation of `maps` and its generic spec
(`maps.wp_Equal`, Perennial `70706ce5e`); until then a trust-boundary axiom (k8s 7g,
`notes/k8s-7g-trust.md`). Both maps non-nil (the points-tos); a nil and an empty map are `Equal` in
Go, outside the spec. The `isPkgInit pkg_id.maps` premise is no longer needed by the proof.
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
abbrev maps.Equal.spec_strBool : Prop :=
  ∀ (m1 m2 : Loc) (M1 M2 : GMap GoString Bool) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.maps ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }}
    (App (App (Val #(functions _root_.Perennial.maps.Equal
      [go.GoType.MapType go.string go.bool, go.GoType.MapType go.string go.bool, go.string,
        go.bool])) (Val #m1)) (Val #m2))
  {{ (b : Bool), RET #b; ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 }}

end spec

end EtcdGrove
end Perennial
