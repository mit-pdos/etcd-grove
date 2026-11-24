/-
The authorizer package's values as `fmt` arguments (2026-11-20): a `Decision` under `%v`/`%s`
(its `String()`, proved: `Decision.String.spec`): what the union authorizer's
`fmt.Errorf("evaluated to decision %s, but only [%s] were possible", ...)` passes. (Until 2026-11-24
also a read-only `[]Decision` under the same, for the axioms `fmt.SprintfSlice`/`fmt.ErrorfSlice`,
retired: the fork now spells the slice out.) Lean-first.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.Decision__String
public import Spec.fmt.Errorf
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

/-- A `Decision` is `fmt.argOk`: its `String()` returns some string needing nothing more than the
package's initialization; its type has `String() string` and neither `Format` nor `Error`. -/
theorem Decision.argOk (wp_String : Decision.String.spec (GF := GF) (hG := hG)) (k : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ⊢
      fmt.argOk (interface.mkOk Decision.ty #k) := by
  iintro #Hpkg
  unfold fmt.argOk
  iright; iright
  isplitr
  · unfold fmt.stringMethodSpec
    iintro !> %Φ HΦ
    iapply (wp_String k)
    · iexact Hpkg
    · inext; iintro %s -; iapply HΦ
  · ipureintro
    simp only [interface.mkOk]
    fmt_method_facts

/-- A `Decision` is `fmt.argOkAtBase` a method-verb directive other than `%#v` and `%w`. -/
theorem Decision.argOkAtBase (wp_String : Decision.String.spec (GF := GF) (hG := hG)) (k : w64)
    {mv : List w8} {d : fmt.Directive} (hd : d.verb ∈ mv ∧ d.sharpV = false ∧ d.verb ≠ W8 119) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ⊢
      fmt.argOkAtBase mv d (interface.mkOk Decision.ty #k) := by
  iintro #Hpkg
  unfold fmt.argOkAtBase
  iright; iright
  isplitr
  · ipureintro; exact ⟨hd.1, hd.2.1, fun hw => absurd hw hd.2.2⟩
  · iapply Decision.argOk wp_String k
    iexact Hpkg

end lemmas

end authorizer
end EtcdGrove
end Perennial
