/-
Proof of `Spec/k8s_io/client_go/util/consistency/ConsistencyError__Error.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.ConsistencyError__Error
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem ConsistencyError.Error.wp_proof
    (wp_String : schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)) :
    ConsistencyError.Error.spec (GF := GF) (hG := hG) := by
  intro l dq e
  wp_start as He
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave %Hnn := typedPointsto_not_null $$ He
  iStructNamed He
  wp_auto
  wp_if_destruct
  · wp_apply (wp_String _ dq e.GroupResource') $$ [$GroupResource] as %str GroupResource
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_auto
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
      List.set_cons_succ, List.set_cons_zero]
    wp_apply (fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"read version is not synced (written version: %s) for group resource %s"
      [.lit go!"read version is not synced (written version: ", .dir none _root_.Perennial.fmt.verb_s, .lit go!") for group resource ", .dir none _root_.Perennial.fmt.verb_s]
      _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil))) $$ [$Hl1]
      as %s -
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · wp_apply (wp_String _ dq e.GroupResource') $$ [$GroupResource] as %str GroupResource
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    wp_auto
    simp only [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl,
      List.set_cons_succ, List.set_cons_zero]
    wp_apply (fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"read version: %s is not as new as written version: %s for group resource %s"
      [.lit go!"read version: ", .dir none _root_.Perennial.fmt.verb_s, .lit go!" is not as new as written version: ", .dir none _root_.Perennial.fmt.verb_s, .lit go!" for group resource ", .dir none _root_.Perennial.fmt.verb_s]
      _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ (.str _ _ _ .nil)))) $$ [$Hl1] as %s -
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end consistency
end EtcdGrove
end Perennial
