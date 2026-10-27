/-
Proof of `Spec/k8s_io/client_go/util/consistency/ConsistencyError__Error.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.ConsistencyError__Error
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    wp_apply (fmt.wp_Sprintf _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
      (_root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))) $$ [$Hl1]
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
    wp_apply (fmt.wp_Sprintf _ _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
      (_root_.Perennial.fmt.ArgsWf.cons_string _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
        _root_.Perennial.fmt.ArgsWf.nil)))) $$ [$Hl1] as %s -
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end consistency
end EtcdGrove
end Perennial
