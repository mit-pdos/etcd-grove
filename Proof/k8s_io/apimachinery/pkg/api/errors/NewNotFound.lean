/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewNotFound.lean`: the details, the message (`fmt.Sprintf` of the resource's `String()` and the name), the status literal. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem NewNotFound.wp_proof
    (wp_String : schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)) :
    NewNotFound.spec (GF := GF) (hG := hG) := by
  intro gr name
  wp_start
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_String $$ [$qualifiedResource] as %str qualifiedResource
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  iapply wp_fupd
  -- `%q` of the name (`fmt-stage15`): some string
  wp_apply (_root_.Perennial.fmt.Sprintf_pure_of _root_.Perennial.fmt.wp_Sprintf go!"%s %q not found" [.dir none _root_.Perennial.fmt.verb_s, .lit go!" ", .dir none _root_.Perennial.fmt.verb_q, .lit go!" not found"] _ _ _ (DFrac.own 1)
      (by fmt_encode) ?fits ?pa)
    $$ [$Hasl] as %s -
  case pa =>
    (try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]); (try simp only [List.set_cons_succ, List.set_cons_zero])
    exact .str _ _ _ (.str _ _ _ .nil)
  case fits => fmt_fits
  ipersist «$v3»
  imodintro
  iapply HΦ
  iexists _
  iframe
  isplitr
  · unfold statusDetailsAt; iright; iexists _; iframe «$v3»
    iapply (ownSlice_nil (V := k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) DFrac.discard)
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
