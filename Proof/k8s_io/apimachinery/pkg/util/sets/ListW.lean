/-
`List(s)` of a set of decision words (`Set[authorizer.Decision]`): a new slice of its items.
Lean-first; the second spec of `List` (the first, `List.lean`, is for strings), for the
conditional authorizer's failure messages. Its proof, over `UnsortedList` and `slices.Sort`;
`cmp.Less` at `Decision` (whose underlying type is `int`; Perennial's `cmp.Less.spec` covers only
`uint64` and `string`) is proved here from its code: signed `<`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.ListW
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Perennial.Spec.slices.Sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- At `Decision` (an integer type), `cmp.isNaN` is `false`. -/
theorem wp_isNaN_decision (x : w64) :
    {{ (True : IProp GF) }}
      (App (Val #(functions _root_.Perennial.cmp.isNaN
        [_root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty])) (Val #x))
    {{ RET #false; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro
  trivial

/-- At `Decision` (underlying `int`), `cmp.Less` is signed `<`. -/
theorem wp_Less_decision (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions _root_.Perennial.cmp.Less
        [_root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty])) (Val #x))
        (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ sint.Z x < sint.Z y⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_isNaN_decision
  iapply HΦ
  ipureintro
  simp

theorem lessImplements_decision :
    ⊢ _root_.Perennial.slices.lessImplements (GF := GF)
        (Et := _root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty)
        (fun (x y : w64) => sint.Z x < sint.Z y) := by
  unfold _root_.Perennial.slices.lessImplements
  iintro %x %y
  imodintro
  iintro %Φ _ HΦ
  wp_apply wp_Less_decision x y with %b %Hb
  iapply HΦ
  ipureintro
  exact Hb

theorem List'.wp_proofW (wp_UnsortedList : Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Sort : _root_.Perennial.slices.Sort.spec (GF := GF) (hG := hG)) :
    List'.specW (GF := GF) (hG := hG) := by
  intro m dq s hsz
  wp_start as Hm
  ihave #Hsl : isPkgInit (PROP := IProp GF) pkg_id.slices $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_UnsortedList (T := _root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty) $$ [$Hm] as %sl %ks ⟨Hm, Hks, %Hk⟩
  (try wp_auto)
  ihave #Hless := lessImplements_decision (GF := GF)
  wp_apply wp_Sort (fun (x y : w64) => sint.Z x < sint.Z y) sl ks
      _root_.Perennial.slices.StrictWeakOrder_signed_lt $$ [Hks]
    with %ks' ⟨Hks, %Hperm, %Hsorted⟩
  · iframe Hks; iframe #; ipureintro; rw [Hk.2.2]; exact hsz
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro
  intro k
  rw [← Hk.1 k]; exact Hperm.mem_iff.symm

end proof

end sets
end EtcdGrove
end Perennial
