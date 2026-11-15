/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/SelectionPredicate__Matches.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Matches
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__MatchesSharding
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__labelFieldEmpty
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__MatchesObjectAttributes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.SelectionPredicate.Matches.wp_proof
    (wp_MatchesSharding : storage.SelectionPredicate.MatchesSharding.spec (GF := GF) (hG := hG))
    (wp_labelFieldEmpty : storage.SelectionPredicate.labelFieldEmpty.spec (GF := GF) (hG := hG))
    (wp_MatchesObjectAttributes : storage.SelectionPredicate.MatchesObjectAttributes.spec (GF := GF) (hG := hG))
    : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG) := by
  intro O objAt pp dq p le fe lm fm lab fld x o hs
  wp_start as ⟨Hp, #Hl, #Hf, #Hg, Hx⟩
  (try wp_auto)
  wp_apply (wp_MatchesSharding pp dq p x hs) $$ [$Hp] as Hp
  (try wp_auto)
  wp_apply (wp_labelFieldEmpty pp dq p le fe lm fm) $$ [$Hp $Hl $Hf] as Hp
  cases hlf : (le && fe)
  · (try wp_auto)
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
    iStructNamed Hp
    (try wp_auto)
    iunfold getAttrsOk at Hg
    wp_bind
    iapply Hg $$ Hx
    inext
    iintro %lp %fp Hx #HL #HF
    (try wp_auto)
    ihave Hp : pp ↦{dq} p $$ [Label Field GetAttrs IndexLabels IndexFields Limit Continue AllowWatchBookmarks ShardSelector]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    (try wp_auto)
    wp_apply (wp_MatchesObjectAttributes pp dq p le fe lm fm lp fp (lab o) (fld o)) $$ [$Hp $Hl $Hf $HL $HF] as Hp
    (try wp_auto)
    rw [hlf]
    iapply HΦ
    iframe
  · (try wp_auto)
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
