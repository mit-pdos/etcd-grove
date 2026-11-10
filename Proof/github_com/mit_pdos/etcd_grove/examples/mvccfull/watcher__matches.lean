/- Lean-first (no Rocq counterpart). The proof of `watcher.matches` (the range, then the filter). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem watcher.matches.wp_proof
    (wp_inRange : inRange.spec (GF := GF) (hG := hG)) :
    watcher.matches.spec (GF := GF) (hG := hG) := by
  intro w wv dq dk de kk e ch
  wp_start as ⟨Hw, Hk, He⟩
  icases (typedPointsto_not_null_dup _ _ _) $$ Hw with ⟨Hw, %Hwn⟩
  iStructNamedSuffix Hw "W"
  wp_auto
  wp_apply wp_inRange wv.key' wv.end' kk e ch.key' dk de $$ [$Hk $He] as ⟨Hk, He⟩
  ihave Hw : w.[watcher, go!"filter"] ↦{dq} wv.filter' ∗
      (w.[watcher, go!"filter"] ↦{dq} wv.filter' -∗ w ↦{dq} wv)
    $$ [keyW end'W filterW startW floatLoW revW indexW stampedW cancelledW compactedW]
  · iframe filterW
    iintro filterW
    iapply typedPointsto_combine w _ dq Hwn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  icases Hw with ⟨filterW, Hback⟩
  iStructNamedSuffix ch "C"
  unfold matchesM filtOk
  cases hin : inRangeM (decide (wv.end' = slice.nil)) kk e ch.key'
  · (try wp_auto)
    iapply HΦ
    iframe
    iapply Hback $$ filterW
  (try wp_auto)
  cases hdel : ch.del'
  all_goals
    (try wp_auto)
    simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte, decide_not]
    iapply HΦ
    ihave Hw := Hback $$ filterW
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
