/- Lean-first (no Rocq counterpart). The proof of `checkKV`: each comparison holds by
`kvMatches`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkKV

@[expose] public section

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

theorem checkKV.wp_proof (wp_check : check.spec (GF := GF) (hG := hG)) :
    checkKV.spec (GF := GF) (hG := hG) := by
  intro p v dq dk dv kk vv k e keysOnly hm
  obtain ⟨hk, hc, hmo, hv, hval⟩ := hm
  wp_start as ⟨Hp, Hk, Hv⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hp
  wp_auto
  wp_apply wp_bytes_to_string v.Key' kk dk $$ [$Hk] as Hk
  subst hk
  (try wp_auto)
  wp_apply wp_check
  · itrivial
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp [hc]
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp [hmo]
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp [hv]
  (try wp_auto)
  cases keysOnly
  · simp only [Bool.false_eq_true, ↓reduceIte] at hval
    obtain ⟨rfl, hl⟩ := hval
    (try wp_auto)
    wp_apply wp_bytes_to_string v.Value' _ dv $$ [$Hv] as Hv
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [hl]
    (try wp_auto)
    iapply HΦ; iframe
  · simp only [↓reduceIte] at hval
    subst hval
    ihave %Hvl := ownSlice_len $$ Hv
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp at Hvl; simp; word
    (try wp_auto)
    iapply HΦ; iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
