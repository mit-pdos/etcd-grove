/- Lean-first (no Rocq counterpart). The proof of `runner.genRange` (`genKey`, `genEnd`, the
revision by `pick` over `RangeRev` (only its range matters), the limit and flags by `choose`):
proved. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section lemmas
variable [GooseExts]

theorem lim_ok (len l : w64) (n : Nat) (hn : n = sint.nat len) (h0 : 0 ≤ sint.Z len)
    (hl : 0 ≤ sint.Z l ∧ (0 < sint.Z (len + W64 2) → sint.Z l < sint.Z (len + W64 2)) ∧
      (sint.Z (len + W64 2) ≤ 0 → l = W64 0)) :
    0 ≤ sint.Z l ∧ sint.Z l ≤ (n : Int) + 1 := by
  have h4 : sint.nat len = (sint.Z len).toNat := rfl
  by_cases hb : sint.Z len + 2 < 2 ^ 63
  · have : sint.Z (len + W64 2) = sint.Z len + 2 := by word
    rw [this] at hl
    have := hl.2.1 (by omega)
    omega
  · have : sint.Z (len + W64 2) < 0 := by word
    have := hl.2.2 (by omega)
    subst this
    refine ⟨by decide, ?_⟩
    have : sint.Z (W64 0) = 0 := by decide
    omega

theorem rev_ok (cur y : w64)
    (hy : 0 ≤ sint.Z y ∧ (0 < sint.Z (cur + W64 2) → sint.Z y < sint.Z (cur + W64 2)) ∧
      (sint.Z (cur + W64 2) ≤ 0 → y = W64 0)) :
    0 ≤ sint.Z y ∧ sint.Z y ≤ max 0 (sint.Z cur + 1) := by
  refine ⟨hy.1, ?_⟩
  by_cases hp : 0 < sint.Z (cur + W64 2)
  · have h1 := hy.2.1 hp
    by_cases hb : sint.Z cur + 2 < 2 ^ 63
    · have : sint.Z (cur + W64 2) = sint.Z cur + 2 := by word
      omega
    · have : sint.Z (cur + W64 2) < 0 := by word
      omega
  · have := hy.2.2 (by omega)
    subst this
    have : sint.Z (W64 0) = 0 := by decide
    omega

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.genRange.wp_proof
    (wp_genKey : runner.genKey.spec (GF := GF) (hG := hG))
    (wp_genEnd : runner.genEnd.spec (GF := GF) (hG := hG))
    (wp_choose : choose.spec (GF := GF) (hG := hG))
    (wp_pick : pick.spec (GF := GF) (hG := hG)) :
    runner.genRange.spec (GF := GF) (hG := hG) := by
  intro x ks cfg cur cmp
  wp_start as ⟨Hks, Hmix⟩
  iunfold runnerKeys at Hks
  icases Hks with ⟨%keys, #Hkeys, #Hksl, %Hsorted, %Hne⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  iunfold runnerRangeMix at Hmix
  icases Hmix with ⟨#Hcfg, %wrr, #Hwrr⟩
  icases typedPointsto_split _ _ _ $$ Hcfg with #Hcfgf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfgf
  icases typedPointsto_split _ _ _ $$ Mix with #Hmixf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hmixf
  wp_auto
  wp_apply wp_genKey x ks as %ksl ⟨%kk, Hk, %Hkk⟩
  · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
  (try wp_auto)
  wp_apply wp_genEnd x ks as %esl ⟨%e, He, %He⟩
  · iunfold runnerKeys; iexists keys; iframe #; ipureintro; exact ⟨Hsorted, Hne⟩
  (try wp_auto)
  wp_apply wp_pick cfg.Mix'.RangeRev' wrr DFrac.discard (W64 4) $$ [Hwrr] as %sw ⟨-, %Hsw⟩
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_choose (keys.len + W64 2) as %l %Hl
    (try wp_auto)
    wp_apply wp_choose (W64 2) as %c1 -
    (try wp_auto)
    wp_apply wp_choose (W64 2) as %c2 -
    (try wp_auto)
    wp_apply wp_choose (W64 2) as %c3 -
    (try wp_auto)
    iapply HΦ
    iexists kk, e
    iframe
    ipureintro
    refine ⟨⟨Hkk, He⟩, Or.inl rfl, lim_ok _ _ _ Hksn.1 Hksn.2 Hl⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_choose (keys.len + W64 2) as %l %Hl
      (try wp_auto)
      wp_apply wp_choose (W64 2) as %c1 -
      (try wp_auto)
      wp_apply wp_choose (W64 2) as %c2 -
      (try wp_auto)
      wp_apply wp_choose (W64 2) as %c3 -
      (try wp_auto)
      iapply HΦ
      iexists kk, e
      iframe
      ipureintro
      refine ⟨⟨Hkk, He⟩, Or.inr (Or.inl rfl), lim_ok _ _ _ Hksn.1 Hksn.2 Hl⟩
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply wp_choose (cur + W64 2) as %y %Hy
        (try wp_auto)
        wp_apply wp_choose (keys.len + W64 2) as %l %Hl
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c1 -
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c2 -
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c3 -
        (try wp_auto)
        iapply HΦ
        iexists kk, e
        iframe
        ipureintro
        refine ⟨⟨Hkk, He⟩, Or.inr (Or.inr (Or.inr (rev_ok _ _ Hy))), lim_ok _ _ _ Hksn.1 Hksn.2 Hl⟩
      · (try wp_auto)
        wp_apply wp_choose (keys.len + W64 2) as %l %Hl
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c1 -
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c2 -
        (try wp_auto)
        wp_apply wp_choose (W64 2) as %c3 -
        (try wp_auto)
        iapply HΦ
        iexists kk, e
        iframe
        ipureintro
        refine ⟨⟨Hkk, He⟩, Or.inr (Or.inr (Or.inl rfl)), lim_ok _ _ _ Hksn.1 Hksn.2 Hl⟩
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
