/- Lean-first (no Rocq counterpart). The proof of `rng.genRange`: the key, the end, the options'
draws, then the revision's three arms. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem rng.genRange.wp_proof (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_genEnd : rng.genEnd.spec (GF := GF) (hG := hG)) :
    rng.genRange.spec (GF := GF) (hG := hG) := by
  intro r g cur hc0 hc2
  wp_start as Hr
  wp_auto
  wp_apply wp_genKey r g $$ [$Hr] as %ks ⟨⟨%g1, Hr⟩, %kk, Hks, Hkc, %Hkk⟩
  wp_apply wp_genEnd r g1 $$ [$Hr] as %es ⟨⟨%g2, Hr⟩, %e, Hes, Hec, %He⟩
  (try wp_auto)
  wp_apply wp_intn r g2 (W64 4) (by decide) $$ [$Hr] as %sw ⟨⟨%g3, Hr⟩, %Hsw⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_intn r g3 (W64 4) (by decide) $$ [$Hr] as %l ⟨⟨%gl, Hr⟩, %Hl⟩
    (try wp_auto)
    wp_apply wp_intn r gl (W64 5) (by decide) $$ [$Hr] as %c ⟨⟨%gc, Hr⟩, -⟩
    (try wp_auto)
    wp_apply wp_intn r gc (W64 4) (by decide) $$ [$Hr] as %f ⟨⟨%gf, Hr⟩, -⟩
    (try wp_auto)
    wp_apply wp_intn r gf (W64 2) (by decide) $$ [$Hr] as %w ⟨⟨%gw, Hr⟩, -⟩
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hkk, He.1, He.2, ?_, ?_, ?_, ?_⟩ <;> simp <;> word
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_intn r g3 (W64 4) (by decide) $$ [$Hr] as %l ⟨⟨%gl, Hr⟩, %Hl⟩
      (try wp_auto)
      wp_apply wp_intn r gl (W64 5) (by decide) $$ [$Hr] as %c ⟨⟨%gc, Hr⟩, -⟩
      (try wp_auto)
      wp_apply wp_intn r gc (W64 4) (by decide) $$ [$Hr] as %f ⟨⟨%gf, Hr⟩, -⟩
      (try wp_auto)
      wp_apply wp_intn r gf (W64 2) (by decide) $$ [$Hr] as %w ⟨⟨%gw, Hr⟩, -⟩
      (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hkk, He.1, He.2, ?_, ?_, ?_, ?_⟩ <;> simp <;> word
    · (try wp_auto)
      wp_apply wp_intn r g3 (cur + W64 2) (by word) $$ [$Hr] as %y ⟨⟨%g4, Hr⟩, %Hy⟩
      (try wp_auto)
      wp_apply wp_intn r g4 (W64 4) (by decide) $$ [$Hr] as %l ⟨⟨%gl, Hr⟩, %Hl⟩
      (try wp_auto)
      wp_apply wp_intn r gl (W64 5) (by decide) $$ [$Hr] as %c ⟨⟨%gc, Hr⟩, -⟩
      (try wp_auto)
      wp_apply wp_intn r gc (W64 4) (by decide) $$ [$Hr] as %f ⟨⟨%gf, Hr⟩, -⟩
      (try wp_auto)
      wp_apply wp_intn r gf (W64 2) (by decide) $$ [$Hr] as %w ⟨⟨%gw, Hr⟩, -⟩
      (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      refine ⟨Hkk, He.1, He.2, ?_, ?_, ?_, ?_⟩ <;> simp <;> word

end proof

end mvccrand
end EtcdGrove
end Perennial
