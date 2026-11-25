/-
The proof of `Enc.Bool` (`Spec/.../dist/enc/Enc__Bool.lean`): one append, of `1` or `0`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Bool
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Lemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Assumptions]

theorem Enc.Bool.wp_proof : Enc.Bool.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  unfold ownEnc
  icases He with ⟨%s, He, Hs, Hcap⟩
  wp_auto
  cases x <;>
  · try simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hlit] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iexists s'
    iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
