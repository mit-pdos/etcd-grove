/-
The proof of `Dec.Int` (`Spec/.../dist/enc/Dec__Int.lean`): a call of `U64`, the value converted (a no-op on `w64`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Int
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__U64

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

theorem Dec.Int.wp_proof (wp_U64 : Dec.U64.spec (GF := GF) (hG := hG)) :
    Dec.Int.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  wp_auto
  wp_apply wp_U64 d bs ok $$ [Hd] as %x Hd
  · iframe
  try wp_auto
  iapply HΦ
  iexact Hd

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
