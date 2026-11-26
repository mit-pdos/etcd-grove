/-
The proof of `Enc.I64` (`Spec/.../dist/enc/Enc__I64.lean`): a call of `U64`, the value converted (a no-op on `w64`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__I64
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__U64

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

theorem Enc.I64.wp_proof (wp_U64 : Enc.U64.spec (GF := GF) (hG := hG)) :
    Enc.I64.spec (GF := GF) (hG := hG) := by
  intro e bs x
  wp_start as He
  wp_auto
  wp_apply wp_U64 e bs x $$ [He] as He
  · iframe
  try wp_auto
  iapply HΦ
  iexact He

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
