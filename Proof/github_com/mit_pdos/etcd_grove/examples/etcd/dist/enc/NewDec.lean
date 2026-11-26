/-
The proof of `NewDec` (`Spec/.../dist/enc/NewDec.lean`): the decoder allocated, holding the slice.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.NewDec

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

theorem NewDec.wp_proof : NewDec.spec (GF := GF) (hG := hG) := by
  intro b bs dq
  wp_start as Hb
  wp_auto
  iapply HΦ
  unfold ownDec
  iexists b, dq
  iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
