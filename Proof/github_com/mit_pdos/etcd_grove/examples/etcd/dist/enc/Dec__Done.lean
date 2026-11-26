/-
The proof of `Dec.Done` (`Spec/.../dist/enc/Dec__Done.lean`): the flag, and the slice's length.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Done

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

theorem Dec.Done.wp_proof : Dec.Done.spec (GF := GF) (hG := hG) := by
  intro d bs ok
  wp_start as Hd
  unfold ownDec
  icases Hd with ⟨%s, %dq, Hd, Hs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  cases ok
  · wp_auto
    iapply HΦ
    ipureintro; simp
  · wp_auto
    iapply HΦ
    ipureintro
    intro h
    refine ⟨rfl, ?_⟩
    apply List.eq_nil_of_length_eq_zero
    simp_all

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
end Perennial
