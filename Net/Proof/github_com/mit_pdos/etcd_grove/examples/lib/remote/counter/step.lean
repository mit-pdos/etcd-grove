/-
The proof of `step` (`Net/Spec/.../lib/remote/counter/step.lean`): straight-line code over
`int64`s, which `stepG` transcribes.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.step

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

theorem step.wp_proof : step.spec (GF := GF) (hG := hG) := by
  intro ⟨lo, k⟩ incr ⟨u, n⟩
  wp_start
  wp_auto
  cases u <;> cases incr <;> wp_auto
  all_goals (try wp_if_destruct)
  all_goals (try wp_if_destruct)
  all_goals (iapply HΦ; ipureintro; simp_all [stepG])

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
