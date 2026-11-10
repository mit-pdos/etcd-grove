/- Lean-first (no Rocq counterpart). The proof of `MainConfig` (the literal): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig

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

theorem MainConfig.wp_proof :
    MainConfig.spec (GF := GF) (hG := hG) := by
  intro pfx
  wp_start
  wp_auto
  repeat (wp_apply wp_slice_literal; isplitr; · ipureintro; rfl
          iintro %_ ⟨_, -⟩; (try wp_auto))
  unfold mainConfigM
  rw [show (W64 0 : w64) = 0 from rfl]
  iapply HΦ
  iunfold mainMixOwn
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
