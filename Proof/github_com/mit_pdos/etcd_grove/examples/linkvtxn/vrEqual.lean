/-
Lean-first (no Rocq counterpart).

The proof of `vrEqual`: the three fields compared.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem VR_eq_iff (a b : VR) : a = b ↔ a.Val' = b.Val' ∧ a.Mod' = b.Mod' ∧ a.Ver' = b.Ver' := by
  cases a; cases b; simp

theorem vrEqual.wp_proof : vrEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals first
    | (rw [decide_eq_false (fun h => by subst h; simp_all)]; iapply HΦ; itrivial)
    | (rw [decide_eq_true (by rw [VR_eq_iff]; and_intros <;> assumption)]
       iapply HΦ; itrivial)

end proof

end linkvtxn
end EtcdGrove
end Perennial
