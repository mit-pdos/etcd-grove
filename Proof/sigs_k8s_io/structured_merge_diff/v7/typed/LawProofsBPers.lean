/-
**Persistence instances of the merge walker's vocabulary** (`Walkers.lean`): what the merging and
compare walkers' proofs keep in the intuitionistic context.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance ruleKeepRHSOk_pers (f : GoFunc) : Persistent (ruleKeepRHSOk (GF := GF) f) := by
  unfold ruleKeepRHSOk; infer_instance

instance outRep_pers (o : Loc) : (x : Option UVal) → Persistent (outRep (GF := GF) o x)
  | none => by unfold outRep; infer_instance
  | some _ => by unfold outRep; infer_instance

/-- Calling `ruleKeepRHS`'s closure (the persistent spec read at one call). -/
theorem ruleKeepRHSOk_call (f : GoFunc) (w : Loc) (v : typed.mergingWalker) (dql dqr : DFrac)
    (l r : Option UVal) :
    ruleKeepRHSOk (GF := GF) f ⊢
    {{ w ↦ v ∗ isValO v.lhs' dql l ∗ isValO v.rhs' dqr r ∗ ⌜l.isSome ∨ r.isSome⌝ }}
      (App (Val #f) (Val #w))
    {{ RET #(); ∃ o : Loc, w ↦ { v with out' := o } ∗ outRep o (leafM l r) ∗
        isValO v.lhs' dql l ∗ isValO v.rhs' dqr r }} := by
  unfold ruleKeepRHSOk
  iintro #H
  iapply H

end laws

end smd
end EtcdGrove
end Perennial
