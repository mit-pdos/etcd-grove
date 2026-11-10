/- Lean-first (no Rocq counterpart). Small lemmas the stream leaves' proofs share
(`stream.expect`): a watcher's position fields out of its struct's points-to, and back. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.watcher__matches

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

/-- **A watcher's position fields** (`rev`, `index`) out of its struct, and the struct back. -/
theorem watcher_pos_split (w : Loc) (wv : watcher) (dq : DFrac) :
    (w ↦{dq} wv : IProp GF) ⊢ w.[watcher, go!"rev"] ↦{dq} wv.rev' ∗ w.[watcher, go!"index"] ↦{dq} wv.index' ∗
      (w.[watcher, go!"rev"] ↦{dq} wv.rev' -∗ w.[watcher, go!"index"] ↦{dq} wv.index' -∗
        w ↦{dq} wv) := by
  iintro Hw
  icases (typedPointsto_not_null_dup _ _ _) $$ Hw with ⟨Hw, %Hwn⟩
  iStructNamedSuffix Hw "W"
  iframe revW indexW
  iintro revW indexW
  iapply typedPointsto_combine w _ dq Hwn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
