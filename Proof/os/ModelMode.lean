/-
`os.modelMode(ty)` (the Go model's mode of a file of type `ty`: `ty | FileMode(ChooseUint64()) &
modelOtherBits`): some mode. A defs module; the `Stat` proofs use it.
-/
module

public import Proof.os.Base
public import Proof.internal.gomodel.LocalChoose

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- `modelMode(ty)` returns some `FileMode`. -/
theorem os.wp_modelMode (ty : w32) (Φ : val → IProp GF) :
    (∀ m : w32, Φ #m) ⊢ WP (App (Val (@! os.modelMode)) (Val #ty)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  try wp_auto
  wp_apply internal.gomodel.ChooseUint64.wp_local as %x -
  try wp_auto
  iapply HΦ

end proof

end EtcdGrove
end Perennial
