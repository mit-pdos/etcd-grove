/-
`typed.removeItemsWithSchema`'s body, for the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`): its spec inside the
logic from the cluster's specs under a later.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalkerRec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- `typed.removeItemsWithSchema`'s body: given the cluster's specs under a later, its spec. -/
abbrev typed.removeItemsWithSchema.specBody : Prop :=
  ⊢ ▷ typed.removingWalkerRec.specI (GF := GF) -∗ typed.removeItemsWithSchema.specI (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
