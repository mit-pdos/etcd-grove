/-
`fieldpath.Set.Size`'s body, for the recursion cluster `fieldpath.SizeRec` (`SizeRec.lean`): its spec inside the
logic from the cluster's specs under a later.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SizeRec

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
variable [package_sem : fieldpath.Assumptions]

/-- `fieldpath.Set.Size`'s body: given the cluster's specs under a later, its spec. -/
abbrev fieldpath.Set.Size.specBody : Prop :=
  ⊢ ▷ fieldpath.SizeRec.specI (GF := GF) -∗ fieldpath.Set.Size.specI (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
