/-
`int32PtrEqual(a, b)`: both nil, or both pointing to equal values.
Lean-first (no Rocq counterpart); phase 3 of `notes/k8s-daemonset-plan.md` (the model API server's
specs, D50's internal layer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

abbrev int32PtrEqual.spec : Prop :=
  ∀ [ApiDeps] (a b : Loc) (da db : Option w32),
  {{ (ownPtrD (V := w32) ownBaseD a (DFrac.own 1) da : IProp GF) ∗ ownPtrD (V := w32) ownBaseD b (DFrac.own 1) db }}
    (App (App (Val (@! apimodel.int32PtrEqual)) (Val #a)) (Val #b))
  {{ RET #(decide (da = db)); ownPtrD (V := w32) ownBaseD a (DFrac.own 1) da ∗
      ownPtrD (V := w32) ownBaseD b (DFrac.own 1) db }}

end spec

end apimodel
end EtcdGrove
end Perennial
