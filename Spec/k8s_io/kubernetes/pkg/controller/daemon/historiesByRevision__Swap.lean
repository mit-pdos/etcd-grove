/-
`historiesByRevision.Swap(i, j)` (`update.go:630`): swaps two elements. Lean-first; Stage 3, track B.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`historiesByRevision(s).Swap(i, j)`**, in bounds: the elements' order permuted. -/
abbrev historiesByRevision.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (xs : List kd.apps.ControllerRevision) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ crsAt sl (DFrac.own 1) xs ∗
      ⌜sint.Z i < xs.length ∧ sint.Z j < xs.length ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j⌝ }}
    (App (App (Val #(methods historiesByRevision.ty go!"Swap" #sl)) (Val #i)) (Val #j))
  {{ RET #(); ∃ ys, crsAt sl (DFrac.own 1) ys ∗ ⌜List.Perm ys xs⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
