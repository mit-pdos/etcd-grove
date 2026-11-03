/-
`labelsutil.CloneAndAddLabel(labels, key, value)` (`pkg/util/labels`): with a non-empty key, a
fresh copy of the labels (`nil`: none) with `key ↦ value`. Lean-first; Stage 3, track B (`snapshot`).
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

open Iris Iris.BI apimodel consistency 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.util.labels.Assumptions]

/-- **`CloneAndAddLabel(m, k, v)`**, `k` not empty: a fresh map; the argument comes back. -/
abbrev CloneAndAddLabel.spec : Prop :=
  ∀ (m : GoMap) (dq : DFrac) (L : Option (GMap GoString GoString)) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.labels ∗ ownMapD m dq L ∗
      ⌜k ≠ []⌝ }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.util.labels.CloneAndAddLabel)) (Val #m)) (Val #k)) (Val #v))
  {{ (m' : GoMap), RET #m'; ownMapD m dq L ∗ m' ↦$ (<[k := v]> (L.getD ∅)) }}

end spec

end dsctl
end EtcdGrove
end Perennial
