/-
`DisableSnapshotList()` (`examples/k8s/compactor/compactor.go`; U3 of K2 in
`notes/k8s-compactor-plan.md`, the user's approval 2026-11-04):
`utilfeature.DefaultMutableFeatureGate.Set("ListFromCacheSnapshot=false")`, as an API server started
with `--feature-gates=ListFromCacheSnapshot=false`. Lean-first (no Rocq counterpart).

**The triple:** from the package's initialization, it returns an error or, on success, `gateOff`:
`DefaultFeatureGate`'s `Enabled` answers `false` for `ListFromCacheSnapshot`, for good (so
`NewCompactor` starts no watch loop). Its proof is an axiom (the trust boundary: the gate is
`component-base/featuregate`'s, names only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev DisableSnapshotList.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.DisableSnapshotList))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ k8s.gateOff) }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
