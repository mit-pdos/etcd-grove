/-
`(*store).validateMinimumResourceVersion(minimumResourceVersion, actualRevision)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`) with no minimum (`""`): `nil`. A minimum that
parses is checked against the revision (`NewTooLargeResourceVersionError`, through apimachinery's
names-only `NewTimeoutError`): not specified yet. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.validateMinimumResourceVersion.spec : Prop :=
  ∀ (sp : Loc) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
      go!"validateMinimumResourceVersion")) (Val #([] : GoString))) (Val #rev))
  {{ RET #GoInterface.nil; True }}

end spec

end k8s
end EtcdGrove
end Perennial
