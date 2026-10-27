/-
`getTypeName(obj)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`): some string (the object's
type name, a tracing attribute). Lean-first (no Rocq counterpart).
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
abbrev getTypeName.spec : Prop :=
  ∀ (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      ⌜x ≠ GoInterface.nil⌝ }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.getTypeName)) (Val #x))
  {{ (s : GoString), RET #s; True }}

end spec

end k8s
end EtcdGrove
end Perennial
