/-
`getTypeName(obj)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`): some string (the object's
type name, a tracing attribute), of an object that is not a value of reflect's own `rtype`
(`reflectM.notRType`: `reflect.TypeOf` of the model is stuck on those). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.reflect.Values

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev getTypeName.spec : Prop :=
  ∀ (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      ⌜reflectM.notRType x⌝ }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.getTypeName)) (Val #x))
  {{ (s : GoString), RET #s; True }}

end spec

end k8s
end EtcdGrove
end Perennial
