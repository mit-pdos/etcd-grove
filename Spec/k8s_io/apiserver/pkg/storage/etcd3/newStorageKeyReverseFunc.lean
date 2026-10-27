/-
`newStorageKeyReverseFunc(pathPrefix, reverseKeyFunc)` (`store.go`): a function. Lean-first (no Rocq counterpart).
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
abbrev newStorageKeyReverseFunc.spec : Prop :=
  ∀ (pp : GoString) (rk : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.newStorageKeyReverseFunc)) (Val #pp)) (Val #rk))
  {{ (f : GoFunc), RET #f; True }}

end spec

end k8s
end EtcdGrove
end Perennial
