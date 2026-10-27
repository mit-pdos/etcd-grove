/-
`storage.NewKeyExistsError(key, rv)` (`k8s.io/apiserver/pkg/storage/errors.go`): a new
`*StorageError` with code `ErrCodeKeyExists` (`2`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.NewKeyExistsError.spec : Prop :=
  ∀ (key : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.NewKeyExistsError)) (Val #key)) (Val #rv))
  {{ (p : Loc), RET #p;
      p ↦ k8s_io.apiserver.pkg.storage.StorageError.mk (W64 2) key rv GoInterface.nil }}

end spec

end EtcdGrove
end Perennial
