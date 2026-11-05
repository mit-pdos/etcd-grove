/-
`storage.NewInvalidObjError(key, msg)` (`k8s.io/apiserver/pkg/storage/errors.go`): a new
`*StorageError` with code `ErrCodeInvalidObj` (`4`), the key, and an inner error (`errors.New(msg)`).
Lean-first (no Rocq counterpart; stage 7b of `notes/k8s-etcd3-plan.md`).
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
abbrev storage.NewInvalidObjError.spec : Prop :=
  ∀ (key msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.NewInvalidObjError)) (Val #key)) (Val #msg))
  {{ (p : Loc), RET #p; ∃ e : GoInterface,
      p ↦ k8s_io.apiserver.pkg.storage.StorageError.mk (W64 4) key (W64 0) e }}

end spec

end EtcdGrove
end Perennial
