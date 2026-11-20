/-
`storage.isErrCode(err, code)` (`k8s.io/apiserver/pkg/storage/errors.go`): whether `err` is a
`*StorageError` (a type assertion, no unwrapping) with that code (`errCodeAt`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.ErrCode

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
abbrev storage.isErrCode.spec : Prop :=
  ∀ (err : GoInterface) (dq : DFrac) (c : Option w64) (code : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ k8s.errCodeAt err dq c }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.isErrCode)) (Val #err)) (Val #code))
  {{ RET #(decide (c = some code)); k8s.errCodeAt err dq c }}

end spec

end EtcdGrove
end Perennial
