/-
`(*storage.StorageError).Unwrap()` (`k8s.io/apiserver/pkg/storage/errors.go`): the inner error
`e.err`, read from the struct (held at any fraction). Lean-first (no Rocq counterpart).
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
abbrev storage.StorageError.Unwrap.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (s : k8s_io.apiserver.pkg.storage.StorageError),
  {{ (l ↦{dq} s : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty)
      go!"Unwrap" #l)) (Val #()))
  {{ RET #s.err'; l ↦{dq} s }}

end spec

end EtcdGrove
end Perennial
