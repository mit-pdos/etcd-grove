/-
`(*storage.Preconditions).Check(key, obj)` (`k8s.io/apiserver/pkg/storage/interfaces.go`) on `nil`
preconditions: `nil`. Lean-first (no Rocq counterpart). `GuaranteedUpdate` checks its
preconditions unconditionally; the store's specs take none for now.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.Preconditions.Check.spec : Prop :=
  ∀ (key : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (Val ((null : Loc) @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.Preconditions.ty @!! go!"Check")) (Val #key)) (Val #obj))
  {{ RET #GoInterface.nil; True }}

end spec

end EtcdGrove
end Perennial
