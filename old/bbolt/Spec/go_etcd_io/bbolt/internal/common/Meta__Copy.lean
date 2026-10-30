module
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `m.Copy(dest)`: `*dest = *m`. -/
abbrev Meta.Copy.spec : Prop :=
  ∀ (l d : Loc) (v w : Meta) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v ∗ d ↦ w }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"Copy")) (Val #d))
  {{ RET #(); l ↦{dq} v ∗ d ↦ v }}

end spec

end bbolt
end EtcdGrove
end Perennial
