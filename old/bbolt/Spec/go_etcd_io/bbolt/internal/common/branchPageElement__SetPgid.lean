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

/-- `branchPageElement.SetPgid(x)` writes the field `pgid`. -/
abbrev branchPageElement.SetPgid.spec : Prop :=
  ∀ (l : Loc) (v : branchPageElement) (x : Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType branchPageElement.ty @!! go!"SetPgid")) (Val #x))
  {{ RET #(); l ↦ ({ v with pgid' := x } : branchPageElement) }}

end spec

end bbolt
end EtcdGrove
end Perennial
