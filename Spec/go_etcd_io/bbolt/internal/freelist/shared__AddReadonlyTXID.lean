module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.AddReadonlyTXID(tid)`: `tid` is appended to the read-only transactions. -/
abbrev shared.AddReadonlyTXID.spec : Prop :=
  ∀ (s : Loc) (iface : GoInterface) (σ : FLState) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s iface σ }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"AddReadonlyTXID")) (Val #tid))
  {{ RET #(); ownShared s iface { σ with readonly := σ.readonly ++ [tid] } }}

end spec

end bbolt
end EtcdGrove
end Perennial
