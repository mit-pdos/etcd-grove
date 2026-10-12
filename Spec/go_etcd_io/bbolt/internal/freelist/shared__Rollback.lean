module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.Iface

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

/-- `t.Rollback(txid)`: `FLState.rollback`. Not proved: it deletes map entries while ranging over the map (allowed in Go, stuck in
the GooseLang map model, whose range body runs under a read of the map). -/
abbrev shared.Rollback.spec : Prop :=
  ∀ (s : Loc) (iface : GoInterface) (σ : FLState) (txid : w64), σ.canRollback txid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s iface σ }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Rollback")) (Val #txid))
  {{ RET #(); ownShared s iface (σ.rollback txid) }}

end spec

end bbolt
end EtcdGrove
end Perennial
