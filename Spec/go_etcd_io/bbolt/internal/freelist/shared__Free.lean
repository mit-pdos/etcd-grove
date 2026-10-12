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

/-- `t.Free(txid, p)`: the page `p` and its overflow pages are pending for `txid`
(`FLState.freePages`); it must not panic (`FLState.canFree`). -/
abbrev shared.Free.spec : Prop :=
  ∀ (s : Loc) (iface : GoInterface) (σ : FLState) (txid : w64) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac),
  σ.canFree txid pv.id' (uint.nat pv.overflow' + 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s iface σ ∗ p ↦{dq} pv }}
    (App (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Free")) (Val #txid)) (Val #p))
  {{ RET #(); ownShared s iface (σ.freePages txid pv.id' (uint.nat pv.overflow' + 1)) ∗
      p ↦{dq} pv }}

end spec

end bbolt
end EtcdGrove
end Perennial
