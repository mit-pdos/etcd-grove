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

/-- `Meta.IncTxid()`: the field `txid` becomes one more (modulo `2^64`). -/
abbrev Meta.IncTxid.spec : Prop :=
  ∀ (l : Loc) (v : Meta),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType Meta.ty @!! go!"IncTxid")) (Val #()))
  {{ RET #(); l ↦ ({ v with txid' := v.txid' + 1 } : Meta) }}

end spec

end bbolt
end EtcdGrove
end Perennial
