module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayModel

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

/-- `f.Init(ids)`: the free ids become `ids` (kept: the slice is the array's now), the
cache rebuilt (`reindex`). -/
abbrev array.Init.spec : Prop :=
  ∀ (a s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
  ({ σ with free := xs } : FLState).WF →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ arrayHdl (GF := GF) a s ∗ ownShared s (arrayImpl (GF := GF) a).iface σ ∗ ownArrayPart a s σ.free ∗
      ids ↦* xs ∗ ownSliceCap w64 ids (DFrac.own 1) }}
    (App (Val (a @!! go.GoType.PointerType array'.ty @!! go!"Init")) (Val #ids))
  {{ RET #(); ownShared s (arrayImpl (GF := GF) a).iface { σ with free := xs } ∗ ownArrayPart a s xs }}

end spec

end bbolt
end EtcdGrove
end Perennial
