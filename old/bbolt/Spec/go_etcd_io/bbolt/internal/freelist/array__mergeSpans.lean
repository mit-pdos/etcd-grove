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

/-- `f.mergeSpans(ids)`: the ids (distinct, at least 2, not free) become free (merged into the
sorted free ids; `ids` is sorted in place and may be kept as the free ids). -/
abbrev array.mergeSpans.spec : Prop :=
  ∀ (a s : Loc) (free : List w64) (ids : GoSlice) (ys : List w64),
  (free ++ ys).Nodup → (∀ y ∈ ys, 2 ≤ uint.Z y) → free.length + ys.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownArrayPart a s free ∗ ids ↦* ys ∗ ownSliceCap w64 ids (DFrac.own 1) }}
    (App (Val (a @!! go.GoType.PointerType array'.ty @!! go!"mergeSpans")) (Val #ids))
  {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm (free ++ ys)⌝ ∗
      ownArrayPart a s free' }}

end spec

end bbolt
end EtcdGrove
end Perennial
