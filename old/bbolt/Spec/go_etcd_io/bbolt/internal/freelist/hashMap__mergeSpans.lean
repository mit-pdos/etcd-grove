module
public import Proof.go_etcd_io.bbolt.internal.freelist.HashImpl

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

/-- `f.mergeSpans(ids)`: the ids (distinct, at least 2, not free) become free (the optional
checks hold: the maps agree, the ids are distinct and not free). -/
abbrev hashMap.mergeSpans.spec : Prop :=
  ∀ (h s : Loc) (free : List w64) (ids : GoSlice) (ys : List w64),
  (free ++ ys).Nodup → (∀ y ∈ ys, 2 ≤ uint.Z y) → free.length + ys.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownHashMap (GF := GF) h s free ∗ ids ↦* ys ∗ ownSliceCap w64 ids (DFrac.own 1) }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"mergeSpans")) (Val #ids))
  {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm (free ++ ys)⌝ ∗
      ownHashMap h s free' }}

end spec

end bbolt
end EtcdGrove
end Perennial
