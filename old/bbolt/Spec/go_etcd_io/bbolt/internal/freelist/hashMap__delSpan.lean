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

/-- `f.delSpan(start, size)`: the span at `start`, of size `size` (in a consistent `hashMap`),
is removed from the maps (its set of size `size` dropped if it is left empty), and `size` from
the count. -/
abbrev hashMap.delSpan.spec : Prop :=
  ∀ (h : Loc) (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
    (free : List w64) (start size : w64),
  hashOK cnt sp bwm sets free → sp !! start = some size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ hmRaw (GF := GF) h cnt sp bwm sets }}
    (App (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"delSpan")) (Val #start)) (Val #size))
  {{ RET #(); hmRaw h (cnt - size) (GMap.delete start sp)
      (GMap.delete (start + (size - W64 1)) bwm) (setsDel sets size start) }}

end spec

end bbolt
end EtcdGrove
end Perennial
