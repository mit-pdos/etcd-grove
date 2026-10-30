module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.HashModel

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

/-- `f.addSpan(start, size)`: the span is added to the maps, and `size` to the count. -/
abbrev hashMap.addSpan.spec : Prop :=
  ∀ (h : Loc) (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)) (start size : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ hmRaw (GF := GF) h cnt sp bwm sets }}
    (App (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"addSpan")) (Val #start)) (Val #size))
  {{ RET #(); hmRaw h (cnt + size) (<[start := size]> sp) (<[start - W64 1 + size := size]> bwm)
      (<[size := <[start := ()]> ((sets !! size).getD ∅)]> sets) }}

end spec

end bbolt
end EtcdGrove
end Perennial
