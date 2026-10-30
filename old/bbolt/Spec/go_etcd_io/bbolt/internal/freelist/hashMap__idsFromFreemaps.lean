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

/-- `f.idsFromFreemaps()`: a new set of the free ids, gathered from `freemaps` (it does not panic: the
spans are disjoint). -/
abbrev hashMap.idsFromFreemaps.spec : Prop :=
  ∀ (h s : Loc) (free : List w64),
  {{ ownHashPart (GF := GF) h s free }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"idsFromFreemaps")) (Val #()))
  {{ (m : Loc) (M : GMap w64 Unit), RET #m;
      m ↦$ M ∗ ⌜∀ x, (M !! x).isSome ↔ x ∈ free⌝ ∗ ownHashPart h s free }}

end spec

end bbolt
end EtcdGrove
end Perennial
