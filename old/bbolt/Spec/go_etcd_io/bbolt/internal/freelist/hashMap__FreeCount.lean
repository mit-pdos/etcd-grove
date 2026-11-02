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

/-- `f.FreeCount()`: the number of free ids (the optional check, that the count agrees with
the spans, holds). -/
abbrev hashMap.FreeCount.spec : Prop :=
  ∀ (h s : Loc) (free : List w64),
  {{ ownHashMap (GF := GF) h s free }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"FreeCount")) (Val #()))
  {{ RET #(W64 (free.length : Int)); ownHashMap h s free }}

end spec

end bbolt
end EtcdGrove
end Perennial
