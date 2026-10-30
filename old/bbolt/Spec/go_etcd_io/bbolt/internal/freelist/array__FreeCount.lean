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

/-- `f.FreeCount()`: the number of free ids. -/
abbrev array.FreeCount.spec : Prop :=
  ∀ (a s : Loc) (free : List w64),
  {{ ownArrayPart (GF := GF) a s free }}
    (App (Val (a @!! go.GoType.PointerType array'.ty @!! go!"FreeCount")) (Val #()))
  {{ RET #(W64 (free.length : Int)); ownArrayPart a s free }}

end spec

end bbolt
end EtcdGrove
end Perennial
