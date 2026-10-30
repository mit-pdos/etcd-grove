module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `cloneBytes(v)`: a new slice with `v`'s bytes. -/
abbrev cloneBytes.spec : Prop :=
  ∀ (v : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ v ↦*{dq} bs }}
    (App (Val #(functions cloneBytes [])) (Val #v))
  {{ (c : GoSlice), RET #c; c ↦* bs ∗ ownSliceCap w8 c (DFrac.own 1) ∗ v ↦*{dq} bs }}

end spec

end bbolt
end EtcdGrove
end Perennial
