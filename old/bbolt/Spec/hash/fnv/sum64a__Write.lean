module
public import Proof.hash.fnv.Model
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `h.Write(s)` of a `New64a` hash: it hashes `s`'s bytes too; it returns `len(s)` and no
error. -/
abbrev fnv.sum64a.Write.spec : Prop :=
  ∀ (t : go.GoType) (v : val) (bs : List w8) (s : GoSlice) (ds : List w8) (dq : DFrac),
  {{ fnvHash (GF := GF) t v bs ∗ s ↦*{dq} ds }}
    (App (Val #(methods t go!"Write" v)) (Val #s))
  {{ RET (PairV #s.len #interface.nil); fnvHash t v (bs ++ ds) ∗ s ↦*{dq} ds }}

end spec

end bbolt
end EtcdGrove
end Perennial
