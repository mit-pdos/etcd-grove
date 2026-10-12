module
public import Spec.go_etcd_io.bbolt.DefaultLogger__Panicf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DefaultLogger.Panicf.wp_proof :
    DefaultLogger.Panicf.spec (GF := GF) (hG := hG) := by
  intro dl f v
  wp_start as %Hf
  exact Hf.elim

end proof

end bbolt
end EtcdGrove
end Perennial
