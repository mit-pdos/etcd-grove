module
public import Spec.go_etcd_io.bbolt.node__minKeys

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

theorem node.minKeys.wp_proof : node.minKeys.spec (GF := GF) (hG := hG) := by
  intro nl nv dq
  wp_start as Hn
  wp_auto
  cases h : nv.isLeaf' <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> wp_auto <;> iapply HΦ <;> iframe

end proof

end bbolt
end EtcdGrove
end Perennial
