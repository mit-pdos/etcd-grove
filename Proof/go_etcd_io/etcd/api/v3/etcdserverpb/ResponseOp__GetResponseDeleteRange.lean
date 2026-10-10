/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/ResponseOp__GetResponseDeleteRange.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseDeleteRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem ResponseOp.GetResponseDeleteRange.wp_proof :
    ResponseOp.GetResponseDeleteRange.spec (GF := GF) (hG := hG) := by
  intro p w x
  wp_start as ⟨%Hnn, #Hr, #Hx⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · wp_end

end proof

end EtcdGrove
end Perennial
