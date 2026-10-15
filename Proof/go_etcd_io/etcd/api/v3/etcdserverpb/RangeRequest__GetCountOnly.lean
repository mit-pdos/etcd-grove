/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RangeRequest__GetCountOnly.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetCountOnly

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem RangeRequest.GetCountOnly.wp_proof : RangeRequest.GetCountOnly.spec (GF := GF) (hG := hG) := by
  intro p v
  wp_start as ⟨%Hnn, #Hh⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · wp_end

end proof

end EtcdGrove
end Perennial
