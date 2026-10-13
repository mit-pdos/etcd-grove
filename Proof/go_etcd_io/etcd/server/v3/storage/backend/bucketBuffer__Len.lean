/-
Proof of `Spec/.../backend/bucketBuffer__Len.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.bucketBuffer.Len.wp_proof : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG) := by
  intro bb es
  wp_start as H
  iunfold ownBB at H
  icases H with ⟨%p, H, %Hok⟩
  iunfold bbAt at H
  icases H with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
  wp_auto
  iapply HΦ
  iunfold ownBB
  iexists p
  iunfold bbAt
  iframe # ∗
  ipureintro; exact Hok

end proof

end EtcdGrove
end Perennial
