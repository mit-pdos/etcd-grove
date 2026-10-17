/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/newSharedTx.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newSharedTx

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

theorem backend.newSharedTx.wp_proof :
    backend.newSharedTx.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %cm Hcm
  wp_alloc st as Hst
  iStructNamed Hst
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
