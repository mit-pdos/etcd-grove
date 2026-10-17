/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/sharedBoltTx__clone.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__clone

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

theorem backend.sharedBoltTx.clone.wp_proof :
    backend.sharedBoltTx.clone.spec (GF := GF) (hG := hG) := by
  intro st dq tm tx cm wg
  wp_start as ⟨#Htm, Htx, Hcm, Hwg⟩
  wp_auto
  wp_alloc st' as Hst
  iStructNamed Hst
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
