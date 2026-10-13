/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__UnlockForSafeRangeDelete.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__UnlockForSafeRangeDelete

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

theorem backend.backend.UnlockForSafeRangeDelete.wp_proof :
    backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b
  wp_start as ⟨#Hb, Hmu⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hmu] as Hmu
  · inext
    itrivial
  iapply HΦ
  iexact Hmu

end proof

end EtcdGrove
end Perennial
