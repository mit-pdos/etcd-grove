/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__LockForSafeRangeDelete.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__LockForSafeRangeDelete

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

theorem backend.backend.LockForSafeRangeDelete.wp_proof :
    backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG) := by
  intro γ P WR b
  wp_start as ⟨#Hb, Hmu⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hmu] as ⟨Hl, -⟩
  iapply HΦ
  iexact Hl

end proof

end EtcdGrove
end Perennial
