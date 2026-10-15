/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__Lock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__Lock

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

theorem backend.readTx.Lock.wp_proof : backend.readTx.Lock.spec (GF := GF) (hG := hG) := by
  intro γ P rt
  wp_start as #Hg
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hl, HP⟩
  wp_pure
  wp_auto
  iapply HΦ
  iframe


end proof

end EtcdGrove
end Perennial
