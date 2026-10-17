/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/sharedBoltTx__lock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__lock

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

theorem backend.sharedBoltTx.lock.wp_proof :
    backend.sharedBoltTx.lock.spec (GF := GF) (hG := hG) := by
  intro st tm P
  wp_start as ⟨#Htm, #Hg⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hwl, HP⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
