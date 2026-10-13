/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__ForceCommit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Commit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.backend.ForceCommit.wp_proof
    (hCommit : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG)) :
    backend.backend.ForceCommit.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b qo
  wp_start as ⟨#Hb, Ho, Htok⟩
  icases isBackend_b γ P W Pk b $$ Hb with
    ⟨%t, %rt, %db1, %lg2, #Ht, #-⟩
  wp_auto
  wp_apply (hCommit γ P W Pk b t qo) $$ [$Ho $Htok] as Ho
  · iframe #
  iapply HΦ
  iexact Ho

end proof

end EtcdGrove
end Perennial
