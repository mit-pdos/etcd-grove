/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__LockInsideApply.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__LockInsideApply

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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTxBuffered.LockInsideApply.wp_proof
    (hM : backend.batchTx.LockInsideApply.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t qo dq f Pre Q
  wp_start as ⟨#Hb, #Ht, Ho, Hpl, Hpre, Hf⟩
  wp_apply (hM γ P W Pk b t qo dq f Pre Q) $$ [$Ho $Hpl $Hpre $Hf] as ⟨%st, Hl, %Hfo, HWv, HQ, Ho, Hpl⟩
  · iframe #
  iapply HΦ
  iexists st
  iframe
  ipureintro
  exact Hfo

end proof

end EtcdGrove
end Perennial
