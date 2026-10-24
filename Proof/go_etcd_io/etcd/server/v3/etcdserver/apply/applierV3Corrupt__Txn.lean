/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3Corrupt.Txn.wp_proof :
    apply.applierV3Corrupt.Txn.spec (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t log F Pre Q Post info
  wp_start as ⟨-, Hpre, #HF⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_corrupt $$ Hev with ⟨%eC, #HeC, #HeI⟩
  iunfold apply.txnPre at Hpre
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨%Hk, -, -, -, Hkv, Hres, Hcs⟩
  wp_auto
  iapply HΦ
  isplitl
  rotate_left
  · iapply apply.traceRes_null
  ihave #Hcls : apply.chainClass (GF := GF) E.authMode info (.corrupt c) rq (.rejected .corrupt) $$ []
  · iapply apply.chainClass_corrupt_rejected
  iunfold apply.kvPostF
  iexists (.rejected .corrupt)
  isplitr
  · ipureintro
    refine ⟨?_, fun _ _ h => by cases h⟩
    simp only [apply.chainStep, apply.corruptRejects, Hk.2.1, ↓reduceIte]
  simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
  iframe Hkv Hres Hcls
  isplitl []
  · isplitl []
    · ipureintro; trivial
    iunfold txn.errVarIs
    iexists eC
    iframe HeC
    ipureintro; rfl
  iright
  iapply apply.csContract_pre $$ Hcs

end proof

end EtcdGrove
end Perennial
