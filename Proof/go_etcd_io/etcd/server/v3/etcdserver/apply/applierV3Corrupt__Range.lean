/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Range
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

theorem apply.applierV3Corrupt.Range.wp_proof :
    apply.applierV3Corrupt.Range.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log
  wp_start as ⟨-, Hpre⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_corrupt $$ Hev with ⟨%eC, #HeC, #HeI⟩
  iunfold apply.rangePre at Hpre
  icases Hpre with ⟨%Hk, -, Hkv, Hres⟩
  wp_auto
  iapply HΦ
  iunfold apply.rangePost
  iexists (.rejected .corrupt)
  isplitr
  · ipureintro
    simp only [apply.chainStep, apply.corruptRejects, Hk.2.1, ↓reduceIte]
  simp only [apply.rangeOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
  iframe Hkv Hres
  isplitl []
  · ipureintro; trivial
  iunfold txn.errVarIs
  iexists eC
  iframe HeC
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
