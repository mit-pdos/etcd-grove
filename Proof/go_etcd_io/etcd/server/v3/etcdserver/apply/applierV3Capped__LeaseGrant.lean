/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3Capped.LeaseGrant.wp_proof :
    apply.applierV3Capped.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E c inner p r log Pre Q Post info
  wp_start as ⟨-, -, -, Htt, Hpre⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_noSpace $$ Hev with ⟨%eN, #HeN, #HeI⟩
  icases apply.mPreW_reject _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hkv, Hres, HPre, Hrt⟩
  wp_auto
  iapply HΦ
  iframe Htt HeI
  iunfold apply.mPostW
  iframe Hrt
  iunfold apply.mPost
  ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
  iframe Hkv Hres
  iright
  iexact HPre

end proof

end EtcdGrove
end Perennial
