/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__LeaseGrant
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

theorem apply.applierV3Corrupt.LeaseGrant.wp_proof :
    apply.applierV3Corrupt.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq g log T rs Pre Q Post info
  wp_start as ⟨-, Hgp⟩
  iunfold apply.grantPre at Hgp
  icases Hgp with ⟨%Hrq, -, -, -, HltT, HRO, -, Hpre, -⟩
  obtain ⟨-, Hg, Hk⟩ := Hrq
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_corrupt $$ Hev with ⟨%eC, #HeC, #HeI⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  wp_auto
  iapply HΦ
  iexists (Outcome.rejected .corrupt)
  iunfold apply.grantPost
  iframe HeI
  isplitl [Hkv Hres Hcs]
  · iunfold apply.mPost
    ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
    iframe Hkv Hres
    iright
    iapply apply.csContract_pre $$ Hcs
  isplitr
  · ipureintro
    refine ⟨?_, ?_, ?_⟩
    · simp [apply.chainStep, Hk, apply.corruptRejects]
    · constructor
      · rintro ⟨_, _, h⟩; cases h
      · intro h; cases h
    · constructor
      · intro h; cases h
      · rintro ⟨h, -⟩; cases h
  rw [apply.grantIds_rejected]
  iframe HltT
  isplitl [HRO]
  · iexists (W64 0); rw [apply.grantRest_rejected]; iexact HRO
  iunfold apply.grantAnswer
  rw [Hg]
  iexists _
  isplitr
  · ipureintro; rfl
  iright; ipureintro; nofun

end proof

end EtcdGrove
end Perennial
