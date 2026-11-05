/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
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

theorem apply.quotaApplierV3.LeaseGrant.wp_proof :
    apply.quotaApplierV3.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E c inner p r log Pre Q Post info
  wp_start as ⟨#Hq, #Hin, HR, Htt, Hpre, #Hsp⟩
  iunfold apply.quotaIs at Hq
  icases Hq with ⟨#Hf, %q, #Hqf, #Hqc⟩
  iunfold apply.isQuota at Hqc
  icases Hqc with ⟨%qi, %Hqi, #HAvail, -⟩
  subst Hqi
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_noSpace $$ Hev with ⟨%eN, #HeN, #HeI⟩
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, #HResp, -⟩
  icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hm, Hres⟩
  wp_auto
  wp_apply HAvail $$ %_ %r [] as %ok -
  · ipureintro; exact Or.inr (Or.inr rfl)
  ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ Hf Hres
  wp_apply HResp $$ %go!"LeaseGrant" %r %log %Pre %Q %Post [] [HR Htt Hm Hres]
    as %resp %err ⟨Htt, Hpost, #HeI'⟩
  · ipureintro; simp [apply.respMethods]
  · simp only [apply.reqFacts, ↓reduceIte]
    iframe HR Htt Hsp
    iapply apply.mPreW_of_rest
    iframe
  iunfold apply.mPostW at Hpost
  icases Hpost with ⟨Hpost, Hrt⟩
  iunfold apply.mPost at Hpost
  icases Hpost with ⟨Hkv, Hres, HPP⟩
  ihave Hres := apply.chainResAny_quota_in c p (.ok bi) $$ Hf Hres
  rcases err with e | _ <;> cases ok <;> (try wp_auto) <;>
  · iapply HΦ
    iframe Htt
    iunfold apply.mPostW
    iframe Hrt
    iunfold apply.mPost
    iframe
    (try first | iexact HeI | iexact HeI')

end proof

end EtcdGrove
end Perennial
