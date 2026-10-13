/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas

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

theorem apply.applierV3backend.LeaseRevoke.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro E p r rq id log Pre Q Post
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.revokePre at Hpre
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨%Hrq, #Hr, Hwt, ⟨Hrd, Hsw, #Hknown⟩, Hres, Hcs⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, -, -, #Hle, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, -, #HRevoke, -⟩
  iunfold apply.leaseRevokeIs at Hr
  icases Hr with ⟨%Hrn, #Hid⟩
  iStructNamed Hopts
  wp_auto
  rw [Hli]
  wp_auto
  wp_apply HRevoke $$ [$Hcs $Hsw $Hwt] as %err ⟨HPP, ⟨%pend, %Hdel, Hsw⟩, #HeI⟩
  wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
  · iexact Hb
  wp_alloc resp as Hresp
  wp_auto
  iapply HΦ
  iunfold apply.kvPost
  iexists (.applied (mvcc.commitLog log pend) false)
  isplitr
  · ipureintro
    unfold apply.chainStep apply.backendStep
    rw [Hrq.2]
    exact ⟨pend, Hdel, rfl⟩
  simp only [apply.revokeOutcomeIs, apply.Outcome.logAfter]
  iframe HeI Hres HPP
  iunfold apply.kvOwn
  iframe Hrd Hsw
  iapply apply.leasesKnown_commit_dels _ log pend Hdel $$ Hknown

end proof

end EtcdGrove
end Perennial
