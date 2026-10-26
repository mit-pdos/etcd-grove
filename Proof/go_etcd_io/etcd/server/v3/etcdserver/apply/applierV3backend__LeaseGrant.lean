/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseGrant
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.LeaseGrant.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post info
  wp_start as ⟨#Hb, ⟨⟨%g, #Hr, #Hgr⟩, HRW⟩, Hpre, Hwt⟩
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨⟨Hrd, Hsw, Hlive, Hard⟩, Hres, Hcs⟩
  icases Hard with ⟨Hard, Hwo⟩
  icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu⟩
  iunfold EtcdGrove.lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, -, -, #Hle, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, #HGrant, -⟩
  iunfold apply.leaseGrantIs at Hr
  icases Hr with ⟨%Hrn, #Hid, #Httl⟩
  iStructNamed Hopts
  wp_auto
  rw [Hli]
  wp_auto
  wp_apply HGrant $$ [$Hcs $HRW $Hown $Hwt $Hrt $Hgr] as %l %err ⟨HPP, Hrt, ⟨%L', Hown, %HLL, Hl⟩, #HeI⟩
  ihave Hwo := Hrdb $$ Hrt
  ihave Hlive : apply.leasesLive E.γ (mvcc.stateAfter log) $$ [Hown Hrdo]
  · iunfold apply.leasesLive
    iexists L'
    isplitl []
    · iapply EtcdGrove.apply.leasesKnown_mono L L' _ HLL $$ Hknown
    iunfold EtcdGrove.lease.lessorUser
    iframe Hown Hrdo
  icases Hl with (%Hne | ⟨%He, %id', #Hlease, -⟩)
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      isplitl; rotate_left
      · first | iexact HeI | iapply applyErrIs_nil
      iapply apply.mPost_backend
      iunfold apply.kvOwn
      iframe
  · subst He
    iunfold apply.leaseTTLIs at Hlease
    icases Hlease with ⟨%Hln, #HlID, #HTTL⟩
    iStructNamed «$r0»
    wp_auto
    wp_apply HTTL as %t -
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
    · iexact Hb
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iapply apply.mPost_backend
    iunfold apply.kvOwn
    iframe

end proof

end EtcdGrove
end Perennial
