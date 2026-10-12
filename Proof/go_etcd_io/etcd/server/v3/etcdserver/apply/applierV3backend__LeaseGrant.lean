/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader

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

theorem apply.applierV3backend.LeaseGrant.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post
  wp_start as ⟨#Hb, ⟨%g, #Hr⟩, Hpre⟩
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨⟨Hrd, Hsw, #Hknown⟩, Hres, Hcs⟩
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
  wp_apply HGrant $$ [$Hcs] as %l %err ⟨HPP, Hl⟩
  icases Hl with (%Hne | ⟨%He, %id', #Hlease, -⟩)
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iunfold apply.mPost
      iunfold apply.kvOwn
      iframe
      iframe #
  · subst He
    iunfold apply.leaseIs at Hlease
    icases Hlease with ⟨%Hln, #HlID, #HTTL, -⟩
    iStructNamed «$r0»
    wp_auto
    wp_apply HTTL as %t -
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
    · iexact Hb
    iapply HΦ
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
