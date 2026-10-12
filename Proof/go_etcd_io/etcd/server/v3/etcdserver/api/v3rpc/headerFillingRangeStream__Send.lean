/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.headerFillingRangeStream__Send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fillWithoutRevision

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.headerFillingRangeStream.Send.wp_proof
    (hFWR : v3rpc.header.fillWithoutRevision.spec (GF := GF) (hG := hG)) :
    v3rpc.headerFillingRangeStream.Send.spec (GF := GF) (hG := hG) := by
  intro p hp s A cid mid stv Ψ Ξ resp rr h
  wp_start as ⟨#Hst, #Hhp, #Hhdr, #Hsend, #Hrr, %Hrrn, #Hh, Hpre⟩
  iunfold v3rpc.streamSendOk at Hsend
  icases Hsend with ⟨%si, %Hsi, #HSend⟩
  subst Hsi
  wp_auto
  icases Hpre with (⟨%Hhn, HΨ⟩ | ⟨Hw, HΨ⟩)
  · subst Hhn
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #resp))
    iapply HSend $$ HΨ
    inext
    iintro %err HΞ
    wp_auto
    iapply HΦ
    iexact HΞ
  · iunfold v3rpc.hdrW at Hw
    icases Hw with ⟨%Hhn, Hw⟩
    ihave Hw : v3rpc.hdrW h $$ [Hw]
    · iunfold v3rpc.hdrW; iframe; ipureintro; exact Hhn
    simp only [decide_false, Hhn, Bool.not_false]
    wp_auto
    wp_apply hFWR $$ [Hw] as Hf
    · iframe; iframe #
    wp_auto
    wp_bind (App (Val #(methods si.ty go!"Send" si.v)) (Val #resp))
    iapply HSend $$ [HΨ Hf]
    · iapply HΨ $$ Hf
    inext
    iintro %err HΞ
    wp_auto
    iapply HΦ
    iexact HΞ

end proof

end EtcdGrove
end Perennial
