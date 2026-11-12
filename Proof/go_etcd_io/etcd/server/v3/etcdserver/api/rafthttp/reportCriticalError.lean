/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/reportCriticalError.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.reportCriticalError

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.reportCriticalError.wp_proof :
    rafthttp.reportCriticalError.spec (GF := GF) (hG := hG) := by
  intro err ec
  wp_start as ⟨#Hec, #Herr⟩
  iunfold errcOk at Hec
  icases Hec with ⟨%γ, #Hbag⟩
  wp_auto_lc 3
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, ec, γ, err
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      unfold nonblockingSendAu
      isplit
      · iapply bag_nonblocking_send_au $$ Hlc1 Hbag Herr
        inext
        (try wp_auto)
        iapply HΦ; itrivial
      · itrivial
    · iapply BigAndL.bigAndL_nil.2; itrivial
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
