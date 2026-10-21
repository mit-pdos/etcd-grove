/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridgeConn__Close.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__Close
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridgeConn__close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridgeConn.Close.wp_proof (wp_close : bridgeConn.close.spec (GF := GF) (hG := hG)) :
    bridgeConn.Close.spec (GF := GF) (hG := hG) := by
  intro b c q γt
  wp_start as #Hc
  iunfold connOk at Hc
  icases Hc with ⟨%inc, %outc, %donec, %γd, #Hcf, #Hin, #Hout, #Hdb⟩
  ihave #Hcf' := Hcf
  iunfold connFields at Hcf'
  icases Hcf' with ⟨#Hci, #Hco, #Hcd⟩
  wp_auto
  wp_apply wp_close c inc outc donec $$ []
  · iframe #
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdb
  wp_bind (App (Val (chan.receive _)) (Val #donec))
  wp_apply_core chan.wp_receive (V := Unit) donec γd $$ Hdcc
  iintro -
  iapply broadcast_chan_receive donec γd (doneQ b q γt) _ .Unknown $$ Hdb
  iintro ⟨#HQ, -⟩
  wp_auto
  iapply HΦ
  iexact HQ

end proof

end bridge
end EtcdGrove
end Perennial
