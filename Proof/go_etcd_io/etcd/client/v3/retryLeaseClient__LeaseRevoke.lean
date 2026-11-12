/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryLeaseClient__LeaseRevoke.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseRevoke
public import Spec.go_etcd_io.etcd.client.v3.withRepeatablePolicy
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.leaseClient__LeaseRevoke

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem retryLeaseClient.LeaseRevoke.wp_proof
    (wp_withRepeatablePolicy : withRepeatablePolicy.spec (GF := GF) (hG := hG))
    (wp_stub : leaseClient.LeaseRevoke.spec (GF := GF) (hG := hG)) :
    retryLeaseClient.LeaseRevoke.spec (GF := GF) (hG := hG) := by
  intro rlc conn addr Spec Q ctx cd inp req opts vs
  wp_start as ⟨#Hrlc, #Hconn, #Hrpc, #Hpre, #Hctx, Hin, #Hopts, %Hcap, #Hok, %Hsz⟩
  iunfold retryLeaseAt at Hrlc
  icases Hrlc with ⟨%lc, #Hlc, #Hstub⟩
  wp_auto
  wp_apply wp_withRepeatablePolicy as %ro #Hro
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hopts
  ihave Hocap := ownSliceCap_empty (GF := GF) (V := GoInterface) opts Hcap Hlen.2
  wp_apply wp_slice_append_persistent opts vs _ _ (DFrac.own 1) $$ [$Hopts $Hocap $Hsl]
    as %copts ⟨#Hco, -, -⟩
  ihave #Hro1 : callOptOk (GF := GF) (interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro) $$ []
  · unfold callOptOk
    iright
    iexists ro
    iframe #
    ipureintro; rfl
  ihave #Hs1 := callOptsOk_singleton _ $$ Hro1
  ihave #Hok2 := callOptsOk_app vs _ $$ [Hok Hs1]
  · iframe #
  wp_apply wp_stub lc conn addr Spec Q ctx cd inp req copts _ $$ [Hin] as %resp %err Hres
  · iframe #
    iframe
    try (ipureintro; exact Hsz)
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
