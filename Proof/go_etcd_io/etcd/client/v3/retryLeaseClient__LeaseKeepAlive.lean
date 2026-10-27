/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryLeaseClient__LeaseKeepAlive.lean` (item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryLeaseClient__LeaseKeepAlive
public import Spec.go_etcd_io.etcd.client.v3.withRepeatablePolicy
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.leaseClient__LeaseKeepAlive

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

theorem retryLeaseClient.LeaseKeepAlive.wp_proof
    (wp_withRepeatablePolicy : withRepeatablePolicy.spec (GF := GF) (hG := hG))
    (wp_stub : leaseClient.LeaseKeepAlive.spec (GF := GF) (hG := hG)) :
    retryLeaseClient.LeaseKeepAlive.spec (GF := GF) (hG := hG) := by
  intro rlc conn addr ctx cd opts vs
  wp_start as ⟨#Hrlc, #Hconn, #Hstr, #Hctx, #Hopts, Hocap, #Hok⟩
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
  wp_apply wp_slice_append_persistent opts vs _ _ (DFrac.own 1) $$ [$Hopts $Hocap $Hsl]
    as %copts ⟨#Hco, -, -⟩
  ihave #Hro1 : callOptOk (GF := GF) (interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro) $$ []
  · unfold callOptOk
    iright
    iexists ro
    iframe #
    ipureintro; rfl
  ihave #Hs1 := callOptsOk_singleton _ $$ Hro1
  ihave #Hs1' := streamCallOptsOk_of _ $$ Hs1
  ihave #Hok2 := streamCallOptsOk_app vs _ $$ [Hok Hs1']
  · iframe #
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hdesc := leaseDescOk_of_init $$ Hpb
  wp_apply wp_stub lc conn addr ctx cd copts _ $$ [] as %st %err Hres
  · iframe #
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
