/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryKVClient__Range.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Range
public import Spec.go_etcd_io.etcd.client.v3.withRepeatablePolicy
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Range

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem retryKVClient.Range.wp_proof
    (wp_withRepeatablePolicy : withRepeatablePolicy.spec (GF := GF) (hG := hG))
    (wp_kVClient_Range : kVClient.Range.spec (GF := GF) (hG := hG)) :
    retryKVClient.Range.spec (GF := GF) (hG := hG) := by
  intro rkv conn K ctx cd inp req k e opts vs Q
  wp_start as ⟨#Hrkv, #Hconn, #Hctx, Hin, #Hk, #He, #Hopts, %Hcap, #Hok, #Hrun⟩
  iunfold retryKVAt at Hrkv
  icases Hrkv with ⟨%kc, #Hkc, #Hstub⟩
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
  wp_apply wp_kVClient_Range kc conn K ctx cd inp req k e copts _ Q $$ [Hin] as %resp %err Hres
  · iframe #
    iframe
  iapply HΦ
  iexact Hres

end proof

end EtcdGrove
end Perennial
