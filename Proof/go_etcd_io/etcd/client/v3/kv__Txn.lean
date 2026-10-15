/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Txn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Txn

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

theorem kv.Txn.wp_proof : kv.Txn.spec (GF := GF) (hG := hG) := by
  intro api addr ci cd
  wp_start as ⟨#Hkv, #Hctx, #Hce⟩
  ihave #Hkv' := Hkv
  iunfold kvObjAt at Hkv'
  icases Hkv' with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iapply wp_fupd
  wp_auto
  wp_alloc tp as Htp
  wp_auto
  ihave %Htpn := typedPointsto_not_null _ _ _ $$ Htp
  iStructNamed Htp
  imod sync.init_Mutex iprop(True) ⊤ _ $$ mu [] with #Hmu
  · inext; itrivial
  ipersist kv; ipersist ctx; ipersist callOpts
  imodintro
  iapply HΦ
  iexists tp
  isplitl []
  · ipureintro; rfl
  unfold txnObjAt
  isplitl []
  · ipureintro; exact Htpn
  iexists api, sl, slice.nil, slice.nil, slice.nil, [], [], [], false
  iframe #
  iframe
  ihave Hn1 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hn2 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hn3 := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hc1 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave Hc2 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave Hc3 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave #Hcn := comparesAt_nil (GF := GF)
  ihave #Hrn := reqOpsAt_nil (GF := GF)
  simp only [TxnBuild.empty, TxnModel.empty, List.map_nil]
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
