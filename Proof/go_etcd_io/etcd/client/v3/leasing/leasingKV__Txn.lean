/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Txn.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Txn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.Txn.wp_proof : leasingKV.Txn.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs
  wp_start as ⟨#Hlkv, #Hctx⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %c, %ccs, %cancel, %osl, -, -, #Hkv, -, -, -, -, -, -, #HTxn, -⟩
  wp_auto
  iunfold isEtcdTxnKVO at HTxn
  wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
  (try wp_auto)
  wp_alloc txn as Htxn
  iStructNamed Htxn
  wp_auto
  iapply HΦ
  unfold ownTxnLeasing
  iexists t, B, slice.nil, slice.nil, slice.nil, [], []
  rw [show LTxnBuild.empty.inner [] [] = TxnBuild.empty from rfl]
  iframe Txn lkv ctx cs opst opse HBs Hlkv Hctx HB
  ihave #Hnc := ownSlice_nil (V := go_etcd_io.etcd.client.v3.Cmp) (GF := GF) DFrac.discard
  ihave #Hno := ownSlice_nil (V := go_etcd_io.etcd.client.v3.Op) (GF := GF) DFrac.discard
  ihave Hcc := ownSliceCap_nil (V := go_etcd_io.etcd.client.v3.Cmp) (GF := GF)
  ihave Hco1 := ownSliceCap_nil (V := go_etcd_io.etcd.client.v3.Op) (GF := GF)
  ihave Hco2 := ownSliceCap_nil (V := go_etcd_io.etcd.client.v3.Op) (GF := GF)
  unfold cmpsOwn opsOwn
  isplitl [Hcc]
  · iexists []
    iframe Hnc Hcc
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %c %m %h
    simp at h
  isplitl [Hco1]
  · iexists []
    iframe Hno Hco1
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %o %h
    simp at h
  isplitl [Hco2]
  · iexists []
    iframe Hno Hco2
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %v %o %h
    simp at h
  ipureintro; exact ⟨rfl, rfl⟩

end proof

end leasing
end EtcdGrove
end Perennial
