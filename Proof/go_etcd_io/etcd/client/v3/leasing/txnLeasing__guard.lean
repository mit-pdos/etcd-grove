/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__guard.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guard
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guardKeys
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guardRanges
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.guard.wp_proof
    (hGK : txnLeasing.guardKeys.spec (GF := GF) (hG := hG))
    (hGR : txnLeasing.guardRanges.spec (GF := GF) (hG := hG)) :
    txnLeasing.guard.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs dq sl os
  wp_start as ⟨Hlkvf, Hctxf, #HLKV, Hrd, #Hsr, #Hctx, #Hcc, #Hops⟩
  wp_auto
  wp_apply hGK $$ [$Hlkvf $HLKV $Hrd $Hops] as %c1 ⟨Hlkvf, Hrd, %ms1, #Hc1, Hcap1⟩
  (try wp_auto)
  wp_apply hGR $$ [$Hlkvf $Hctxf $HLKV $Hrd $Hsr $Hctx $Hcc $Hops] as %c2 %err
    ⟨Hlkvf, Hctxf, Hrd, Hres⟩
  ihave #Hc1' := (cmpsAt_listRel _ _).1 $$ Hc1
  icases Hc1' with ⟨%cs1, #Hcs1, #Hrel1⟩
  icases Hres with (⟨%Herr, %Hc2⟩ | ⟨%Herr, %ms2, #Hc2⟩)
  · subst Hc2
    (try wp_auto)
    wp_apply (wp_slice_append_persistent c1 cs1 slice.nil ([] : List go_etcd_io.etcd.client.v3.Cmp)
      (DFrac.own 1)) $$ [$Hcs1 $Hcap1] as %c3 ⟨#Hc3, -, -⟩
    · iapply ownSlice_nil
    iapply HΦ
    iframe
    ileft; ipureintro; exact Herr
  · ihave #Hc2' := (cmpsAt_listRel _ _).1 $$ Hc2
    icases Hc2' with ⟨%cs2, #Hcs2, #Hrel2⟩
    (try wp_auto)
    wp_apply (wp_slice_append_persistent c1 cs1 c2 cs2 DFrac.discard) $$ [$Hcs1 $Hcap1 $Hcs2]
      as %c3 ⟨#Hc3, -, -⟩
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; exact Herr
    iexists ms1 ++ ms2
    iapply (cmpsAt_listRel _ _).2
    iexists cs1 ++ cs2
    iframe Hc3
    iapply listRel_app
    iframe #

end proof

end leasing
end EtcdGrove
end Perennial
