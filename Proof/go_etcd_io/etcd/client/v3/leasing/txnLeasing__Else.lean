/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__Else.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__Else
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.Else.wp_proof : txnLeasing.Else.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b sl os ops
  wp_start as ⟨Hown, #Hos, ⟨%Hmap, %Hb1⟩⟩
  ihave #HosT := opsAt_leaves sl os ops Hmap $$ Hos
  unfold ownTxnLeasing
  icases Hown with ⟨%t, %B, %csl, %tsl, %esl, %tops, %eops, Htxn, HB, #HBs, Hlkv, #HLKV, Hctx,
    #Hctxok, Hcsf, Hcsown, Hopst, Hopsown, Hopse, Heown, %Hops⟩
  unfold opsOwn
  icases Heown with ⟨%vs, #Hvs, Hcap, %Hvlen, #Hv⟩
  ihave #Hos' := Hos
  unfold opsAt
  icases Hos' with ⟨%vs2, #Hsl, %Hlen2, #Hv2⟩
  wp_auto
  wp_apply (wp_slice_append_persistent esl vs sl vs2 DFrac.discard) $$ [$Hvs $Hcap $Hsl] as %sl' ⟨#Hvs', Hcap', -⟩
  (try wp_auto)
  ihave #HBs' := HBs
  iunfold txnBuilderSpecO at HBs'
  icases HBs' with ⟨#HIf, #HThen, #HElse, #HCommit⟩
  wp_apply_raw HElse $$ %(b.inner tops eops) %sl %(os.map OpT.leaf) %ops [$HB $HosT]
  · ipureintro; exact ⟨txnOps_leaves os ops Hmap, Hb1⟩
  inext
  iintro HB
  (try wp_auto)
  iapply HΦ
  iexists t, B, csl, tsl, sl', tops, eops ++ ops
  iframe
  iframe #
  isplitr
  · isplitr
    · ipureintro; simp [Hvlen, Hlen2]
    · imodintro
      iintro %i %v %o %Hc %Hm
      simp only at Hm
      by_cases hi : i < vs.length
      · rw [List.getElem?_append_left hi] at Hc
        rw [List.getElem?_append_left (by omega)] at Hm
        iapply Hv $$ %i %v %o %Hc %Hm
      · rw [List.getElem?_append_right (by omega)] at Hc
        rw [List.getElem?_append_right (by omega)] at Hm
        rw [Hvlen] at Hc
        iapply Hv2 $$ %(i - b.elseOs.length) %v %o %Hc %Hm
  have Hnew : b.thenOs.mapM txnOpOf = some tops ∧ (b.elseOs ++ os).mapM txnOpOf = some (eops ++ ops) := ⟨Hops.1, mapM_txnOpOf_append _ _ _ _ Hops.2 (mapM_of_map_some os ops Hmap)⟩
  first
    | (ipureintro; exact Hnew)
    | (isplitr
       · ipureintro; exact Hnew.1
       · ipureintro; exact Hnew.2)

end proof

end leasing
end EtcdGrove
end Perennial
