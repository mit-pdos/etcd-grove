/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__If.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__If
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

theorem txnLeasing.If.wp_proof : txnLeasing.If.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b sl ms
  wp_start as ⟨Hown, #Hcs, %Hb⟩
  ihave #Hcmps := cmpsSetAt_cmpsAt sl ms $$ Hcs
  unfold ownTxnLeasing
  icases Hown with ⟨%t, %B, %csl, %tsl, %esl, %tops, %eops, Htxn, HB, #HBs, Hlkv, #HLKV, Hctx,
    #Hctxok, Hcsf, Hcsown, Hopst, Hopsown, Hopse, Heown, %Hops⟩
  unfold cmpsOwn
  icases Hcsown with ⟨%cvs, #Hcvs, Hcap, %Hclen, #Hcv⟩
  ihave #Hcs' := Hcs
  unfold cmpsSetAt
  icases Hcs' with ⟨%cs2, #Hsl, %Hlen2, #Hcv2⟩
  wp_auto
  wp_apply (wp_slice_append_persistent csl cvs sl cs2 DFrac.discard) $$ [$Hcvs $Hcap $Hsl] as %csl' ⟨#Hcvs', Hcap', -⟩
  (try wp_auto)
  ihave #HBs' := HBs
  iunfold txnBuilderSpecO at HBs'
  icases HBs' with ⟨#HIf, #HThen, #HElse, #HCommit⟩
  wp_apply_raw HIf $$ %(b.inner tops eops) %sl %ms [$HB $Hcmps]
  · ipureintro; exact Hb
  inext
  iintro HB
  (try wp_auto)
  iapply HΦ
  iexists t, B, csl', tsl, esl, tops, eops
  iframe
  iframe #
  isplitr
  · isplitr
    · ipureintro; simp [Hclen, Hlen2]
    · imodintro
      iintro %i %c %m %Hc %Hm
      simp only at Hm
      by_cases hi : i < cvs.length
      · rw [List.getElem?_append_left hi] at Hc
        rw [List.getElem?_append_left (by omega)] at Hm
        iapply Hcv $$ %i %c %m %Hc %Hm
      · rw [List.getElem?_append_right (by omega)] at Hc
        rw [List.getElem?_append_right (by omega)] at Hm
        rw [Hclen] at Hc
        iapply Hcv2 $$ %(i - b.cmps.length) %c %m %Hc %Hm
  first
    | (ipureintro; exact Hops)
    | (isplitr
       · ipureintro; exact Hops.1
       · ipureintro; exact Hops.2)

end proof

end leasing
end EtcdGrove
end Perennial
