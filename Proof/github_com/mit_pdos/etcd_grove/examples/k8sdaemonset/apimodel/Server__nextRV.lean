/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__nextRV.lean`.
Lean-first. The receipt is the call of `rvString`'s resolution step (a pure Go instruction); with
the version's earlier receipts it bounds the counter below `2 ^ 63`, so `rev + 1` does not wrap.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__nextRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.rvString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem Server.nextRV.wp_proof (wp_rvString : rvString.spec (GF := GF) (hG := hG)) :
    Server.nextRV.spec (GF := GF) (hG := hG) := by
  intro _ s rvs n
  wp_start as ⟨Hrev, #Hrvs, Hm, Hr, %Hn⟩
  wp_auto
  wp_apply +noauto wp_rvString
  wp_pure
  wp_pure
  wp_bind (App (Val (GoInstruction (GoZeroVal _))) (Val _))
  iapply wp_go_step_receipt'
  · exact isPanic_intoVal _
  inext
  iintro Hr1 -
  ihave ⟨%Hlt, Hr⟩ := receipt_add_one_lt (GF := GF) (n.toNat - 1) $$ [Hr1 Hr]
  · iframe
  have hn1 : n.toNat - 1 + 1 = n.toNat := by omega
  rw [hn1] at Hlt
  have hno : (n + W64 1).toNat = n.toNat + 1 := by
    have : receiptBound GF ≤ 2 ^ 63 := Hn.2
    word
  rw [hn1]
  wp_auto
  wp_apply (wp_mapInsert go.string rvs (issuedMap n.toNat) (rvStr (n + W64 1)) (n + W64 1)) $$ [Hm] as Hm
  · iexact Hm
  iapply HΦ
  have hw : W64 ((BitVec.toNat n : Int) + 1) = n + W64 1 := by word
  have hm : issuedMap (BitVec.toNat n + 1) = <[rvStr (n + W64 1) := n + W64 1]> (issuedMap n.toNat) := by
    simp only [issuedMap, rvStr]
    rw [hw]
  rw [hm]
  iframe
  ipureintro
  exact hno

end proof

end apimodel
end EtcdGrove
end Perennial
