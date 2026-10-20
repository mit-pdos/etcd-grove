/-
Lean-first (no Rocq counterpart).

The proof of `callTxn`: the comparisons and operations (`cmpsFor`, `opsOf`), the builder
(`client_Txn_st`, `If`, `Then`, `Else`: the model's transaction, `clientTxn`), `txn_Commit_st`,
then the output from the reply (`txnRes`, `withRes`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callTxn
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpsFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.opsOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.thenOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.elseOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.txnRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.withRes
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem callTxn.wp_proof (wp_cmpsFor : cmpsFor.spec (GF := GF) (hG := hG))
    (wp_opsOf : opsOf.spec (GF := GF) (hG := hG)) (wp_thenOf : thenOf.spec (GF := GF) (hG := hG))
    (wp_elseOf : elseOf.spec (GF := GF) (hG := hG)) (wp_txnRes : txnRes.spec (GF := GF) (hG := hG))
    (wp_withRes : withRes.spec (GF := GF) (hG := hG)) :
    callTxn.spec (GF := GF) (hG := hG) := by
  intro _ cl ep V E γr cid mid hAs x cs t e Q hx hne
  obtain ⟨hn, hcs, ht, he⟩ := decIn_txn x cs t e hx
  wp_start as ⟨#Hcl, #Hone, #Hrpc, Hau⟩
  wp_auto
  wp_apply wp_elseOf x as %esl ⟨Hesl, -⟩
  wp_apply wp_opsOf esl (elseOfL x) (DFrac.own 1) e he $$ [$Hesl] as %eos ⟨-, #Heos⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_thenOf x as %tsl ⟨Htsl, -⟩
  wp_apply wp_opsOf tsl (thenOfL x) (DFrac.own 1) t ht $$ [$Htsl] as %tos ⟨-, #Htos⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_cmpsFor x cs hcs hn $$ [] as %csl #Hcsl
  · iframe #
  (try wp_auto)
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #Hc0
  ihave #Hc0' : committedAtLeast (GF := GF) γr (W64 0) $$ []
  · iunfold committedAtLeast
    iExactEq Hc0; rfl
  (try wp_auto)
  wp_apply (client_Txn_st cl ep V context.backgroundCtxVal cd) as %tv ⟨%tp, %Htv, Hobj, Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (client.v3.txn.wp_If tp ep context.backgroundCtxVal cd TxnBuild.empty csl
      (cs.map linkv.cmpOf)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; simp [TxnBuild.empty]
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Then tp ep context.backgroundCtxVal cd _ tos (t.map clientOp)
      (t.map clientTOp)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨txnOpOf_clientOps t, rfl, rfl⟩
  (try wp_auto)
  wp_apply (client.v3.txn.wp_Else tp ep context.backgroundCtxVal cd _ eos (e.map clientOp)
      (e.map clientTOp)) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨txnOpOf_clientOps e, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp ep context.backgroundCtxVal cd
      ⟨clientTxn cs t e, true, true, true⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, clientTxn]
  (try wp_auto)
  wp_apply (txn_Commit_st tp ep E γr cid mid context.backgroundCtxVal cd
      ⟨clientTxn cs t e, true, true, true⟩ [] Q cs t e rfl hne) $$ [Hobj Hau Hkt]
    as %resp %err Hout
  · iframe #
    iframe
  icases Hout with (⟨%Herr, %m, %σ, #Hm, HQ, %Hσ⟩ | %Herr)
  · subst Herr
    obtain ⟨hok, hrel, hrev, hb⟩ := Hσ
    iunfold txnRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hsl, #Hms⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    wp_apply wp_elseOf x as %esl2 ⟨Hesl2, -⟩
    (try wp_auto)
    have hrel' := hrel
    rw [txnOf_branch'] at hrel'
    cases hs : m.succeeded
    · -- the else-branch
      rw [hs] at hrel'
      simp only [Bool.false_eq_true, ↓reduceIte] at hrel'
      have hdec := he
      wp_pures
      ipersist Hesl2
      (try wp_auto)
      wp_apply wp_txnRes esl2 _ _ sl ps _ m.resps hdec hrel' $$ [] as %rsl ⟨Hrsl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_withRes _ rsl _ (DFrac.own 1) $$ [Hrsl] as %o' ⟨-, %Ho'⟩
      · iframe
      iapply HΦ
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [Ho', hrev]
      unfold txnBase
      congr 2
      rw [← hs, hok]
      rfl
    · -- the then-branch
      rw [hs] at hrel'
      simp only [↓reduceIte] at hrel'
      have hdec := ht
      wp_pures
      (try wp_auto)
      wp_apply wp_thenOf x as %osl ⟨Hosl, -⟩
      (try wp_auto)
      ipersist Hosl
      (try wp_auto)
      wp_apply wp_txnRes osl _ _ sl ps _ m.resps hdec hrel' $$ [] as %rsl ⟨Hrsl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_withRes _ rsl _ (DFrac.own 1) $$ [Hrsl] as %o' ⟨-, %Ho'⟩
      · iframe
      iapply HΦ
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [Ho', hrev]
      unfold txnBase
      congr 2
      rw [← hs, hok]
      rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    ileft
    ipureintro; rfl
end proof

end linkvtxn
end EtcdGrove
end Perennial
