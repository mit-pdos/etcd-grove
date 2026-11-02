/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Range

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.metricsTxnWrite.Range.wp_proof
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ kind ctx cd todo key endk k e ro crev Z
  wp_start as ⟨Htx, #Hctx, #Hkey, #Hend⟩
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    icases Htrc with ⟨%te, Htrc⟩
    (try wp_auto)
    -- `tw.TxnWrite.Range(...)`: `txnReadWrite`'s promoted `Range`, then `storeTxnRead`'s
    -- (`storeTxnCommon.Range` on its embedded field)
    wp_method_call; wp_call
    (try wp_auto)
    wp_method_call; wp_call
    (try wp_auto)
    ihave #Hs' : mvcc.isStore s (γ.withPhys p) $$ []
    · rw [mvcc.isStore_withPhys]; iexact Hs
    wp_apply (hRange tr s trace ti rt (γ.withPhys p) log rev ctx cd todo key endk k e ro te crev Z)
      $$ [$Hs' $Htr $Hrd $Hti $Hctx $Hkey $Hend $Hmu $Htrc]
      as %r %err ⟨%Htodo, Hti, Hmu, Hrd, Htrc, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout
    ihave Htrc : iprop(∃ te' : Bool, traceutil.ownTrace trace te') $$ [Htrc]
    · iexists te; iexact Htrc
    iunfold mvcc.isTxnRead
    iexists p, trw, tr, ti, rt, (ranges + W64 1)
    iframe
    iframe #
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    iunfold mvcc.isTxnWrite at Htx
    iNamed Htx
    icases Htrc with ⟨%te, Htrc⟩
    (try wp_auto)
    -- `tw.TxnWrite.Range(...)`: `storeTxnWrite.Range`
    wp_apply (hRangeW trace tw s γ ilog pend ctx cd todo key endk k e ro te crev Z)
      $$ [$Htw $Hctx $Hkey $Hend $Htrc] as %r %err ⟨%Htodo, Htw, Htrc, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout
    ihave Htrc : iprop(∃ te' : Bool, traceutil.ownTrace trace te') $$ [Htrc]
    · iexists te; iexact Htrc
    iunfold mvcc.isTxnWrite
    iexists tw, (ranges + W64 1)
    iframe

/-- **The candidate `Range`** (`specC`): `spec`'s, at the transaction's kind. -/
theorem mvcc.metricsTxnWrite.Range.wp_proofC (hO : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.specC (GF := GF) (hG := hG) := by
  intro mw γ trace k ctx cd todo key endk kk e ro
  iintro %Φ ⟨#Hpkg, Htx, Hctx, #Hk, #He⟩ HΦ
  cases k with
  | read σ =>
    icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hs, Hrd, Hloan⟩
    iapply (hO trace mw s γ.st (.read σ.log (W64 (σ.rev : Int))) ctx cd todo key endk kk e ro σ.crev
      iprop(True)) $$ %Φ [Hrd Hctx]
    · iframe Hpkg Hctx Hk He
      simp only [mvcc.isTxn]
      iexact Hrd
    inext
    iintro %r %err ⟨%Hr, Hrd, Hout⟩
    iapply HΦ
    simp only [mvcc.isTxn] at *
    isplitr
    · ipureintro; exact Hr
    isplitr [Hout]
    · iapply (mvcc.mvccTxn_read_eq mw γ trace σ).2
      iexists s; iframe Hs Hloan Hrd; ipureintro; exact Hl
    simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev, mvcc.MTxn.readLog, mvcc.MTxn.readRev,
      mvcc.MTxn.state]
    iexact Hout
  | write σ pend =>
    icases (mvcc.mvccTxn_write_eq mw γ trace σ pend).1 $$ Htx
      with ⟨%s, %puts, %deletes, %putSize, %Hl, #Hs, Hwr, Hloan⟩
    iapply (hO trace mw s γ.st (.write σ.log pend puts deletes putSize) ctx cd todo key endk kk e ro
      σ.crev iprop(True)) $$ %Φ [Hwr Hctx]
    · iframe Hpkg Hctx Hk He
      simp only [mvcc.isTxn]
      iexact Hwr
    inext
    iintro %r %err ⟨%Hr, Hwr, Hout⟩
    iapply HΦ
    simp only [mvcc.isTxn] at *
    isplitr
    · ipureintro; exact Hr
    isplitr [Hout]
    · iapply (mvcc.mvccTxn_write_eq mw γ trace σ pend).2
      iexists s, puts, deletes, putSize; iframe Hs Hloan Hwr; ipureintro; exact Hl
    simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev, mvcc.MTxn.readLog, mvcc.MTxn.readRev,
      mvcc.MTxn.state]
    iexact Hout

end proof

end EtcdGrove
end Perennial
