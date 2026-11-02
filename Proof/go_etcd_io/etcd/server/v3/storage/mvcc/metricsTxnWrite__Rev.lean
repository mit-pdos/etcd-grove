/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Rev

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

theorem mvcc.metricsTxnWrite.Rev.wp_proof
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hRevW : mvcc.storeTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ kind crev Z
  wp_start as Htx
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    ihave #HtrT := Htr
    iunfold mvcc.storeTxnReadIs at HtrT
    iNamedSuffix HtrT "T"
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    wp_apply (hRev (mvcc.txCommon tr) _) $$ [$HrevT]
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.isTxnRead
    iexists p, trw, tr, ti, rt, ranges
    iframe
    iframe #
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev]
    iunfold mvcc.isTxnWrite at Htx
    iNamed Htx
    icases mvcc.storeTxnWriteIs_split tw s γ ilog pend crev Z $$ Htw with ⟨%chs, %ps, Htw, Hchs, Hkvs⟩
    (try wp_auto)
    wp_apply (hRevW trace tw s γ ilog pend chs ps false crev Z) $$ [$Htw] as Htw
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.isTxnWrite
    iexists tw, ranges
    iframe Hmw Htrc
    iapply mvcc.storeTxnWriteIs_join tw s γ ilog pend chs ps crev Z $$ [$Htw $Hchs $Hkvs]

/-- **The candidate `Rev`** (`specC`): `spec`'s, at the transaction's kind (a write transaction's
revision is its log's last, the state's). -/
theorem mvcc.metricsTxnWrite.Rev.wp_proofC (hO : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Rev.specC (GF := GF) (hG := hG) := by
  intro mw γ trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  cases k with
  | read σ =>
    icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hs, Hrd, Hloan⟩
    iapply (hO trace mw s γ.st (.read σ.log (W64 (σ.rev : Int))) σ.crev iprop(True)) $$ %Φ [Hrd]
    · iframe Hpkg
      simp only [mvcc.isTxn]
      iexact Hrd
    inext
    iintro Hrd
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev, mvcc.MTxn.state]
    iapply HΦ
    iapply (mvcc.mvccTxn_read_eq mw γ trace σ).2
    iexists s; iframe Hs Hloan Hrd; ipureintro; exact Hl
  | write σ pend =>
    icases (mvcc.mvccTxn_write_eq mw γ trace σ pend).1 $$ Htx
      with ⟨%s, %puts, %deletes, %putSize, %Hl, #Hs, Hwr, Hloan⟩
    iapply (hO trace mw s γ.st (.write σ.log pend puts deletes putSize) σ.crev iprop(True)) $$ %Φ [Hwr]
    · iframe Hpkg
      simp only [mvcc.isTxn]
      iexact Hwr
    inext
    iintro Hwr
    have hrev : (W64 ((σ.log.length : Int) - 1) : w64) = W64 ((σ.rev : Nat) : Int) := by
      unfold mvcc.MvccState.rev; congr 1; omega
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev, mvcc.MTxn.state]
    rw [hrev]
    iapply HΦ
    iapply (mvcc.mvccTxn_write_eq mw γ trace σ pend).2
    iexists s, puts, deletes, putSize; iframe Hs Hloan Hwr; ipureintro; exact Hl

end proof

end EtcdGrove
end Perennial
