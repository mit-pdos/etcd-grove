/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Changes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas

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

theorem mvcc.metricsTxnWrite.Changes.wp_proof
    (hCh : mvcc.storeTxnWrite.Changes.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ ilog pend puts deletes putSize crev Z ld
  wp_start as Htx
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  (try wp_auto)
  wp_apply (hCh trace tw s γ ilog pend crev Z ld) $$ [$Htw] as %chs %ps ⟨Hchs, Hkvs, %Hps, Htw⟩
  (try wp_auto)
  iapply HΦ
  iframe Hchs Hkvs
  isplitl []
  · ipureintro; exact Hps
  iunfold mvcc.isTxnWriteCore
  iexists tw, ranges
  iframe

/-- **The candidate `Changes`** (`specC`): of a write transaction, `spec`'s, the slice and the
changes' key-values given back to the transaction (`isTxnWrite_join`); of a read one, its
`txnReadWrite`'s (`nil`). -/
theorem mvcc.metricsTxnWrite.Changes.wp_proofC
    (hO : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hRW : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Changes.specC (GF := GF) (hG := hG) := by
  intro mw γ trace k
  cases k with
  | read σ =>
    wp_start as Htx
    icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hmv, Hrd, Hloan⟩
    iunfold mvcc.isTxnRead at Hrd
    iNamed Hrd
    (try wp_auto)
    wp_apply (hRW trw)
    (try wp_auto)
    iapply HΦ
    isplitl
    · iapply (mvcc.mvccTxn_read_eq mw γ trace σ).2
      iexists s
      iframe Hmv Hloan
      isplitr
      · ipureintro; exact Hl
      iunfold mvcc.isTxnRead
      iexists p, trw, tr, ti, rt, ranges
      iframe
      iframe #
    ipureintro; rfl
  | write σ pend =>
    iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
    icases (mvcc.mvccTxn_write_eq mw γ trace σ pend).1 $$ Htx
      with ⟨%s, %puts, %deletes, %putSize, %Hl, #Hs, Hwr, Hloan⟩
    iapply (hO trace mw s γ.st σ.log pend puts deletes putSize σ.crev iprop(True) false) $$ %Φ [Hwr]
    · iframe Hpkg Hwr
    inext
    iintro %chs %ps ⟨Hchs, Hkvs, %Hps, Hcore⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
    iapply HΦ
    isplitl
    · iapply (mvcc.mvccTxn_write_eq mw γ trace σ pend).2
      iexists s, puts, deletes, putSize
      iframe Hs Hloan
      isplitr
      · ipureintro; exact Hl
      iapply mvcc.isTxnWrite_join
      iframe Hcore Hchs Hkvs
    ipureintro
    simp only [mvcc.MTxn.pend]
    rw [← Hps, Hlen.1]
    word

end proof

end EtcdGrove
end Perennial
