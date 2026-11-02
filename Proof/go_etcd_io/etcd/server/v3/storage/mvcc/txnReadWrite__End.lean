/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

theorem mvcc.txnReadWrite.End.wp_proof
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG) := by
  intro trace trw s γ log rev crev Z
  wp_start as Hro
  iunfold mvcc.isRoTxnWrite at Hro
  icases Hro with ⟨%mw, Hf, Htx⟩
  (try wp_auto)
  ihave Htx' : mvcc.isTxn mw s γ trace (.read log rev) crev Z $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev Z $$ Htx'
  ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd trace mw s γ (.read log rev) crev Z) $$ [$Hpkg $Htx' $Hep] as ⟨Hrd, #HZ, -, Htrc⟩
  (try wp_auto)
  iapply HΦ
  iframe Hrd HZ Htrc

/-- **The candidate `End`** of a read-only write transaction (`specC`): `spec`'s, the reader's ticket
back to the readers' pool for the thread token. -/
theorem mvcc.txnReadWrite.End.wp_proofC (hO : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.End.specC (GF := GF) (hG := hG) := by
  intro trw γ trace σ
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  icases (mvcc.mvccTxn_ro_eq trw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hs, Hro, Hloan⟩
  ihave #Hs1 := Hs
  iunfold mvcc.isMvccI at Hs1
  icases Hs1 with ⟨-, -, -, #Hpool, -, -⟩
  iapply wp_fupd
  wp_apply (hO trace trw s γ.st σ.log (W64 (σ.rev : Int)) σ.crev iprop(True)) $$ [Hro]
    as ⟨Hrd, -, Htrc⟩
  · iframe Hro
    try iframe #
  imod threadPool.giveBack mvcc.tixN γ.tl _ ⊤ (by simp) $$ [$Hpool $Hloan $Hrd] with Htt
  imodintro
  iapply HΦ
  iframe Htt Htrc

end proof

end EtcdGrove
end Perennial
