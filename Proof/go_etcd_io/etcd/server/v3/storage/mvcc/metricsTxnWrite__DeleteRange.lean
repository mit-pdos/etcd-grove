/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__DeleteRange

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

theorem mvcc.metricsTxnWrite.DeleteRange.wp_proof
    (hDel : mvcc.storeTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ ilog pend puts deletes putSize key endk k e L crev Z
  wp_start as ⟨Htx, #Hkey, #Hend, Hown⟩
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  (try wp_auto)
  wp_apply (hDel trace tw s γ ilog pend key endk k e L crev Z) $$ [$Htw $Hkey $Hend $Hown]
    as %n %rev ⟨Htw, Hown, %Hnr⟩
  (try wp_auto)
  iapply HΦ
  iframe Hown
  isplitl [Hmw Htw Htrc]
  · iunfold mvcc.isTxnWrite
    iexists tw, ranges
    iframe Htw Htrc
    iexact Hmw
  ipureintro; exact Hnr

/-- **The candidate `DeleteRange`** (`specC`): `spec`'s, the counters existential. -/
theorem mvcc.metricsTxnWrite.DeleteRange.wp_proofC
    (hO : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.DeleteRange.specC (GF := GF) (hG := hG) := by
  intro mw γ trace σ pend key endk k e L
  iintro %Φ ⟨#Hpkg, Htx, #Hk, #He, Hown⟩ HΦ
  icases (mvcc.mvccTxn_write_eq mw γ trace σ pend).1 $$ Htx
    with ⟨%s, %puts, %deletes, %putSize, %Hl, #Hs, Hwr, Hloan⟩
  iapply (hO trace mw s γ.st σ.log pend puts deletes putSize key endk k e L σ.crev iprop(True))
    $$ %Φ [Hwr Hown]
  · iframe Hpkg Hwr Hk He
    simp only [mvcc.mvccLeases]
    iexact Hown
  inext
  iintro %n %rev ⟨Hwr, Hown, %Hn⟩
  iapply HΦ
  simp only [mvcc.mvccLeases]
  iframe Hown
  isplitl
  · iapply (mvcc.mvccTxn_write_eq mw γ trace σ _).2
    iexists s, puts, deletes + W64 1, putSize
    iframe Hs Hloan Hwr
    ipureintro; exact Hl
  ipureintro; exact Hn

end proof

end EtcdGrove
end Perennial
