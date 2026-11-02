/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Put
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Put

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

theorem mvcc.metricsTxnWrite.Put.wp_proof (hPut : mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ ilog pend puts deletes putSize key value k v leaseID L crev Z
  wp_start as ⟨Htx, #Hkey, #Hval, %Hklen, Hown, %Hlease⟩
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  icases Htrc with ⟨%te, Htrc⟩
  (try wp_auto)
  wp_apply (hPut trace tw s γ ilog pend key value k v leaseID L te crev Z)
    $$ [$Htw $Hkey $Hval $Hown $Htrc] as ⟨Htw, Hown, Htrc⟩
  · ipureintro; exact ⟨Hklen, Hlease⟩
  (try wp_auto)
  iapply HΦ
  iframe Hown
  ihave Htrc : iprop(∃ te' : Bool, traceutil.ownTrace trace te') $$ [Htrc]
  · iexists te; iexact Htrc
  iunfold mvcc.isTxnWrite
  iexists tw, ranges
  iframe Htw Htrc
  iexact Hmw

/-- **The candidate `Put`** (`specC`): `spec`'s, the counters existential. -/
theorem mvcc.metricsTxnWrite.Put.wp_proofC (hO : mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Put.specC (GF := GF) (hG := hG) := by
  intro mw γ trace σ pend key value k v leaseID L
  iintro %Φ ⟨#Hpkg, Htx, #Hk, #Hv, %Hklen, Hown, %Hlease⟩ HΦ
  icases (mvcc.mvccTxn_write_eq mw γ trace σ pend).1 $$ Htx
    with ⟨%s, %puts, %deletes, %putSize, %Hl, #Hs, Hwr, Hloan⟩
  iapply (hO trace mw s γ.st σ.log pend puts deletes putSize key value k v leaseID L σ.crev iprop(True))
    $$ %Φ [Hwr Hown]
  · iframe Hpkg Hwr Hk Hv
    simp only [mvcc.mvccLeases]
    iframe Hown
    ipureintro; exact ⟨Hklen, Hlease⟩
  inext
  iintro ⟨Hwr, Hown⟩
  iapply HΦ
  simp only [mvcc.mvccLeases]
  iframe Hown
  iapply (mvcc.mvccTxn_write_eq mw γ trace σ (pend ++ [.put k v leaseID])).2
  iexists s, puts + W64 1, deletes, putSize + (key.len + value.len)
  iframe Hs Hloan Hwr
  ipureintro; exact Hl

end proof

end EtcdGrove
end Perennial
