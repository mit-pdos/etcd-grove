/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.metricsTxnWrite.End.wp_proof
    (hEnd : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG))
    (hEndW : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro mw s γ kind
  wp_start as Htx
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, ⟨%ct, #Hct, #HctS⟩, ⟨%cr, #Hcr, #HcrS⟩, ⟨%cp, #Hcp, #HcpS⟩,
    ⟨%cdl, #Hcd, #HcdS⟩, ⟨%g, #Hg, #HgS⟩, -⟩
  iunfold counterSpec at HctS HcrS HcpS HcdS
  iunfold gaugeSpec at HgS
  icases HctS with ⟨#HctI, -⟩
  icases HcrS with ⟨-, #HcrA⟩
  icases HcpS with ⟨-, #HcpA⟩
  icases HcdS with ⟨-, #HcdA⟩
  icases HgS with ⟨-, -, #HgA⟩
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxn, mvcc.txnEndPost]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    -- `if sum > 1 { txnCounter.Inc() }`
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      -- the counters and the gauge
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `txnReadWrite`'s promoted `End`, `storeTxnRead.End`
      rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"End")]; wp_call
      (try wp_auto)
      wp_apply (hEnd tr s trace ti rt γ log rev) $$ [$Hs $Htr $Hidx $Hmu $HrevMu $Hti] as Hrd
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      (try itrivial)
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxn, mvcc.txnEndPost]
    iunfold mvcc.isTxnWrite at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `storeTxnWrite.End`
      wp_apply (hEndW tw s γ ilog pend) $$ [$Htw] as ⟨Hrd, #Hcert, Htok⟩
      (try wp_auto)
      iapply HΦ
      iframe Hrd Htok
      iexact Hcert

end proof

end EtcdGrove
end Perennial
