/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.metricsTxnWrite.End.wp_proof
    (hEnd : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev
  wp_start as Htx
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, ⟨%ct, #Hct, #HctS⟩, ⟨%cr, #Hcr, #HcrS⟩, ⟨%cp, #Hcp, #HcpS⟩,
    ⟨%cdl, #Hcd, #HcdS⟩, ⟨%g, #Hg, #HgS⟩⟩
  iunfold counterSpec at HctS HcrS HcpS HcdS
  iunfold gaugeSpec at HgS
  icases HctS with ⟨#HctI, -⟩
  icases HcrS with ⟨-, #HcrA⟩
  icases HcpS with ⟨-, #HcpA⟩
  icases HcdS with ⟨-, #HcdA⟩
  icases HgS with ⟨-, -, #HgA⟩
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
    iexact Hrd

end proof

end EtcdGrove
end Perennial
