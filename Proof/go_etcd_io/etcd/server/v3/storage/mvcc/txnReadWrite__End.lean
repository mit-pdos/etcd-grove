/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

theorem mvcc.txnReadWrite.End.wp_proof
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG) := by
  intro trw s γ log rev
  wp_start as Hro
  iunfold mvcc.isRoTxnWrite at Hro
  icases Hro with ⟨%mw, Hf, Htx⟩
  (try wp_auto)
  ihave Htx' : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ $$ Htx'
  wp_apply (hEnd mw s γ (.read log rev)) $$ [$Hpkg $Htx'] as ⟨Hrd, -⟩
  (try wp_auto)
  iapply HΦ
  iexact Hrd

end proof

end EtcdGrove
end Perennial
