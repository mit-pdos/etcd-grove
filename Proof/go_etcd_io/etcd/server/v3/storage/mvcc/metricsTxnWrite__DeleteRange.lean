/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__DeleteRange

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

theorem mvcc.metricsTxnWrite.DeleteRange.wp_proof
    (hDel : mvcc.storeTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro mw s γ ilog pend puts deletes putSize key endk k e
  wp_start as ⟨Htx, #Hkey, #Hend, %Hb⟩
  have hpm := mvcc.putMax_le γ
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  (try wp_auto)
  wp_apply (hDel tw s γ ilog pend key endk k e) $$ [$Htw $Hkey $Hend] as %n %rev ⟨Htw, %Hnr⟩
  · ipureintro; exact Hb
  (try wp_auto)
  iapply HΦ
  isplitl [Hmw Htw]
  · iunfold mvcc.isTxnWrite
    iexists tw, ranges
    iframe Htw
    iexact Hmw
  ipureintro; exact Hnr

end proof

end EtcdGrove
end Perennial
