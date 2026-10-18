/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Put

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

theorem mvcc.metricsTxnWrite.Put.wp_proof (hPut : mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ ilog pend puts deletes putSize key value k v leaseID L crev Z
  wp_start as ⟨Htx, #Hkey, #Hval, Hown, %Hlease⟩
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  icases Htrc with ⟨%te, Htrc⟩
  (try wp_auto)
  wp_apply (hPut trace tw s γ ilog pend key value k v leaseID L te crev Z)
    $$ [$Htw $Hkey $Hval $Hown $Htrc] as ⟨Htw, Hown, Htrc⟩
  · ipureintro; exact Hlease
  (try wp_auto)
  iapply HΦ
  iframe Hown
  ihave Htrc : iprop(∃ te' : Bool, traceutil.ownTrace trace te') $$ [Htrc]
  · iexists te; iexact Htrc
  iunfold mvcc.isTxnWrite
  iexists tw, ranges
  iframe Htw Htrc
  iexact Hmw

end proof

end EtcdGrove
end Perennial
