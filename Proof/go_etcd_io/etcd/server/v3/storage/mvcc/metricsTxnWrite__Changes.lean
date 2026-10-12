/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Changes

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

theorem mvcc.metricsTxnWrite.Changes.wp_proof
    (hCh : mvcc.storeTxnWrite.Changes.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG) := by
  intro mw s γ ilog pend puts deletes putSize
  wp_start as Htx
  iunfold mvcc.isTxnWrite at Htx
  iNamed Htx
  (try wp_auto)
  wp_apply (hCh tw s γ ilog pend) $$ [$Htw] as %chs %ps ⟨Hchs, Hkvs, %Hps, Htw⟩
  (try wp_auto)
  iapply HΦ
  iframe Hchs Hkvs
  isplitl []
  · ipureintro; exact Hps
  iunfold mvcc.isTxnWriteCore
  iexists tw, ranges
  iframe

end proof

end EtcdGrove
end Perennial
