/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

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

theorem mvcc.storeTxnWrite.Changes.wp_proof :
    mvcc.storeTxnWrite.Changes.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend
  wp_start as Htw
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  (try wp_auto)
  iapply HΦ
  iframe Hchs Hkvs
  isplitl []
  · ipureintro; exact Hps
  iintro Hchs Hkvs
  iunfold mvcc.storeTxnWriteIs
  iexists trace, ti, bt, Locked, chs, ps, ntok
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne⟩

end proof

end EtcdGrove
end Perennial
