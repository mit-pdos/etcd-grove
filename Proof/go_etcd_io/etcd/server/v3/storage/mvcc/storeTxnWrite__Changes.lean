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
  ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
  iapply HΦ
  iframe Hchs Hkvs
  isplitl []
  · ipureintro; exact Hps
  iunfold mvcc.storeTxnWriteCore
  iexists trace, ti, bt, Locked, ntok
  simp only [named, mvcc.idxWriterB_false]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres
  iframe #
  ipureintro; exact ⟨Hbudget, ⟨Hps, Hlen⟩, Hne, Htrnn⟩

end proof

end EtcdGrove
end Perennial
