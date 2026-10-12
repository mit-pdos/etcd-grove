/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite


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

theorem mvcc.NewReadOnlyTxnWrite.wp_proof :
    mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev
  wp_start as Htx
  (try wp_auto)
  wp_alloc trw as Htrw
  (try wp_auto)
  iStructNamedPrefix Htrw "W"
  iapply HΦ
  iunfold mvcc.isRoTxnWrite
  iexists mw
  iframe

end proof

end EtcdGrove
end Perennial
