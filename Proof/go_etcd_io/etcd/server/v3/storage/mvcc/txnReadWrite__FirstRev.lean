/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__FirstRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__FirstRev

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

theorem mvcc.txnReadWrite.FirstRev.wp_proof
    (hFirstRev : mvcc.storeTxnCommon.FirstRev.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.FirstRev.spec (GF := GF) (hG := hG) := by
  intro trw s γ log rev crev Z
  wp_start as Hro
  iunfold mvcc.isRoTxnWrite at Hro
  icases Hro with ⟨%mw, Hf, Htx⟩
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  (try wp_auto)
  -- the promoted methods: `metricsTxnWrite`'s, the inner `txnReadWrite`'s, `storeTxnRead`'s
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  wp_apply (hFirstRev (mvcc.txCommon tr) (W64 crev)) $$ [$HfirstRevT]
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.isRoTxnWrite
  iexists mw
  iframe Hf
  iunfold mvcc.isTxnRead
  iexists trw, tr, trace, ti, rt, ranges
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
