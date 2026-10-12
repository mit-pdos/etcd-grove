/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Rev

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

theorem mvcc.metricsTxnWrite.Rev.wp_proof
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hRevW : mvcc.storeTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG) := by
  intro mw s γ kind
  wp_start as Htx
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    ihave #HtrT := Htr
    iunfold mvcc.storeTxnReadIs at HtrT
    iNamedSuffix HtrT "T"
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    wp_apply (hRev (mvcc.txCommon tr) _) $$ [$HrevT]
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, ranges
    iframe
    iframe #
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxn, mvcc.TxnKind.beginRev]
    iunfold mvcc.isTxnWrite at Htx
    iNamed Htx
    icases mvcc.storeTxnWriteIs_split tw s γ ilog pend $$ Htw with ⟨%chs, %ps, Htw, Hchs, Hkvs⟩
    (try wp_auto)
    wp_apply (hRevW tw s γ ilog pend chs ps false) $$ [$Htw] as Htw
    (try wp_auto)
    iapply HΦ
    iunfold mvcc.isTxnWrite
    iexists tw, ranges
    iframe Hmw
    iapply mvcc.storeTxnWriteIs_join $$ [$Htw $Hchs $Hkvs]

end proof

end EtcdGrove
end Perennial
