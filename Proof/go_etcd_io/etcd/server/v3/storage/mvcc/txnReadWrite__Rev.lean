/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev

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

theorem mvcc.txnReadWrite.Rev.wp_proof
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Rev.spec (GF := GF) (hG := hG) := by
  intro trw s γ log rev
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
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  iapply HΦ
  isplitl
  ·
    iunfold mvcc.isRoTxnWrite
    iexists mw
    iframe Hf
    iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, ranges
    iframe
    iframe #
  ipureintro
  exact ⟨HneT, HrevT⟩

end proof

end EtcdGrove
end Perennial
