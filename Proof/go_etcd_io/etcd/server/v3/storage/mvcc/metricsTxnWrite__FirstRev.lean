/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__FirstRev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__FirstRev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.metricsTxnWrite.FirstRev.wp_proof
    (hRev : mvcc.storeTxnCommon.FirstRev.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ log rev crev Z
  wp_start as Htx
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) _) $$ [$HfirstRevT]
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.isTxnRead
  iexists p, trw, tr, ti, rt, ranges
  iframe
  iframe #

/-- **The candidate `FirstRev`** (`specC`): a read transaction's, `spec`'s; a write transaction's
is not proved yet (today's `FirstRev` spec is of read transactions). -/
theorem mvcc.metricsTxnWrite.FirstRev.wp_proofC (hO : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.FirstRev.specC (GF := GF) (hG := hG) := by
  intro mw γ trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  cases k with
  | read σ =>
    icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hs, Hrd, Hloan⟩
    iapply (hO trace mw s γ.st σ.log (W64 (σ.rev : Int)) σ.crev iprop(True)) $$ %Φ [Hrd]
    · iframe Hpkg Hrd
    inext
    iintro Hrd
    iapply HΦ
    iapply (mvcc.mvccTxn_read_eq mw γ trace σ).2
    iexists s; iframe Hs Hrd Hloan; ipureintro; exact Hl
  | write σ pend =>
    sorry

end proof

end EtcdGrove
end Perennial
