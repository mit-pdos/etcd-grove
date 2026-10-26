/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__Rev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

theorem mvcc.readView.Rev.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Rev.spec (GF := GF) (hG := hG) := by
  intro rv s γ
  wp_start as ⟨#Hrv, Hrd⟩
  iunfold mvcc.isReadView at Hrv
  icases Hrv with ⟨%kv, Hrv⟩
  iNamed Hrv
  ihave %Hkvok := mvcc.kvOver_ok kv s $$ Hkvo
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  -- `rv.kv.Read(mode, t)`: the store's
  imod ownToks_0 (GF := GF) γ.revs with Hnone
  imod mvcc.idxCert_nil (GF := GF) γ.idx with #Hc0
  imod mvcc.crevLb_neg γ.idx with #Hlbn
  wp_apply (mvcc.kvOver_Read hRead kty kvv s γ _ t 0 [] true (-1) iprop(True) none) $$ [$Hkvo $Hs $Hrd $Hnone $Hc0 $Hlbn $Htrc]
    as %mw ⟨%log, %rev, %crev, Htx, -, -, -⟩
  · isplitr
    · iintro !>; itrivial
    isplitr
    · ipureintro; exact Ht
    unfold mvcc.logLent; itrivial
  (try wp_auto)
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  -- `tr.Rev()`: the promoted methods down to `storeTxnCommon.Rev`
  rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnRead.ty) (m := go!"Rev")]; wp_call
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  -- the deferred `tr.End()`: `metricsTxnWrite.End`
  ihave Htx : mvcc.isTxnRead mw s γ t log rev crev iprop(True) $$ [Hmw Htrw Hrd Hmu HrevMu Hti Htrc]
  · iunfold mvcc.isTxnRead
    iexists p, trw, tr, ti, rt, ranges
    iframe
    iframe #
  ihave Htx' : mvcc.isTxn mw s γ t (.read log rev) crev iprop(True) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev iprop(True) $$ Htx'
  ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd t mw s γ (.read log rev) crev iprop(True)) $$ [$Htx' $Hep] as ⟨Hrd, -, -, -⟩
  (try wp_auto)
  iapply HΦ
  iframe Hrd
  iexists log
  withPhys_simp
  iframe HcertT
  ipureintro
  exact ⟨HneT, HrevT⟩

end proof

end EtcdGrove
end Perennial
