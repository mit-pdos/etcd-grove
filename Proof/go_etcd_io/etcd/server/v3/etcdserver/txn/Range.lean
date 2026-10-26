/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeSecObserve
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.Range.wp_proof
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hObs : txn.RangeSecObserve.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hExec : txn.executeRange.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Range.spec (GF := GF) (hG := hG) := by
  have hEnd := mvcc.metricsTxnWrite.End.spec_frozen hEnd
  intro ctx cd nd lg kv s γ r o withTotal m log₀ ot te
  wp_start as ⟨#Hkv, Hrd, Htoks, #Hc0, #Hr, #Hctx, #Hct, Hto, #Hnd, %Hlg, %Hvst, #Hsort⟩
  ihave %Hkvok := txn.isKV_ok kv s γ $$ Hkv
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  wp_apply wp_with_defer as %defer defer
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply time.wp_Now as %now -
  wp_apply (txn.kv_Read hRead kty kvv s γ _ trace m log₀ false) $$ [$Hkv $Hrd $Htoks $Hc0 $Htrc] as %mw ⟨%log, %rev, Htx, Htoks, #Hrok, %Hpin⟩
  · ipureintro; exact Ht
  icases isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hlog⟩
  icases isTxnRead_cert mw s γ log rev $$ Htx with ⟨Htx, #Hcert⟩
  have hpin' : log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 := ⟨Hpin.1, Hpin.2⟩
  ihave %Hsok := Hsort $$ %log %hpin' Hcert
  ihave Htx : mvcc.isTxn mw s γ trace (.read log rev) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htv := (txn.txnViewIs_mw mw s γ (.read log rev)).2 $$ Htx
  wp_apply (hExec trace ctx' _ nd lg s γ _ (.read log rev) false r o withTotal)
    $$ [$Htv $Hctx' $Hct' $Hr] as %resp %err ⟨Htv, #Hres, Hhdr, %Hnd'⟩
  · isplitl [Hnd]
    · cases nd
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte, mvcc.neverDone] at *; iexact Hnd
    ipureintro
    exact ⟨Hvst, txn.sortSmall_of_sortOk o log Hlog.1 _ Hsok⟩
  ihave Htx' := (txn.txnViewIs_mw mw s γ (.read log rev)).1 $$ Htv
  simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ $$ Htx'
  ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd trace mw s γ (.read log rev)) $$ [$Htx' $Hep] as ⟨Hrd, -, %te', Htrc⟩
  cases err <;> wp_auto
  all_goals
    wp_apply time.wp_Since as %d -
    wp_apply hObs
    iapply HΦ
    iframe Hrd Htoks
    isplitr
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists te'; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists log, rev
    iframe Hcert Hrok Hres Hhdr
    ipureintro
    exact ⟨⟨Hpin.1, Hpin.2, Hlog.2.1, Hlog.2.2⟩, Hnd'⟩

end proof

end EtcdGrove
end Perennial
