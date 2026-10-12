/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__FirstRev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn go_etcd_io.etcd.server.v3.storage.mvcc
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkRange.wp_proof
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hFirst : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG)) :
    txn.checkRange.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev req o
  wp_start as ⟨Htx, #Hr⟩
  ihave #Hmp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hmp
  icases Hinit with ⟨-, ⟨%ec, #Hcomp⟩, ⟨%ef, #Hfut⟩, -⟩
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨%Hnn, %ksl, %esl, %k, %e, %rv, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  have hrv : o.base.rev = rv := by subst Ho; rfl
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Htx
    iunfold txn.checkRangeErr
    ileft; ipureintro
    exact ⟨rfl, Or.inl (by simp_all)⟩
  · skip
    have hne : ¬ rv = W64 0 := by simpa using Hif
    ihave Htx : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    wp_apply +noauto (hRev mw s γ (.read log rev)) $$ [$Htx] as Htx
    rw [show (mvcc.TxnKind.read log rev).beginRev = rev from rfl]
    ihave Htx : mvcc.isTxnRead mw s γ log rev $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    wp_auto
    wp_if_destruct
    · skip
      have hlt : sint.Z rev < sint.Z rv := by simpa using Hif
      iapply HΦ
      iframe Htx
      iunfold txn.checkRangeErr
      iright; ileft
      isplitr
      · ipureintro; rw [hrv]; exact ⟨hne, hlt⟩
      iexists ef; iframe Hfut; ipureintro; rfl
    · skip
      have hle : ¬ sint.Z rev < sint.Z rv := by simpa using Hif
      have hm1 : sint.Z (W64 (-1)) = -1 := by decide
      wp_apply (hFirst mw s γ log rev) $$ [$Htx] as Htx
      wp_if_destruct
      · skip
        have hc : sint.Z rv < sint.Z (W64 (-1)) := by simpa using Hif
        iapply HΦ
        iframe Htx
        iunfold txn.checkRangeErr
        iright; iright
        isplitr
        · ipureintro; rw [hrv]
          exact ⟨hne, by omega, by omega⟩
        iexists ec; iframe Hcomp; ipureintro; rfl
      · skip
        have hge : ¬ sint.Z rv < sint.Z (W64 (-1)) := by simpa using Hif
        iapply HΦ
        iframe Htx
        iunfold txn.checkRangeErr
        ileft; ipureintro
        refine ⟨rfl, Or.inr ⟨by rw [hrv]; omega, by rw [hrv]; omega⟩⟩

end proof

end EtcdGrove
end Perennial
