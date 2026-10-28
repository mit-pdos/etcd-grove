/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StepWithFunction
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

set_option linter.unusedSimpArgs false in
theorem txn.getPrevKV.wp_proof
    (hStep : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    txn.getPrevKV.spec (GF := GF) (hG := hG) := by
  have hRange := mvcc.metricsTxnWrite.Range.spec_R hRange
  intro trace mw s γ kind p o tyX vX crev
  wp_start as ⟨%Htr, Htx, #Hwrap, #Hp⟩
  iunfold txn.putRequestIs at Hp
  icases Hp with ⟨%Hpnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl,
    #Hpk, #Hiv, #Hil, -, %Ho, -⟩
  have hR : txn.readsPrev o = ((iv || il) || pk) := by subst Ho; rfl
  have hK : o.key = k := by subst Ho; rfl
  rw [hR, hK]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  cases hb : ((iv || il) || pk)
  · -- no previous key-value needed
    have hiv : iv = false := by cases iv <;> simp_all
    have hil : il = false := by cases il <;> simp_all
    have hpk : pk = false := by cases pk <;> simp_all
    subst hiv hil hpk
    wp_auto
    iapply HΦ
    iframe Htx
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; rfl
  · -- the range read of the key, in the trace's step
    simp only [↓reduceIte]
    cases iv <;> cases il <;> cases pk <;> simp only [Bool.or_false, Bool.false_or, Bool.or_true,
      Bool.true_or, Bool.false_eq_true] at hb <;> (try wp_auto)
    all_goals
      icases mvcc.isTxn_trace_acc mw s γ trace kind crev $$ Htx with ⟨⟨%te, Htrc⟩, Hback⟩
      wp_apply (hStep trace te _ _ slice.nil
          (iprop(∃ rr : Loc, prevKV_ptr ↦ rr ∗ err_ptr ↦ (GoInterface.nil : GoInterface) ∗
            p_ptr ↦ p ∗
            txnWrite_ptr ↦ (interface.mkOk tyX vX : GoInterface) ∗
            ((∃ te' : Bool, traceutil.ownTrace trace te') -∗ mvcc.isTxn mw s γ trace kind crev) ∗
            txn.prevKvIs rr (txn.kindState kind) k)))
        $$ [Htrc Hback err prevKV p txnWrite] as ⟨⟨%rr, prevKV, err, p, txnWrite, Hback, Hprev⟩, Htrc⟩
      · iframe #
        iframe Htrc
        isplitr
        · iapply traceutil.ownFields_nil
        iintro Htrc
        ihave Htx := Hback $$ [Htrc]
        · iexists te; iexact Htrc
        wp_auto
        wp_apply hTODO
        ihave #Hctx : mvcc.rangeCtx true todoCtxVal txn.todoCd $$ []
        · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
        wp_bind (App (App (App (App (Val #(methods tyX _ vX)) _) _) _) _)
        iapply mvcc.tw_wp4 tyX vX mw go!"Range" (by unfold mvcc.twMethod; simp)
        iframe Hwrap
        wp_apply (hRange trace mw s γ kind todoCtxVal txn.todoCd true ksl slice.nil k []
            (zero_val RangeOptions) crev) $$ [$Htx $Hctx $Hks $Hnil] as %r %rerr ⟨%Hrn, Htx, Hout⟩
        ihave ⟨%Hok, Htx⟩ := txn.isTxn_kindOk mw s γ kind crev $$ Htx
        -- (M2, S1) a read at the transaction's revision is never compacted
        ihave ⟨%Hcr, Htx⟩ := txn.isTxn_crev mw s γ kind crev $$ Htx
        ihave Hout := mvcc.rangeOutcomeC_latest _ _ _ _ _ _ _ _ (zero_val RangeOptions)
          (by rw [show (zero_val RangeOptions).Rev' = W64 0 from rfl]; decide) Hcr $$ Hout
        clear Hcr
        icases txn.prevKvIs_of_outcome r rerr kind k [] (zero_val RangeOptions) Hok
          ⟨rfl, rfl, rfl, rfl⟩ (Hrn rfl) $$ Hout with ⟨%Herr, Hprev⟩
        subst Herr
        (try wp_auto)
        icases mvcc.isTxn_trace_acc mw s γ trace kind crev $$ Htx with ⟨Htrc, Hback⟩
        isplitl []
        · ipureintro; rfl
        iframe Htrc
        iexists r
        iframe
      ihave Htx := Hback $$ Htrc
      (try wp_auto)
      iapply HΦ
      iframe Htx Hprev

end proof

end EtcdGrove
end Perennial
