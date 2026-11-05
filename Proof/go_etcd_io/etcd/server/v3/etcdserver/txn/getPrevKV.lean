/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): over mvcc's API (`Txn.Range` at the transaction's dynamic type, inside the
trace's `StepWithFunction`; gaps A and E fixed).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StepWithFunction
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.getPrevKV.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    : txn.getPrevKV.spec (GF := GF) (hG := hG) := by
  intro t γ trace te kt p o
  wp_start as ⟨%Htr, Htx, Htrc, %Hreach, #Hp⟩
  icases txn.mvccTxn_shape hsh t γ trace kt $$ Htx with ⟨%Hsh, Htx⟩
  obtain ⟨tyX, vX, rfl, -, -, hRangeC, -⟩ := Hsh
  have hkm : txn.kindState kt = txn.mstate kt := by
    have := txn.kindState_append kt [] Hreach (fun _ => rfl)
    rw [txn.MTxn.append_nil] at this
    rw [this]; rfl
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
    isplitl [Htrc]
    · iexists te; iexact Htrc
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; rfl
  · -- the range read of the key, in the trace's step
    simp only [↓reduceIte]
    cases iv <;> cases il <;> cases pk <;> simp only [Bool.or_false, Bool.false_or, Bool.or_true,
      Bool.true_or, Bool.false_eq_true] at hb <;> (try wp_auto)
    all_goals
      wp_apply (hStep trace te _ _ slice.nil
          (iprop(∃ rr : Loc, prevKV_ptr ↦ rr ∗ err_ptr ↦ (GoInterface.nil : GoInterface) ∗
            p_ptr ↦ p ∗
            txnWrite_ptr ↦ (interface.mkOk tyX vX : GoInterface) ∗
            mvcc.api.mvccTxn (interface.mkOk tyX vX) γ trace kt ∗
            txn.prevKvIs rr (txn.kindState kt) k)))
        $$ [Htrc Htx err prevKV p txnWrite] as ⟨⟨%rr, prevKV, err, p, txnWrite, Htx, Hprev⟩, Htrc⟩
      · iframe #
        iframe Htrc
        isplitr
        · iapply traceutil.ownFields_nil
        iintro Htrc
        wp_auto
        wp_apply hTODO
        ihave #Hctx : mvcc.rangeCtx true todoCtxVal txn.todoCd $$ []
        · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
        wp_apply (hRangeC γ trace te kt todoCtxVal txn.todoCd true ksl slice.nil k []
            (zero_val RangeOptions)) $$ [$Htx $Htrc $Hctx $Hks $Hnil] as %r %rerr ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
        have Hok := txn.kindOk_of kt Hreach Hlwf.1 Hlwf.2
        -- (M2, S1) a read at the transaction's revision is never compacted
        have Hcr := txn.crev_le_readRev kt Hreach
        ihave Hout := mvcc.rangeOutcomeC_latest _ _ _ _ _ _ _ _ (zero_val RangeOptions)
          (by rw [show (zero_val RangeOptions).Rev' = W64 0 from rfl]; decide) Hcr $$ Hout
        clear Hcr
        icases txn.prevKvIs_of_outcome r rerr kt k [] (zero_val RangeOptions) Hok
          ⟨rfl, rfl, rfl, rfl⟩ (Hrn rfl) $$ Hout with ⟨%Herr, Hprev⟩
        subst Herr
        (try wp_auto)
        isplitl []
        · ipureintro; rfl
        isplitr [Htrc]
        · iexists r; iframe
        iexists te; iexact Htrc
      (try wp_auto)
      iapply HΦ
      iframe Htx Htrc
      rw [← hkm]
      iexact Hprev

end proof

end EtcdGrove
end Perennial
