/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.rangeLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.filterRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.sortRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.asembleRangeResponse
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `executeRange` on a transaction `tw = interface.mkOk tyX vX` whose `Range` is given by `HR`
(its owned part `V`, reading `kind`'s log and revision). -/
theorem txn.executeRange_core
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hLimit : txn.rangeLimit.spec (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hFilter : txn.filterRangeResults.spec (GF := GF) (hG := hG))
    (hSort : txn.sortRangeResults.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hAsm : txn.asembleRangeResponse.spec (GF := GF) (hG := hG))
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (tyX : go.GoType) (vX : val) (V : IProp GF) (kind : mvcc.TxnKind) (hkind : txn.KindOk kind)
    (hR : ∀ (key endk : GoSlice) (k e : GoString)
      (ro' : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ V ∗
          mvcc.rangeCtx nd ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
        (App (App (App (App (Val #(methods tyX go!"Range" vX)) (Val #(GoInterface.ok ctx)))
          (Val #key)) (Val #endk)) (Val #ro'))
      {{ (rr : Loc) (err : GoInterface), RET (PairV #rr #err); ⌜nd = true → rr ≠ null⌝ ∗ V ∗
          mvcc.rangeOutcome rr err kind.readLog kind.readRev (decide (endk = slice.nil)) k e ro' }})
    (r : Loc) (o : OpFull) (withTotal : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ V ∗
        context.isContext ctx cd ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
        txn.rangeRequestIs r o ∗
        ⌜txn.validSortTarget o ∧ txn.sortSmall o (mvcc.stateAt kind.readLog
          (sint.nat (mvcc.rangeRev kind.readRev o.base.rev)))⌝ }}
      (App (App (App (App (App (Val (@! txn.executeRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
        (Val #(interface.mkOk tyX vX))) (Val #r)) (Val #withTotal))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        V ∗ txn.rangeResult resp err kind.readLog kind.readRev o withTotal ∗
        ⌜nd = true → err = GoInterface.nil ∨ sint.Z kind.readRev < sint.Z o.base.rev⌝ }} := by
  obtain ⟨hok, h0rev, hrevlt⟩ := hkind
  generalize hlog : kind.readLog = log at *
  generalize hrev : kind.readRev = rev at *
  wp_start as ⟨Htx, #Hctx, #Hnd, #Hr, %Hpre⟩
  ihave #Hr2 := Hr
  iunfold txn.rangeRequestIs at Hr2
  icases Hr2 with ⟨%Hnn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  wp_auto
  wp_apply (hGet ctx cd) $$ [$Hctx] as %t %Ht
  wp_apply (hLimit r o) $$ [$Hr]
  wp_join (Q := fun v => iprop(⌜v = #(ko && !decide (target = W32 4))⌝ ∗ r_ptr ↦ r))
    at (if: _ then _ else #false) with [r] as ⟨%Hv, r⟩
  · wp_if_destruct <;> first | (iframe; done) | (iframe; itrivial) | skip
  subst Hv
  wp_auto
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  have hnil : esl = slice.nil → e = [] := by
    intro h; subst h
    have := Hesl.1; simp [slice.nil] at this; exact List.length_eq_zero_iff.1 this
  wp_apply (hGte esl e) $$ [$Hes] as %esl' ⟨#Hes', %Hgte⟩
  have Hend := (srvEnd_mkGte esl esl' e hnil Hgte).symm
  generalize (if e = [W8 0] then [] else e) = e' at Hend ⊢
  -- the transaction's `Range`, at the request's context
  ihave #Hctx' : mvcc.rangeCtx nd ctx cd $$ []
  · cases nd
    · simp only [mvcc.rangeCtx, Bool.false_eq_true, ↓reduceIte]; iexact Hctx
    · simp only [mvcc.rangeCtx, ↓reduceIte]; iright; iframe Hctx Hnd
  wp_apply (hR ksl esl' k e' _) $$ [$Htx $Hctx' $Hks $Hes'] as %rr %err ⟨%Hrn, Htx, Hout⟩
  have hrevo : o.base.rev = rev0 := by subst Ho; rfl
  have hco : o.base.countOnly = co := by subst Ho; rfl
  have hfast : fastKeysOnly o = (ko && !decide (target = W32 4)) := by
    subst Ho
    simp only [fastKeysOnly, rangeOpOf, ne_eq, sext32_eq target 4 (by omega) (by omega)]
    cases ko <;> simp
  iunfold mvcc.rangeOutcome at Hout
  icases Hout with (⟨%Hfut, ⟨%ef, #Hef, %Herr⟩, Hrr⟩ | ⟨%Hle, %Hflags, %Hrrnull, %Herr⟩ | ⟨%Hle, %Herr, Hres⟩)
  · simp only at Hfut
    subst Herr
    wp_auto
    iapply HΦ
    iframe Htx
    isplitl
    · iunfold txn.rangeResult
      ileft
      iframe Hef
      ipureintro
      exact ⟨⟨by rw [hrevo]; exact Hfut, rfl⟩, rfl⟩
    · ipureintro; intro _; exact Or.inr (by rw [hrevo]; exact Hfut)
  · simp only at Hle Hflags
    subst Hrrnull
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Htx
      isplitl
      · iunfold txn.rangeResult
        iright; ileft
        ipureintro
        exact ⟨by rw [hrevo]; exact Hle, by rw [hco]; exact Hflags.1, by rw [hfast]; exact Hflags.2,
          rfl, Herr⟩
      · ipureintro; intro hnd; exact absurd rfl (Hrn hnd)
  · simp only at Hle
    subst Herr
    wp_auto
    simp only
    -- the revision read and its state
    have h0 : 0 ≤ sint.Z (mvcc.rangeRev rev rev0) := by
      unfold mvcc.rangeRev; split
      · exact h0rev
      · omega
    have hre : o.base.rangeEnd = rangeEndOf esl e := by subst Ho; rfl
    have hk : o.key = k := by subst Ho; rfl
    have hsel : ∀ st : List EtcdKv, srvSel st (decide (esl' = slice.nil)) k e' = rangeIn st o := by
      intro st
      have := srvSel_srvEnd st o
      rw [hre, hk, Hend] at this
      exact this
    generalize hst : mvcc.stateAt log (sint.nat (mvcc.rangeRev rev rev0)) = st
    ihave Hrr : (|==> ∃ (cnt : w64) (vs0 : List EtcdKv), txn.rangeResultIs rr rev cnt vs0 ∗
        ⌜vs0.filter (kvFilterOk o) = srvPre o st ∧ cnt = srvCount o st withTotal⌝) $$ [Hres]
    · cases hcoB : co <;> rw [hcoB] at hco
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hres with ⟨%kvs, Hrr, Hkvs⟩
        iunfold mvcc.rangeKvs at Hkvs
        icases Hkvs with ⟨%ps, Hsl, %Hplen, Hbig⟩
        have hF := taken_stateAt log hok (decide (esl' = slice.nil)) k e' (mvcc.rangeRev rev rev0)
          (rangeLimitOf o) h0
        rw [hst, hsel st] at hF
        have hFlen := forall2_length hF
        imod rangeKvs_kvsAt (GF := GF) (!(ko && !decide (target = W32 4))) st ps _ _
          (hF.imp (fun h => h.1)) Hplen $$ Hbig with Hkv
        simp only [Bool.not_not, ← hfast]
        imodintro
        iexists _, ((mvcc.takeLimit (mvcc.limitOf (rangeLimitOf o)) (rangeIn st o)).map (kvRead (fastKeysOnly o)))
        isplitl
        · iunfold txn.rangeResultIs
          iexists kvs, ps.zip ((mvcc.takeLimit (mvcc.limitOf (rangeLimitOf o)) (rangeIn st o)).map
            (kvRead (fastKeysOnly o)))
          iframe Hrr
          isplitr
          · ipureintro
            exact zip_map_snd _ _ (by simp; omega)
          iunfold txn.kvsOwnAt
          rw [zip_map_fst _ _ (by simp; omega)]
          iframe
        · ipureintro
          refine ⟨?_, ?_⟩
          · unfold srvPre; simp [hco]
          · unfold srvCount
            rw [hco]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [total_stateAt log hok _ k e' _ _ _ h0, hst, hsel st]
      · simp only [↓reduceIte]
        imodintro
        iexists _, []
        isplitl
        · iunfold txn.rangeResultIs
          iexists slice.nil, []
          iframe Hres
          isplitr
          · ipureintro; rfl
          iunfold txn.kvsOwnAt
          simp only [List.map_nil]
          isplitl
          · iapply ownSlice_nil
          · iapply kvsAt_nil
        · ipureintro
          refine ⟨?_, ?_⟩
          · unfold srvPre; simp [hco]
          · unfold srvCount
            rw [hco]
            simp only [↓reduceIte]
            rw [answers_length_stateAt log hok _ k e' _ h0, hst, hsel st]
    imod Hrr with ⟨%cnt, %vs0, Hrr, %Hvs0⟩
    obtain ⟨hpre, hcnt⟩ := Hvs0
    wp_apply (hFilter rr r o rev cnt vs0) $$ [$Hrr $Hr] as Hrr
    rw [hpre]
    have hsmall : (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) →
        (srvPre o st).length ≤ 2 ^ 62 ∧ ∀ v ∈ srvPre o st, kvOk v := by
      intro hs
      have h2 := Hpre.2
      rw [hrevo, hst] at h2
      exact h2 hs
    wp_apply (hSort rr r lg o rev cnt (srvPre o st)) $$ [$Hrr $Hr] as ⟨%vs', Hrr, %Hsorted⟩
    · ipureintro; exact ⟨Hpre.1, hsmall⟩
    wp_apply (hStep t)
    · ipureintro; exact Ht
    wp_apply (hAsm rr r o rev cnt vs') $$ [$Hrr $Hr] as %resp #Hresp
    wp_apply (hStep t)
    · ipureintro; exact Ht
    iapply HΦ
    iframe Htx
    isplitl
    · iunfold txn.rangeResult
      iright; iright
      isplitr
      · ipureintro; exact ⟨by rw [hrevo]; exact Hle, rfl⟩
      iexists _, _
      rw [hrevo, hst, ← hcnt]
      iframe Hresp
      ipureintro
      exact ⟨vs', Hsorted, rfl, rfl⟩
    · ipureintro; intro _; exact Or.inl rfl

theorem txn.executeRange.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hLimit : txn.rangeLimit.spec (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hRoRange : mvcc.txnReadWrite.Range.spec (GF := GF) (hG := hG))
    (hFilter : txn.filterRangeResults.spec (GF := GF) (hG := hG))
    (hSort : txn.sortRangeResults.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hAsm : txn.asembleRangeResponse.spec (GF := GF) (hG := hG)) :
    txn.executeRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg s γ tw kind ro r o withTotal
  wp_start_folded as ⟨Htv, #Hctx, #Hnd, #Hr, %Hpre⟩
  cases ro
  · -- a transaction behind a `*metricsTxnWrite`
    iunfold txn.txnViewIs at Htv
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Htv with ⟨%mw, %Htw, Htx⟩
    subst Htw
    icases txn.isTxn_kindOk mw s γ kind $$ Htx with ⟨%Hk, Htx⟩
    iapply (txn.executeRange_core hGet hLimit hGte hFilter hSort hStep hAsm ctx cd nd lg _ _
      (mvcc.isTxn mw s γ kind) kind Hk (hRange mw s γ kind ctx cd nd) r o withTotal) $$ [Htx]
    · iframe Htx Hctx Hnd Hr Hpkg
      ipureintro; exact Hpre
    inext
    iintro %resp %err ⟨Htx, #Hres, %Hnd'⟩
    iapply HΦ
    iframe Hres
    isplitl
    · iapply (txn.txnViewIs_mw mw s γ kind).2 $$ Htx
    · ipureintro; exact Hnd'
  · -- the read-only wrapper
    iunfold txn.txnViewIs at Htv
    simp only [↓reduceIte]
    icases Htv with ⟨%trw, %log, %rev, %Htw, Hro⟩
    obtain ⟨Htw, Hkind⟩ := Htw
    subst Htw Hkind
    icases txn.isRoTxnWrite_pure trw s γ log rev $$ Hro with ⟨Hro, %Hp⟩
    iapply (txn.executeRange_core hGet hLimit hGte hFilter hSort hStep hAsm ctx cd nd lg _ _
      (mvcc.isRoTxnWrite trw s γ log rev) (.read log rev) (txn.kindOk_read log rev Hp)
      (hRoRange trw s γ log rev ctx cd nd) r o withTotal) $$ [Hro]
    · iframe Hro Hctx Hnd Hr Hpkg
      ipureintro; exact Hpre
    inext
    iintro %resp %err ⟨Hro, #Hres, %Hnd'⟩
    iapply HΦ
    iframe Hres
    isplitl
    · iapply (txn.txnViewIs_ro trw s γ log rev).2 $$ Hro
    · ipureintro; exact Hnd'

end proof

end EtcdGrove
end Perennial
