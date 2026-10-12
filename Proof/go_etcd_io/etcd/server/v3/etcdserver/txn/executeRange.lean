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

theorem txn.executeRange.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hLimit : txn.rangeLimit.spec (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hFilter : txn.filterRangeResults.spec (GF := GF) (hG := hG))
    (hSort : txn.sortRangeResults.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hAsm : txn.asembleRangeResponse.spec (GF := GF) (hG := hG)) :
    txn.executeRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg mw s γ log rev r o withTotal
  wp_start as ⟨Htx, #Hctx, #Hr, %Hpre⟩
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
  wp_apply (hGte esl e) $$ [$Hes] as %esl' %e' ⟨#Hes', %Hend⟩
  wp_apply (hRange mw s γ log rev ctx cd ksl esl' k e' _) $$ [$Htx $Hctx $Hks $Hes'] as %rr %err ⟨Htx, Hout⟩
  icases isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hlog⟩
  obtain ⟨hok, hne, hrev⟩ := Hlog
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
    iunfold txn.rangeResult
    ileft
    iframe Hef
    ipureintro
    exact ⟨⟨by rw [hrevo]; exact Hfut, rfl⟩, rfl⟩
  · simp only at Hle Hflags
    subst Hrrnull
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Htx
      iunfold txn.rangeResult
      iright; ileft
      ipureintro
      exact ⟨by rw [hrevo]; exact Hle, by rw [hco]; exact Hflags.1, by rw [hfast]; exact Hflags.2,
        rfl, Herr⟩
  · simp only at Hle
    subst Herr
    wp_auto
    simp only
    -- the revision read and its state
    have hlen : log.length ≤ 2 ^ 63 := by have := hok.len; omega
    have hrevz : sint.Z rev = (log.length : Int) - 1 := by
      rw [hrev]; exact lastRev_sint _ (List.length_pos_iff.2 hne) hlen
    have h0 : 0 ≤ sint.Z (mvcc.rangeRev rev rev0) := by
      unfold mvcc.rangeRev; split
      · rw [hrevz]; have := List.length_pos_iff.2 hne; omega
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
      · simp only [hcoB, Bool.false_eq_true, ↓reduceIte]
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
      · simp only [hcoB, ↓reduceIte]
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
      have hl := Hpre.2 hs
      rw [← hst]
      exact srvPre_small o _ (stateAt_small log hok.len hl _)
    wp_apply (hSort rr r lg o rev cnt (srvPre o st)) $$ [$Hrr $Hr] as ⟨%vs', Hrr, %Hsorted⟩
    · ipureintro; exact ⟨Hpre.1, hsmall⟩
    wp_apply (hStep t)
    wp_apply (hAsm rr r o rev cnt vs') $$ [$Hrr $Hr] as %resp #Hresp
    wp_apply (hStep t)
    iapply HΦ
    iframe Htx
    iunfold txn.rangeResult
    iright; iright
    isplitr
    · ipureintro; exact ⟨by rw [hrevo]; exact Hle, rfl⟩
    iexists _, _
    rw [hrevo, hst, ← hcnt]
    iframe Hresp
    ipureintro
    exact ⟨vs', Hsorted, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
