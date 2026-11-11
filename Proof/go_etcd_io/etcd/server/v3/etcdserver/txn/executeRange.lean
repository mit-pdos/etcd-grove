/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): over mvcc's API (`Txn.Range` at the transaction's dynamic type, whose post
gives the read log's facts, gap A's fix, and every readable state `stateOk`, the sort's premise).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.rangeLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.filterRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.sortRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.asembleRangeResponse
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

theorem txn.executeRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hLimit : txn.rangeLimit.spec (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hFilter : txn.filterRangeResults.spec (GF := GF) (hG := hG))
    (hSort : txn.sortRangeResults.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hAsm : txn.asembleRangeResponse.spec (GF := GF) (hG := hG))
    : txn.executeRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg tw γ trace te kt r o withTotal
  generalize hlog : kt.readLog = log
  generalize hrev : kt.readRev = rev
  generalize hcrev : kt.state.crev = crev
  wp_start as ⟨Htx, Htrc, #Hctx, #Hnd, #Hct, #Hr, %Hpre⟩
  icases txn.mvccTxn_shape hsh tw γ trace kt $$ Htx with ⟨%Hsh, Htx⟩
  obtain ⟨tyX, vX, rfl, -, -, hRangeC, -⟩ := Hsh
  ihave #Hr2 := Hr
  iunfold txn.rangeRequestIs at Hr2
  icases Hr2 with ⟨%Hnn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho, -⟩
  wp_auto
  wp_apply (hGet ctx (some trace)) $$ [$Hct] as %t ⟨%Ht, %Hteq⟩
  subst Hteq
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
  icases mvcc.txnCtx_rangeCtx nd ctx cd $$ Hctx Hnd with ⟨%td, %Htd, #Hctx'⟩
  wp_apply (hRangeC γ _ te kt ctx cd td ksl esl' k e' _) $$ [$Htx $Htrc $Hctx' $Hks $Hes']
    as %rr %err ⟨%Hrn, Htx, Htrc, Hout, %HstOk, %Hlwf⟩
  have hkok := txn.kindOk_of kt Hpre.1 Hlwf.1 Hlwf.2
  rw [txn.KindOk, hlog, hrev] at hkok
  rw [hlog, hcrev] at HstOk
  rw [hlog, hrev, hcrev]
  obtain ⟨hok, h0rev, hrevlt⟩ := hkok
  have hrevo : o.base.rev = rev0 := by subst Ho; rfl
  have hco : o.base.countOnly = co := by subst Ho; rfl
  have hfast : fastKeysOnly o = (ko && !decide (target = W32 4)) := by
    subst Ho
    simp only [fastKeysOnly, rangeOpOf, ne_eq, sext32_eq target 4 (by omega) (by omega)]
    cases ko <;> simp
  iunfold mvcc.rangeOutcomeC at Hout
  icases Hout with (⟨%Hcmp, ⟨%ec, #Hec, %Herr⟩, Hrr⟩ | ⟨%Hcle, Hout⟩)
  · -- (M2, S1) below the transaction's compaction revision: `ErrCompacted`
    simp only at Hcmp
    subst Herr
    wp_auto
    iapply HΦ
    iframe Htx Htrc
    isplitl []
    · iunfold txn.rangeResult
      iright; iright; iright
      iframe Hec
      ipureintro
      exact ⟨⟨by rw [hrevo]; exact Hcmp.1, by rw [hrevo]; exact Hcmp.2, rfl⟩, rfl⟩
    isplitl []
    · iunfold txn.rangeHdr; iintro %h; cases h
    · ipureintro; intro _; exact Or.inr (Or.inr (by rw [hrevo]; exact Hcmp.2))
  iunfold mvcc.rangeOutcome at Hout
  icases Hout with (⟨%Hfut, ⟨%ef, #Hef, %Herr⟩, Hrr⟩ | ⟨%Hle, %Hflags, %Hrrnull, #Herrf⟩ | ⟨%Hle, %Herr, Hres⟩)
  · simp only at Hfut
    subst Herr
    wp_auto
    iapply HΦ
    iframe Htx Htrc
    isplitl []
    · iunfold txn.rangeResult
      ileft
      iframe Hef
      ipureintro
      exact ⟨⟨by rw [hrevo]; exact Hfut, rfl⟩, rfl⟩
    isplitl []
    · iunfold txn.rangeHdr; iintro %h; cases h
    · ipureintro; intro _; exact Or.inr (Or.inl (by rw [hrevo]; exact Hfut))
  · simp only at Hle Hflags
    subst Hrrnull
    ihave %Herr := mvcc.rangeKeysErr_ne_nil err $$ Herrf
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Htx Htrc
      isplitl []
      · iunfold txn.rangeResult
        iright; ileft
        iframe Herrf
        ipureintro
        exact ⟨by rw [hrevo]; exact Hle, by rw [hco]; exact Hflags.1, by rw [hfast]; exact Hflags.2,
          rfl, by rw [hrevo]; exact Hcle Hle⟩
      isplitl []
      · iunfold txn.rangeHdr; iintro %h; cases h
      · ipureintro; intro hnd; exact absurd rfl (Hrn (Htd hnd))
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
    have hsmall : txn.sortSmall o st := by
      apply txn.srvPre_stateOk
      rw [← hst]
      have hcl := Hcle Hle
      have hle' : sint.Z (mvcc.rangeRev rev rev0) ≤ sint.Z rev := by
        unfold mvcc.rangeRev; split
        · omega
        · exact Hle
      have hn : ((sint.nat (mvcc.rangeRev rev rev0) : Nat) : Int) = sint.Z (mvcc.rangeRev rev rev0) := by
        unfold sint.nat; exact Int.toNat_of_nonneg h0
      apply HstOk
      · rw [hn]; exact hcl
      · omega
    wp_apply (hSort rr r lg o rev cnt (srvPre o st)) $$ [$Hrr $Hr] as ⟨%vs', Hrr, %Hsorted⟩
    · ipureintro; exact ⟨Hpre.2, hsmall⟩
    wp_apply (hStep t te _ slice.nil) $$ [Htrc] as Htrc
    · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
    wp_apply (hAsm rr r o rev cnt vs') $$ [$Hrr $Hr] as %resp ⟨#Hresp, Hhdr⟩
    wp_apply (hStep t te _ slice.nil) $$ [Htrc] as Htrc
    · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
    iapply HΦ
    iframe Htx Htrc
    isplitr [Hhdr]
    · iunfold txn.rangeResult
      iright; iright; ileft
      isplitr
      · ipureintro; exact ⟨by rw [hrevo]; exact Hle, rfl, by rw [hrevo]; exact Hcle Hle⟩
      iexists _, _
      rw [hrevo, hst, ← hcnt]
      iframe Hresp
      ipureintro
      exact ⟨vs', Hsorted, rfl, rfl⟩
    isplitl [Hhdr]
    · iunfold txn.rangeHdr
      iintro -
      iexact Hhdr
    · ipureintro; intro _; exact Or.inl rfl


end proof

end EtcdGrove
end Perennial
