/-
Proof of `Spec/.../mvcc/treeIndex__Revisions.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Revisions
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeGet
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeVisit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__get
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Get
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- The visitor's invariant: after the first `i` entries in range, `revs` and `totalCount`. -/
def mvcc.revisionsInv (revs_ptr totalCount_ptr : Loc) (vis : List mvcc.IdxEntry)
    (atRev limit : w64) (withTotal : Bool) (i : Nat) : IProp GF :=
  iprop(∃ (rs : GoSlice) (total : w64),
    revs_ptr ↦ rs ∗ totalCount_ptr ↦ total ∗
    rs ↦* ((mvcc.takeLimit (mvcc.limitOf limit) (mvcc.entryAnswers (vis.take i) atRev)).map
      fun x => mvcc.revVal x.2.1) ∗
    ownSliceCap Revision rs (DFrac.own 1) ∗
    ⌜total = W64 (mvcc.totalOf (mvcc.limitOf limit) withTotal
      (mvcc.entryAnswers (vis.take i) atRev).length)⌝)

/-- `limit > 0 && len(revs) >= limit`, as Goose compiles it (the first conjunct already a value):
`reached`. -/
theorem wp_reachedLimit (limit : w64) (limit_ptr revs_ptr : Loc) (rs : GoSlice) (vs : List Revision) :
    {{ (limit_ptr ↦□ limit : IProp GF) ∗ revs_ptr ↦ rs ∗ rs ↦* vs }}
      (If (Val #(decide (sint.Z (W64 0) < sint.Z limit)))
        (App (Val (GoInstruction (GoOp GoGe go.int)))
          (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType Revision.ty)))) (Val #revs_ptr))
                  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType Revision.ty)])))
                    (Val #())) (Var "$a0")))
                (App (Val (GoInstruction (GoLoad go.int))) (Val #limit_ptr))))
        (Val #false))
    {{ (b : Bool), RET #b; ⌜b = mvcc.reached (mvcc.limitOf limit) vs.length⌝ ∗ revs_ptr ↦ rs ∗ rs ↦* vs }} := by
  wp_start as ⟨#Hl, Hrs, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe Hrs Hsl
    ipureintro
    unfold mvcc.limitOf mvcc.reached
    have h0 : (0 : Int) < sint.Z limit := by
      have h := Hif; rw [show sint.Z (W64 0) = 0 by decide] at h; exact h
    simp only [h0, ↓reduceIte]
    obtain ⟨h1, h2⟩ := Hlen
    rw [h1]
    unfold sint.nat sint.Z at *
    simp only [decide_eq_decide]
    omega
  · (try wp_auto)
    iapply HΦ
    iframe Hrs Hsl
    ipureintro
    unfold mvcc.limitOf mvcc.reached
    have h0 : ¬ (0 : Int) < sint.Z limit := by
      have h := Hif; rw [show sint.Z (W64 0) = 0 by decide] at h; exact h
    simp [h0]

/-- `reachedLimit && !withTotalCount` (`reachedLimit` already loaded). -/
theorem wp_stopCond (b wt : Bool) (wt_ptr : Loc) :
    {{ (wt_ptr ↦□ wt : IProp GF) }}
      (If (Val #b)
        (App (Val (GoInstruction (GoUnOp GoNot go.bool)))
          (App (Val (GoInstruction (GoLoad go.bool))) (Val #wt_ptr)))
        (Val #false))
    {{ RET #(b && !wt); True }} := by
  wp_start as #Hwt
  cases b
  · (try wp_auto)
    simp only [Bool.false_and]
    iapply HΦ
    itrivial
  · wp_auto
    simp only [Bool.true_and]
    iapply HΦ
    itrivial

theorem mvcc.treeIndex.Revisions.wp_proof
    (hUnsafe : mvcc.treeIndex.unsafeGet.spec (GF := GF) (hG := hG))
    (hVisit : mvcc.treeIndex.unsafeVisit.spec (GF := GF) (hG := hG))
    (hget : mvcc.keyIndex.get.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Revisions.spec (GF := GF) (hG := hG) := by
  intro ti γ log key endk k e atRev limit withTotal e0
  wp_start as ⟨#Hti, Hrd, #Hcert, %Hrev, #Hkey, #Hend, #Herr⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxReader at Hrd
  icases Hrd with ⟨%t', #Htree', Hrd⟩
  icombine Htree Htree' gives %Ht'
  subst Ht'
  iunfold mvcc.idxCert at Hcert
  icases Hcert with ⟨#Hclb, #Hcnt, %Hcwf⟩
  obtain ⟨Hwf0, Hlen0, Hcs0⟩ := Hcwf
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `ti.RLock()`: the promoted method
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RLock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog, %pend, %L, HP⟩
  iNamedSuffix HP "L"
  obtain ⟨HwfL, HlenL, HpendL, HcsL⟩ := HwfL
  (try wp_auto)
  -- the reader's view is the certified log's
  ihave %Hcmp := mono_list_lb_valid γ.hist _ _ $$ Hclb HhistL
  ihave %Hcnt' := monoNatLbOwn_valid γ.nev sync.rfrac _ _ $$ HnevL Hcnt
  obtain ⟨r, hr, hrz⟩ : ∃ r : Nat, atRev = W64 r ∧ sint.Z atRev = r :=
    ⟨(sint.Z atRev).toNat, by
      have h := Int.toNat_of_nonneg Hrev.1
      rw [show (((sint.Z atRev).toNat : Nat) : Int) = sint.Z atRev from h]
      exact BitVec.ofInt_toInt.symm, (Int.toNat_of_nonneg Hrev.1).symm⟩
  have hrlt : r < log.length := by omega
  have hne := entries_not_empty L _ HLL
  subst hr
  wp_if_destruct
  · -- `end == nil`: the one key, `ti.unsafeGet(key, atRev)`
    wp_apply (hUnsafe ti t lg L sync.rfrac key k (W64 r) e0) $$ [$HtreeL] as ⟨HtreeL, -⟩
    · iframe #
      ipureintro
      exact hne
    have hans : (mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty =
        mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k := by
      rw [HLL]; exact (mvcc.indexOf_rep _).2 k
    have hstab := mvcc.reader_answer log ilog pend Hcmp Hcnt'.2 (by omega) Hwf0 Hcs0 k r hrlt
    have hval : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) (W64 r)
        (GoInterface.ok e0) = mvcc.kiGetVal (mvcc.kiOfKey (mvcc.evsOf log) k) (W64 r) (GoInterface.ok e0) := by
      unfold mvcc.kiGetVal; rw [hans, hstab]
    rw [hval, mvcc.rangeTaken_true, mvcc.rangeTotal_true, mvcc.rangeAnswers_nil]
    unfold mvcc.kiGetVal
    cases hg : mvcc.kiGet (mvcc.kiOfKey (mvcc.evsOf log) k) (W64 r) with
    | none =>
      simp only [Option.map_none, Option.toList_none, List.map_nil, List.length_nil]
      wp_auto
      -- the deferred `ti.RUnlock()`
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
      wp_call
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL] as Hrd
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L
        simp only [named]
        iframe HnevL HtreeL
        iframe #
        ipureintro
        exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
      (try wp_auto)
      iapply HΦ
      isplitl [Hrd]
      · iunfold mvcc.idxReader
        iexists t
        iframe Hrd
        iexact Htree
      isplitl []
      · iapply (ownSlice_nil (DFrac.own 1))
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro; rfl
    | some rr =>
      obtain ⟨m, c, v⟩ := rr
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil, List.length_singleton]
      wp_auto
      wp_apply wp_slice_literal (l := [mvcc.revVal m])
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hcap⟩
      wp_auto
      -- the deferred `ti.RUnlock()`
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
      wp_call
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL] as Hrd
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L
        simp only [named]
        iframe HnevL HtreeL
        iframe #
        ipureintro
        exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
      (try wp_auto)
      iapply HΦ
      iframe Hsl Hcap
      isplitl [Hrd]
      · iunfold mvcc.idxReader
        iexists t
        iframe Hrd
        iexact Htree
      ipureintro; rfl
  · -- `end != nil`: `ti.unsafeVisit(key, end, f)`
    rw [mvcc.rangeTaken_false, mvcc.rangeTotal_false,
      mvcc.rangeAnswers_entries log ilog pend L Hcmp Hcnt'.2 (by omega) Hwf0 Hcs0 HLL k e r hrlt]
    ipersist limit
    ipersist withTotalCount
    ipersist atRev
    ipersist ti
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply (hVisit ti t L sync.rfrac key endk k e _
      (mvcc.revisionsInv revs_ptr totalCount_ptr (mvcc.rangeEntries L k e) (W64 r) limit withTotal)
      (mvcc.revisionsInv revs_ptr totalCount_ptr (mvcc.rangeEntries L k e) (W64 r) limit withTotal
        (mvcc.rangeEntries L k e).length)) $$ [$HtreeL revs totalCount] as ⟨HtreeL, Hdone⟩
    · iframe #
      isplitl [revs totalCount]
      · -- the invariant at the start
        iunfold mvcc.revisionsInv
        iexists slice.nil, zero_val w64
        iframe revs totalCount
        simp only [List.take_zero, mvcc.entryAnswers_nil, mvcc.takeLimit_nil, List.map_nil,
          List.length_nil, mvcc.totalOf_zero]
        isplitl []
        · iapply (ownSlice_nil (DFrac.own 1))
        isplitl []
        · iapply ownSliceCap_nil
        ipureintro; rfl
      · -- the visitor
        iunfold mvcc.visitSpec
        iintro %i %z %Hz
        wp_start_folded as ⟨HP, Hz, #Hzi⟩
        iunfold mvcc.revisionsInv at HP
        icases HP with ⟨%rs, %total, Hrs, Htot, Hsl, Hcap, %Htot⟩
        ihave %Hslen := ownSlice_len _ _ _ $$ Hsl
        iunfold mvcc.ownEntry at Hz
        icases Hz with ⟨%Hnn, %gs, Hki⟩
        have hzL : z ∈ L := by
          have h := List.mem_of_getElem? Hz
          unfold mvcc.rangeEntries at h
          exact (List.mem_filter.1 h).1
        wp_auto
        wp_apply (wp_reachedLimit limit limit_ptr revs_ptr rs _) $$ [$limit $Hrs $Hsl] as %b ⟨%hb, Hrs, Hsl⟩
        rw [List.length_map, mvcc.reached_takeLimit] at hb
        subst hb
        (try wp_auto)
        wp_apply (wp_stopCond _ withTotal withTotalCount_ptr) $$ [$withTotalCount]
        cases hstop : (mvcc.reached (mvcc.limitOf limit)
            (mvcc.entryAnswers ((mvcc.rangeEntries L k e).take i) (W64 r)).length && !withTotal) with
        | true =>
          -- the limit reached, not counting: stop with the answers so far
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hstop
          obtain ⟨hre, hwt⟩ := hstop
          subst hwt
          wp_auto
          iapply HΦ
          isplitl [Hki]
          · iunfold mvcc.ownEntry
            isplitl []
            · ipureintro; exact Hnn
            iexists gs; iexact Hki
          simp only [Bool.false_eq_true, ↓reduceIte]
          iunfold mvcc.revisionsInv
          iexists rs, total
          rw [List.take_length,
            mvcc.takeLimit_of_prefix _ (mvcc.entryAnswers_prefix (mvcc.rangeEntries L k e) (W64 r) i) hre,
            mvcc.totalOf_reached _ _ _ (mvcc.entryAnswers_prefix (mvcc.rangeEntries L k e) (W64 r) i).length_le hre]
          iframe Hrs Htot Hsl Hcap
          ipureintro; exact Htot
        | false =>
          -- `ki.get(ti.lg, atRev)`
          have hcont : withTotal = true ∨ mvcc.reached (mvcc.limitOf limit)
              (mvcc.entryAnswers ((mvcc.rangeEntries L k e).take i) (W64 r)).length = false := by
            rcases Bool.and_eq_false_iff.1 hstop with h | h
            · exact Or.inr h
            · exact Or.inl (by simpa using h)
          wp_auto
          wp_apply (hget z.1 gs z.2.2 (DFrac.own sync.rfrac) lg (W64 r) e0) $$ [$Hki $Herr] as Hki
          · ipureintro; exact hne z hzL
          unfold mvcc.kiGetVal
          cases hg : mvcc.kiGet z.2.2 (W64 r) with
          | none =>
            wp_auto
            iapply HΦ
            isplitl [Hki]
            · iunfold mvcc.ownEntry
              isplitl []
              · ipureintro; exact Hnn
              iexists gs; iexact Hki
            simp only [↓reduceIte]
            iunfold mvcc.revisionsInv
            iexists rs, total
            rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
            simp only [Option.map_none, Option.toList_none, List.append_nil]
            iframe Hrs Htot Hsl Hcap
            ipureintro; exact Htot
          | some rr =>
            obtain ⟨m, c, v⟩ := rr
            wp_auto
            cases hre : mvcc.reached (mvcc.limitOf limit)
                (mvcc.entryAnswers ((mvcc.rangeEntries L k e).take i) (W64 r)).length with
            | false =>
              -- `!reachedLimit`: `revs = append(revs, rev)`
              (try wp_auto)
              wp_apply wp_slice_literal (l := [mvcc.revVal m])
              isplitr
              · ipureintro; rfl
              iintro %sl2 ⟨Hsl2, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %rs' ⟨Hsl, Hcap, -⟩
              (try wp_auto)
              iapply HΦ
              isplitl [Hki]
              · iunfold mvcc.ownEntry
                isplitl []
                · ipureintro; exact Hnn
                iexists gs; iexact Hki
              simp only [↓reduceIte]
              iunfold mvcc.revisionsInv
              iexists rs', (total + W64 1)
              rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
              simp only [Option.map_some, Option.toList_some]
              rw [mvcc.takeLimit_append_not _ _ _ hre, List.map_append, List.length_append,
                List.length_singleton, mvcc.totalOf_succ _ _ _ (Or.inr hre)]
              simp only [List.map_cons, List.map_nil]
              iframe Hrs Htot Hsl Hcap
              ipureintro
              subst Htot
              word
            | true =>
              -- the limit reached (counting): only `totalCount++`
              have hwt : withTotal = true := by
                rcases hcont with h | h
                · exact h
                · rw [h] at hre; exact absurd hre Bool.false_ne_true
              (try wp_auto)
              iapply HΦ
              isplitl [Hki]
              · iunfold mvcc.ownEntry
                isplitl []
                · ipureintro; exact Hnn
                iexists gs; iexact Hki
              simp only [↓reduceIte]
              iunfold mvcc.revisionsInv
              iexists rs, (total + W64 1)
              rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
              simp only [Option.map_some, Option.toList_some]
              rw [mvcc.takeLimit_append_reached _ _ _ hre, List.length_append,
                List.length_singleton, mvcc.totalOf_succ _ _ _ (Or.inl hwt)]
              iframe Hrs Htot Hsl Hcap
              ipureintro
              subst Htot
              word
    -- after the visit: the answers of all the entries in range
    ihave HQ : mvcc.revisionsInv (GF := GF) revs_ptr totalCount_ptr (mvcc.rangeEntries L k e) (W64 r) limit
        withTotal (mvcc.rangeEntries L k e).length $$ [Hdone]
    · icases Hdone with (H | H) <;> iexact H
    iunfold mvcc.revisionsInv at HQ
    icases HQ with ⟨%rs, %total, Hrs, Htot, Hsl, Hcap, %Htot⟩
    wp_auto
    -- the deferred `ti.RUnlock()`
    rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
    wp_call
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL] as Hrd
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend, L
      simp only [named]
      iframe HnevL HtreeL
      iframe #
      ipureintro
      exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
    (try wp_auto)
    iapply HΦ
    rw [List.take_length]
    iframe Hsl Hcap
    isplitl [Hrd]
    · iunfold mvcc.idxReader
      iexists t
      iframe Hrd
      iexact Htree
    ipureintro
    rw [List.take_length] at Htot
    exact Htot

end proof

end EtcdGrove
end Perennial
