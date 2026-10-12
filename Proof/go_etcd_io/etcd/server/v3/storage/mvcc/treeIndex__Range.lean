/-
Proof of `Spec/.../mvcc/treeIndex__Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeGet
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeVisit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__get
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReadLemmas
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- The visitor's invariant: after the first `i` entries in range, the four slices and
`totalCount`. -/
def mvcc.rangeInv (keys_ptr modifies_ptr creates_ptr versions_ptr totalCount_ptr : Loc)
    (vis : List mvcc.IdxEntry) (atRev limit : w64) (withTotal : Bool) (i : Nat) : IProp GF :=
  iprop(∃ (keys modifies creates versions : GoSlice) (total : w64),
    keys_ptr ↦ keys ∗ modifies_ptr ↦ modifies ∗ creates_ptr ↦ creates ∗ versions_ptr ↦ versions ∗
    totalCount_ptr ↦ total ∗
    mvcc.ownKeys keys ((mvcc.takeLimit (mvcc.limitOf limit) (mvcc.entryAnswers (vis.take i) atRev)).map
      Prod.fst) ∗
    modifies ↦* ((mvcc.takeLimit (mvcc.limitOf limit) (mvcc.entryAnswers (vis.take i) atRev)).map
      fun x => mvcc.revVal x.2.1) ∗
    ownSliceCap Revision modifies (DFrac.own 1) ∗
    creates ↦* ((mvcc.takeLimit (mvcc.limitOf limit) (mvcc.entryAnswers (vis.take i) atRev)).map
      fun x => mvcc.revVal x.2.2.1) ∗
    ownSliceCap Revision creates (DFrac.own 1) ∗
    versions ↦* ((mvcc.takeLimit (mvcc.limitOf limit) (mvcc.entryAnswers (vis.take i) atRev)).map
      fun x => x.2.2.2) ∗
    ownSliceCap w64 versions (DFrac.own 1) ∗
    ⌜total = W64 (mvcc.totalOf (mvcc.limitOf limit) withTotal
      (mvcc.entryAnswers (vis.take i) atRev).length)⌝)

/-- `ownKeys` of one more key. -/
theorem mvcc.ownKeys_snoc (keys' : GoSlice) (kss : List GoSlice) (ks : List GoString)
    (hlen : kss.length = ks.length) (s : GoSlice) (k : GoString) :
    ⊢ ([∗list] p ∈ kss.zip ks, p.1 ↦*□ p.2 : IProp GF) -∗ keys' ↦* (kss ++ [s]) -∗
      ownSliceCap GoSlice keys' (DFrac.own 1) -∗ s ↦*□ k -∗ mvcc.ownKeys keys' (ks ++ [k]) := by
  iintro Hzip Hk' Hcap #Hs
  iunfold mvcc.ownKeys
  iexists (kss ++ [s])
  iframe Hk' Hcap
  isplitl []
  · ipureintro; simp [hlen]
  rw [List.zip_append hlen, show [s].zip [k] = [(s, k)] from rfl]
  iapply BigSepL.bigSepL_append.2
  iframe Hzip
  iapply BigSepL.bigSepL_singleton.2
  iexact Hs

theorem mvcc.treeIndex.Range.wp_proof
    (hUnsafe : mvcc.treeIndex.unsafeGet.spec (GF := GF) (hG := hG))
    (hVisit : mvcc.treeIndex.unsafeVisit.spec (GF := GF) (hG := hG))
    (hget : mvcc.keyIndex.get.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Range.spec (GF := GF) (hG := hG) := by
  intro ti γ kn key endk k e atRev limit withTotal e0
  generalize hlog : kn.log = log at *
  wp_start as ⟨#Hti, Hrd, Hkn, %Hrev, #Hkey, #Hend, #Herr⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxReader at Hrd
  icases Hrd with ⟨%t', #Htree', Hrd⟩
  icombine Htree Htree' gives %Ht'
  subst Ht'
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
  icases mvcc.idxKnows_facts γ kn log hlog ilog pend sync.rfrac $$ Hkn HhistL HnevL with ⟨%Hfacts, Hkn, HnevL⟩
  obtain ⟨Hcmp, Hcnt', Hwf0, Hlen0, Hcs0⟩ := Hfacts
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
    have hstab := mvcc.reader_answer log ilog pend Hcmp Hcnt' (by omega) Hwf0 Hcs0 k r hrlt
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
      iframe Hkn
      isplitl [Hrd]
      · iunfold mvcc.idxReader
        iexists t
        iframe Hrd
        iexact Htree
      isplitl []
      · iunfold mvcc.ownKeys
        iexists []
        isplitl []
        · iapply (ownSlice_nil (DFrac.own 1))
        isplitl []
        · iapply ownSliceCap_nil
        isplitl []
        · ipureintro; rfl
        simp only [List.zip_nil_left]
        iapply BigSepL.bigSepL_nil_intro
        iempintro
      isplitl []
      · iapply (ownSlice_nil (DFrac.own 1))
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply (ownSlice_nil (DFrac.own 1))
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply (ownSlice_nil (DFrac.own 1))
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro; rfl
    | some rr =>
      obtain ⟨m, c, v⟩ := rr
      simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil, List.length_singleton]
      wp_auto
      wp_apply wp_slice_literal (l := [key])
      isplitr
      · ipureintro; rfl
      iintro %ksl ⟨Hksl, Hkcap⟩
      wp_auto
      wp_apply wp_slice_literal (l := [mvcc.revVal m])
      isplitr
      · ipureintro; rfl
      iintro %msl ⟨Hmsl, Hmcap⟩
      wp_auto
      wp_apply wp_slice_literal (l := [mvcc.revVal c])
      isplitr
      · ipureintro; rfl
      iintro %csl ⟨Hcsl, Hccap⟩
      wp_auto
      wp_apply wp_slice_literal (l := [v])
      isplitr
      · ipureintro; rfl
      iintro %vsl ⟨Hvsl, Hvcap⟩
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
      iframe Hkn
      iframe Hvsl Hvcap Hcsl Hccap Hmsl Hmcap
      isplitl [Hrd]
      · iunfold mvcc.idxReader
        iexists t
        iframe Hrd
        iexact Htree
      isplitl [Hksl Hkcap]
      · iunfold mvcc.ownKeys
        iexists [key]
        iframe Hksl Hkcap
        isplitl []
        · ipureintro; rfl
        simp only [List.zip_cons_cons, List.zip_nil_left]
        iapply BigSepL.bigSepL_singleton.2
        iexact Hkey
      ipureintro; rfl
  · -- `end != nil`: `ti.unsafeVisit(key, end, f)`
    rw [mvcc.rangeTaken_false, mvcc.rangeTotal_false,
      mvcc.rangeAnswers_entries log ilog pend L Hcmp Hcnt' (by omega) Hwf0 Hcs0 HLL k e r hrlt]
    ipersist limit
    ipersist withTotalCount
    ipersist atRev
    ipersist ti
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply (hVisit ti t L sync.rfrac key endk k e _
      (mvcc.rangeInv keys_ptr modifies_ptr creates_ptr versions_ptr totalCount_ptr
        (mvcc.rangeEntries L k e) (W64 r) limit withTotal)
      (mvcc.rangeInv keys_ptr modifies_ptr creates_ptr versions_ptr totalCount_ptr
        (mvcc.rangeEntries L k e) (W64 r) limit withTotal (mvcc.rangeEntries L k e).length))
      $$ [$HtreeL keys modifies creates versions totalCount] as ⟨HtreeL, Hdone⟩
    · iframe #
      isplitl [keys modifies creates versions totalCount]
      · -- the invariant at the start
        iunfold mvcc.rangeInv
        iexists slice.nil, slice.nil, slice.nil, slice.nil, zero_val w64
        iframe keys modifies creates versions totalCount
        simp only [List.take_zero, mvcc.entryAnswers_nil, mvcc.takeLimit_nil, List.map_nil,
          List.length_nil, mvcc.totalOf_zero]
        isplitl []
        · iunfold mvcc.ownKeys
          iexists []
          isplitl []
          · iapply (ownSlice_nil (DFrac.own 1))
          isplitl []
          · iapply ownSliceCap_nil
          isplitl []
          · ipureintro; rfl
          simp only [List.zip_nil_left]
          iapply BigSepL.bigSepL_nil_intro
          iempintro
        isplitl []
        · iapply (ownSlice_nil (DFrac.own 1))
        isplitl []
        · iapply ownSliceCap_nil
        isplitl []
        · iapply (ownSlice_nil (DFrac.own 1))
        isplitl []
        · iapply ownSliceCap_nil
        isplitl []
        · iapply (ownSlice_nil (DFrac.own 1))
        isplitl []
        · iapply ownSliceCap_nil
        ipureintro; rfl
      · -- the visitor
        iunfold mvcc.visitSpec
        iintro %i %z %Hz
        wp_start_folded as ⟨HP, Hz, #Hzi⟩
        iunfold mvcc.rangeInv at HP
        icases HP with ⟨%keys, %modifies, %creates, %versions, %total, Hkeys, Hmod, Hcre, Hver, Htot,
          Hks, Hmsl, Hmcap, Hcsl, Hccap, Hvsl, Hvcap, %Htot⟩
        iunfold mvcc.ownKeys at Hks
        icases Hks with ⟨%kss, Hksl, Hkcap, %Hkslen, #Hzip⟩
        ihave %Hslen := ownSlice_len _ _ _ $$ Hksl
        iunfold mvcc.ownEntry at Hz
        icases Hz with ⟨%Hnn, %gs, Hki⟩
        iunfold mvcc.kiItemIs at Hzi
        icases Hzi with ⟨-, #Hkz⟩
        iunfold mvcc.kiKey at Hkz
        icases Hkz with ⟨%zks, #Hzkf, #Hzks⟩
        have hzL : z ∈ L := by
          have h := List.mem_of_getElem? Hz
          unfold mvcc.rangeEntries at h
          exact (List.mem_filter.1 h).1
        wp_auto
        wp_apply (wp_reachedLimit (V := GoSlice) (go.GoType.SliceType go.byte) limit limit_ptr keys_ptr
          keys _) $$ [$limit $Hkeys $Hksl] as %b ⟨%hb, Hkeys, Hksl⟩
        rw [Hkslen, List.length_map, mvcc.reached_takeLimit] at hb
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
          iunfold mvcc.rangeInv
          iexists keys, modifies, creates, versions, total
          rw [List.take_length,
            mvcc.takeLimit_of_prefix _ (mvcc.entryAnswers_prefix (mvcc.rangeEntries L k e) (W64 r) i) hre,
            mvcc.totalOf_reached _ _ _ (mvcc.entryAnswers_prefix (mvcc.rangeEntries L k e) (W64 r) i).length_le hre]
          iframe Hkeys Hmod Hcre Hver Htot Hmsl Hmcap Hcsl Hccap Hvsl Hvcap
          isplitl [Hksl Hkcap]
          · iunfold mvcc.ownKeys
            iexists kss
            iframe Hksl Hkcap
            isplitl []
            · ipureintro; exact Hkslen
            iexact Hzip
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
            iunfold mvcc.rangeInv
            iexists keys, modifies, creates, versions, total
            rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
            simp only [Option.map_none, Option.toList_none, List.append_nil]
            iframe Hkeys Hmod Hcre Hver Htot Hmsl Hmcap Hcsl Hccap Hvsl Hvcap
            isplitl [Hksl Hkcap]
            · iunfold mvcc.ownKeys
              iexists kss
              iframe Hksl Hkcap
              isplitl []
              · ipureintro; exact Hkslen
              iexact Hzip
            ipureintro; exact Htot
          | some rr =>
            obtain ⟨m, c, v⟩ := rr
            wp_auto
            cases hre : mvcc.reached (mvcc.limitOf limit)
                (mvcc.entryAnswers ((mvcc.rangeEntries L k e).take i) (W64 r)).length with
            | false =>
              -- `!reachedLimit`: the four appends
              (try wp_auto)
              wp_apply wp_slice_literal (l := [mvcc.revVal m])
              isplitr
              · ipureintro; rfl
              iintro %sl2 ⟨Hsl2, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hmsl $Hmcap $Hsl2] as %modifies' ⟨Hmsl, Hmcap, -⟩
              (try wp_auto)
              wp_apply wp_slice_literal (l := [zks])
              isplitr
              · ipureintro; rfl
              iintro %sl3 ⟨Hsl3, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hksl $Hkcap $Hsl3] as %keys' ⟨Hksl, Hkcap, -⟩
              (try wp_auto)
              wp_apply wp_slice_literal (l := [mvcc.revVal c])
              isplitr
              · ipureintro; rfl
              iintro %sl4 ⟨Hsl4, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hcsl $Hccap $Hsl4] as %creates' ⟨Hcsl, Hccap, -⟩
              (try wp_auto)
              wp_apply wp_slice_literal (l := [v])
              isplitr
              · ipureintro; rfl
              iintro %sl5 ⟨Hsl5, -⟩
              wp_auto
              wp_apply wp_slice_append $$ [$Hvsl $Hvcap $Hsl5] as %versions' ⟨Hvsl, Hvcap, -⟩
              (try wp_auto)
              iapply HΦ
              isplitl [Hki]
              · iunfold mvcc.ownEntry
                isplitl []
                · ipureintro; exact Hnn
                iexists gs; iexact Hki
              simp only [↓reduceIte]
              iunfold mvcc.rangeInv
              iexists keys', modifies', creates', versions', (total + W64 1)
              rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
              simp only [Option.map_some, Option.toList_some]
              rw [mvcc.takeLimit_append_not _ _ _ hre, List.map_append, List.map_append,
                List.map_append, List.map_append, List.length_append,
                List.length_singleton, mvcc.totalOf_succ _ _ _ (Or.inr hre)]
              simp only [List.map_cons, List.map_nil]
              iframe Hkeys Hmod Hcre Hver Htot Hmsl Hmcap Hcsl Hccap Hvsl Hvcap
              isplitl [Hksl Hkcap]
              · iapply (mvcc.ownKeys_snoc keys' kss _ Hkslen zks z.2.1) $$ Hzip Hksl Hkcap Hzks
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
              iunfold mvcc.rangeInv
              iexists keys, modifies, creates, versions, (total + W64 1)
              rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
              simp only [Option.map_some, Option.toList_some]
              rw [mvcc.takeLimit_append_reached _ _ _ hre, List.length_append,
                List.length_singleton, mvcc.totalOf_succ _ _ _ (Or.inl hwt)]
              iframe Hkeys Hmod Hcre Hver Htot Hmsl Hmcap Hcsl Hccap Hvsl Hvcap
              isplitl [Hksl Hkcap]
              · iunfold mvcc.ownKeys
                iexists kss
                iframe Hksl Hkcap
                isplitl []
                · ipureintro; exact Hkslen
                iexact Hzip
              ipureintro
              subst Htot
              word
    -- after the visit: the answers of all the entries in range
    ihave HQ : mvcc.rangeInv (GF := GF) keys_ptr modifies_ptr creates_ptr versions_ptr totalCount_ptr
        (mvcc.rangeEntries L k e) (W64 r) limit withTotal (mvcc.rangeEntries L k e).length $$ [Hdone]
    · icases Hdone with (H | H) <;> iexact H
    iunfold mvcc.rangeInv at HQ
    icases HQ with ⟨%keys, %modifies, %creates, %versions, %total, Hkeys, Hmod, Hcre, Hver, Htot,
      Hks, Hmsl, Hmcap, Hcsl, Hccap, Hvsl, Hvcap, %Htot⟩
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
    iframe Hkn
    rw [List.take_length]
    iframe Hks Hmsl Hmcap Hcsl Hccap Hvsl Hvcap
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
