/-
Proof of `Spec/.../mvcc/treeIndex__CountRevisions.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__CountRevisions
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

/-- The visitor's invariant: after the first `i` entries in range, `total`. -/
def mvcc.countInv (total_ptr : Loc) (vis : List mvcc.IdxEntry) (atRev : w64) (i : Nat) : IProp GF :=
  iprop(∃ (total : w64), total_ptr ↦ total ∗
    ⌜total = W64 (mvcc.entryAnswers (vis.take i) atRev).length⌝)

theorem mvcc.treeIndex.CountRevisions.wp_proof
    (hUnsafe : mvcc.treeIndex.unsafeGet.spec (GF := GF) (hG := hG))
    (hVisit : mvcc.treeIndex.unsafeVisit.spec (GF := GF) (hG := hG))
    (hget : mvcc.keyIndex.get.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.CountRevisions.spec (GF := GF) (hG := hG) := by
  intro ti γ kn key endk k e atRev e0 q c
  generalize hlog : kn.log = log at *
  wp_start as ⟨#Hti, Hrd, Hkn, Hcu, %Hcb, %Hrev, #Hkey, #Hend, #Herr⟩
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
  icases HP with ⟨%ilog, %pend, %L, %cmax, HP⟩
  iNamedSuffix HP "L"
  ihave %Hcle := mvcc.crevUB_lb γ q c cmax Hcb.1 HLL.2 $$ Hcu HcrevL
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
  have hne := entries_not_emptyC L _ cmax HLL.1
  subst hr
  wp_if_destruct
  · -- `end == nil`: the one key, `ti.unsafeGet(key, atRev)`
    wp_apply (hUnsafe ti t lg L sync.rfrac key k (W64 r) e0) $$ [$HtreeL] as ⟨HtreeL, -⟩
    · iframe #
      ipureintro
      exact ⟨Hlgnn, hne⟩
    have hstab := mvcc.reader_answerC log ilog pend L cmax Hcmp Hcnt' ⟨HwfL, HlenL, HpendL, HcsL⟩
      Hwf0 Hcs0 HLL.1 k r hrlt Hlen0 (by omega)
    have hval : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) (W64 r)
        (GoInterface.ok e0) = mvcc.kiGetVal (mvcc.kiOfKey (mvcc.evsOf log) k) (W64 r) (GoInterface.ok e0) := by
      unfold mvcc.kiGetVal; rw [hstab]
    rw [hval, mvcc.rangeAnswers_nil]
    unfold mvcc.kiGetVal
    cases hg : mvcc.kiGet (mvcc.kiOfKey (mvcc.evsOf log) k) (W64 r) with
    | none =>
      simp only [Option.map_none, Option.toList_none, List.length_nil]
      wp_auto
      -- the deferred `ti.RUnlock()`
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
      wp_call
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL HcmpL] as Hrd
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L, cmax
        simp only [named]
        iframe HnevL HtreeL HcmpL
        iframe #
        ipureintro
        exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
      (try wp_auto)
      iapply HΦ
      iframe Hkn Hcu
      iunfold mvcc.idxReader
      iexists t
      iframe Hrd
      iexact Htree
    | some rr =>
      obtain ⟨m, c, v⟩ := rr
      simp only [Option.map_some, Option.toList_some, List.length_singleton]
      wp_auto
      -- the deferred `ti.RUnlock()`
      rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
      wp_call
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL HcmpL] as Hrd
      · inext
        iunfold mvcc.idxLockInv
        iexists ilog, pend, L, cmax
        simp only [named]
        iframe HnevL HtreeL HcmpL
        iframe #
        ipureintro
        exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
      (try wp_auto)
      iapply HΦ
      iframe Hkn Hcu
      iunfold mvcc.idxReader
      iexists t
      iframe Hrd
      iexact Htree
  · -- `end != nil`: `ti.unsafeVisit(key, end, f)`
    rw [mvcc.rangeAnswers_entriesC log ilog pend L cmax Hcmp Hcnt' ⟨HwfL, HlenL, HpendL, HcsL⟩ Hwf0 Hcs0
        HLL.1 k e r hrlt Hlen0 (by omega)]
    ipersist atRev
    ipersist ti
    wp_apply (hVisit ti t L sync.rfrac key endk k e _
      (mvcc.countInv total_ptr (mvcc.rangeEntries L k e) (W64 r))
      (mvcc.countInv total_ptr (mvcc.rangeEntries L k e) (W64 r) (mvcc.rangeEntries L k e).length))
      $$ [$HtreeL total] as ⟨HtreeL, Hdone⟩
    · iframe #
      isplitl [total]
      · -- the invariant at the start
        iunfold mvcc.countInv
        iexists (W64 0)
        iframe total
        ipureintro
        simp only [List.take_zero, mvcc.entryAnswers_nil, List.length_nil]
        rfl
      · -- the visitor
        iunfold mvcc.visitSpec
        iintro %i %z %Hz
        wp_start_folded as ⟨HP, Hz, #Hzi⟩
        iunfold mvcc.countInv at HP
        icases HP with ⟨%total, Htot, %Htot⟩
        iunfold mvcc.ownEntry at Hz
        icases Hz with ⟨%Hnn, %gs, Hki⟩
        have hzL : z ∈ L := by
          have h := List.mem_of_getElem? Hz
          unfold mvcc.rangeEntries at h
          exact (List.mem_filter.1 h).1
        wp_auto
        ihave #HzKey := Hzi
        iunfold mvcc.kiItemIs at HzKey
        icases HzKey with ⟨-, #HzKey⟩
        wp_apply (hget z.1 gs z.2.2 z.2.1 (DFrac.own sync.rfrac) lg (W64 r) e0) $$ [$HzKey $Hki $Herr]
          as %res Hres
        · ipureintro; exact Hlgnn
        simp only [hne z hzL, Bool.false_eq_true, ↓reduceIte]
        icases Hres with ⟨%Hres, Hki⟩
        subst Hres
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
          iunfold mvcc.countInv
          iexists total
          rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
          simp only [Option.map_none, Option.toList_none, List.append_nil]
          iframe Htot
          ipureintro; exact Htot
        | some rr =>
          obtain ⟨m, c, v⟩ := rr
          wp_auto
          iapply HΦ
          isplitl [Hki]
          · iunfold mvcc.ownEntry
            isplitl []
            · ipureintro; exact Hnn
            iexists gs; iexact Hki
          simp only [↓reduceIte]
          iunfold mvcc.countInv
          iexists (total + W64 1)
          rw [mvcc.entryAnswers_take_succ _ _ i z Hz, hg]
          simp only [Option.map_some, Option.toList_some, List.length_append, List.length_singleton]
          iframe Htot
          ipureintro
          subst Htot
          word
    -- after the visit: the answers of all the entries in range
    ihave HQ : mvcc.countInv (GF := GF) total_ptr (mvcc.rangeEntries L k e) (W64 r)
        (mvcc.rangeEntries L k e).length $$ [Hdone]
    · icases Hdone with (H | H) <;> iexact H
    iunfold mvcc.countInv at HQ
    icases HQ with ⟨%total, Htot, %Htot⟩
    wp_auto
    -- the deferred `ti.RUnlock()`
    rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
    wp_call
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL HcmpL] as Hrd
    · inext
      iunfold mvcc.idxLockInv
      iexists ilog, pend, L, cmax
      simp only [named]
      iframe HnevL HtreeL HcmpL
      iframe #
      ipureintro
      exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
    (try wp_auto)
    rw [List.take_length] at Htot
    subst Htot
    iapply HΦ
    iframe Hkn Hcu
    iunfold mvcc.idxReader
    iexists t
    iframe Hrd
    iexact Htree

end proof

end EtcdGrove
end Perennial
