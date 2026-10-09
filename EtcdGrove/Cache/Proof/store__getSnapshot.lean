/-
Proof of `Spec/store__getSnapshot.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.store__getSnapshot
import EtcdGrove.Cache.Spec.ringBuffer__DescendLessOrEqual

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- For sorted revisions, the items at or below `rev` are a prefix: `leCount` of them. -/
theorem store_getSnapshot_take_le (rev : w64) :
    ∀ (h : List (w64 × KvMap)), RevSorted Prod.fst h →
      h.take (leCount Prod.fst rev h) = h.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev))
  | [], _ => rfl
  | a :: l, hs => by
    unfold RevSorted at hs
    rw [List.pairwise_cons] at hs
    by_cases ha : sint.Z a.1 ≤ sint.Z rev
    · have h1 : leCount Prod.fst rev (a :: l) = leCount Prod.fst rev l + 1 := by
        unfold leCount; rw [List.countP_cons]; simp [ha]
      rw [h1, List.take_succ_cons, List.filter_cons, ite_eq_left (by simpa using ha),
        store_getSnapshot_take_le rev l hs.2]
    · have hl : ∀ x ∈ l, ¬ sint.Z x.1 ≤ sint.Z rev := fun x hx => by
        have := hs.1 x hx; omega
      have h0 : leCount Prod.fst rev (a :: l) = 0 := by
        unfold leCount; rw [List.countP_eq_zero]
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simpa using ha
        · simpa using hl x hx
      rw [h0, List.take_zero, List.filter_cons, ite_eq_right (by simpa using ha)]
      symm; rw [List.filter_eq_nil_iff]; intro x hx; simpa using hl x hx

/-- The first item `DescendLessOrEqual(rev)` visits is the newest snapshot at or below
`rev`. -/
theorem store_getSnapshot_first (rev : w64) (h : List (w64 × KvMap)) (hs : RevSorted Prod.fst h) :
    (descendLeVisited Prod.fst rev h)[0]? =
      (h.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev))).getLast? := by
  rw [descendLeVisited, store_getSnapshot_take_le rev h hs, ← List.head?_eq_getElem?,
    List.head?_reverse]

theorem store.getSnapshot.wp_proof
    (wp_DescendLessOrEqual : ringBuffer.DescendLessOrEqual.spec (GF := GF) (hG := hG)) :
    store.getSnapshot.spec (GF := GF) (hG := hG) := by
  intro s γ cap r0 rev
  wp_start as ⟨#HS, Hrd, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold storeReader
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  unfold storeLockInv
  iNamed HP
  unfold storeRevLb
  ihave #Hnewlb := monoNatLbOwn_get $$ Hrev
  ihave %Hle := monoNatLbOwn_valid $$ Hrev Hlb
  have Hr0 : sint.Z r0 ≤ sint.Z st.latestRev := by
    have := Hinv.rev_nonneg; have := Hle.2; word
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hci with ⟨⟨%eNR, #HeNR⟩, -, -⟩
  icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eCP, #HeCP, -⟩⟩
  wp_auto
  wp_if_destruct
  · -- not ready
    have Hm : snapModel st rev = .notReady := by simp [snapModel, Hif]
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist] as Hrd
    · inext; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    iapply HΦ
    iframe Hrd
    iexists st
    unfold storeSeen storeRevLb
    rw [Hm]
    iframe Hnewlb
    simp only [snapErr]
    iframe HeNR
    ipureintro; exact ⟨⟨Hinv, Hr0⟩, by simp⟩
  have Hnz := Hif
  wp_if_destruct
  · -- invalid revision
    have Hneg : sint.Z rev < 0 := by word
    have Hm : snapModel st rev = .invalid := by
      unfold snapModel; rw [ite_eq_right Hnz, ite_eq_left Hneg]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %e _
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist] as Hrd
    · inext; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    iapply HΦ
    iframe Hrd
    iexists st
    unfold storeSeen storeRevLb
    rw [Hm]
    iframe Hnewlb
    simp only [snapErr]
    ipureintro; exact ⟨⟨Hinv, Hr0⟩, ⟨e, rfl⟩, by simp⟩
  have Hnn : ¬ sint.Z rev < 0 := by word
  wp_join iprop(s_ptr ↦ s ∗ rev_ptr ↦ (if rev = W64 0 then st.latestRev else rev) ∗
      storeLatestRevAddr s ↦{DFrac.own sync.rfrac} st.latestRev) with [s rev HlatestRev]
    as ⟨s, rev, HlatestRev⟩
  · rw [ite_eq_right Hif]; iframe
  generalize Hrev' : (if rev = W64 0 then st.latestRev else rev) = rev'
  wp_if_destruct
  · -- a future revision
    have Hm : snapModel st rev = .future := by
      unfold snapModel; rw [ite_eq_right Hnz, ite_eq_right Hnn]; simp only [Hrev']
      rw [ite_eq_left Hif]
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist] as Hrd
    · inext; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    iapply HΦ
    iframe Hrd
    iexists st
    unfold storeSeen storeRevLb
    rw [Hm]
    iframe Hnewlb
    simp only [snapErr]
    iframe HeFR
    ipureintro; exact ⟨⟨Hinv, Hr0⟩, by simp⟩
  have Hfut := Hif
  have Hsorted := Hinv.hist_sorted
  wp_apply (wp_DescendLessOrEqual (go.GoType.PointerType snapshot.ty) (storeHistAddr s) cap snapIs
    Prod.fst st.history (DFrac.own sync.rfrac) rev' _
    (fun i => iprop(targetSnapshot_ptr ↦ (null : Loc) ∗ ⌜i = 0⌝))
    iprop(∃ (p : Loc) (v : w64 × KvMap), targetSnapshot_ptr ↦ p ∗ snapIs p v ∗
      ⌜(descendLeVisited Prod.fst rev' st.history)[0]? = some v⌝))
    $$ [Hhist targetSnapshot] as ⟨Hhist, Hpost⟩
  · iframe Hhist
    isplitl [targetSnapshot]
    · iframe; ipureintro; rfl
    unfold iterSpec
    iintro %i %p %v %Hv
    wp_start_folded as ⟨⟨Htgt, %Hi⟩, #Hp⟩
    subst Hi
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    iexists p, v
    iframe
    isplitl []
    · iexact Hp
    ipureintro; exact Hv
  have Hfirst := store_getSnapshot_first rev' st.history Hsorted
  have Hbase : snapModel st rev =
      match (st.history.filter (fun x => decide (sint.Z x.1 ≤ sint.Z rev'))).getLast? with
      | some h => .ok h.1 h.2
      | none => .compacted := by
    unfold snapModel; rw [ite_eq_right Hnz, ite_eq_right Hnn]; simp only [Hrev']
    rw [ite_eq_right Hfut]
    rfl
  icases Hpost with (⟨%p, %v, Htgt, #Hp, %Hv⟩ | ⟨Htgt, %Hlen⟩)
  · -- found
    have Hm : snapModel st rev = .ok v.1 v.2 := by rw [Hbase, ← Hfirst, Hv]
    ihave %Hpnn : ⌜p ≠ null⌝ $$ [Hp]
    · unfold snapIs; icases Hp with ⟨%t, #Hpt, -⟩
      iapply typedPointsto_not_null $$ Hpt
    wp_auto
    rw [decide_eq_false Hpnn]
    wp_auto
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist] as Hrd
    · inext; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    iapply HΦ
    iframe Hrd
    iexists st
    unfold storeSeen storeRevLb
    rw [Hm]
    iframe Hnewlb
    simp only [snapErr]
    isplitr
    · ipureintro; exact ⟨Hinv, Hr0⟩
    isplitr
    · ipureintro; trivial
    isplitr
    · ipureintro; trivial
    iexact Hp
  · -- compacted
    have Hm : snapModel st rev = .compacted := by
      rw [Hbase, ← Hfirst, List.getElem?_eq_none (by omega)]
    wp_auto
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hst Hrev HlatestRev Hhist] as Hrd
    · inext; iexists st; simp only [named]; iframe; ipureintro; exact Hinv
    iapply HΦ
    iframe Hrd
    iexists st
    unfold storeSeen storeRevLb
    rw [Hm]
    iframe Hnewlb
    simp only [snapErr]
    iframe HeCP
    ipureintro; exact ⟨⟨Hinv, Hr0⟩, by simp⟩

end proof

end EtcdGrove
end Perennial
