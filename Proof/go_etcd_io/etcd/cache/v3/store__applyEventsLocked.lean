/-
Proof of `Spec/store__applyEventsLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__applyEventsLocked
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Delete
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__ReplaceOrInsert
public import Spec.go_etcd_io.etcd.cache.v3.newKVItem
public import Spec.go_etcd_io.etcd.cache.v3.newClonedSnapshot
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__Append

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## The model, batch by batch -/

theorem applyEventsLocked_applyBatch_append (m : KvMap) (b c : List EvModel) :
    applyBatch m (b ++ c) =
      match applyBatch m b with
      | (m', true) => applyBatch m' c
      | (m', false) => (m', false) := by
  induction b generalizing m with
  | nil => simp [applyBatch]
  | cons e es ih =>
    simp only [List.cons_append, applyBatch]
    cases applyEv m e with
    | some m' => exact ih m'
    | none => rfl

theorem applyEventsLocked_btDelete_of_find_none {k : KvEntry} {m : KvMap}
    (h : btFind kvLess k m = none) : btDelete kvLess k m = m := by
  induction m with
  | nil => rfl
  | cons w ws ih =>
    unfold btFind at h
    unfold btDelete
    split at h
    · rename_i hw; simp only [hw, ↓reduceIte, ih h]
    · rename_i hw
      simp only [hw, ↓reduceIte]
      split at h
      · rename_i hk; simp only [hk, ↓reduceIte]
      · simp at h

theorem applyEventsLocked_ringAppend_mem {V : Type} {cap : Nat} {items : List V} {v x : V}
    (h : x ∈ ringAppend cap items v) : x = v ∨ x ∈ items := by
  unfold ringAppend at h
  split at h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_singleton.1 h)
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr (List.mem_of_mem_tail h)
    · exact Or.inl (List.mem_singleton.1 h)

theorem applyEventsLocked_ringAppend_length {V : Type} {cap : Nat} {items : List V} {v : V}
    (hc : 0 < cap) (h : items.length ≤ cap) : (ringAppend cap items v).length ≤ cap := by
  unfold ringAppend
  split
  · simp; omega
  · simp; omega

/-- A whole batch `bt` (all of revision `e.rev`, starting with `e`) followed by `r`, which does
not start with that revision: `applyEvents` applies the batch and goes on with `r`. -/
theorem applyEventsLocked_step (cap : Nat) (st : StoreState) (bt r : List EvModel) (e : EvModel)
    (hbt : bt.head? = some e) (he : ∀ x ∈ bt, x.rev = e.rev)
    (hr : ∀ y, r.head? = some y → y.rev ≠ e.rev) (m : KvMap)
    (hm : applyBatch st.latest bt = (m, true)) :
    applyEvents cap st (bt ++ r) =
      applyEvents cap
        { latestRev := e.rev, latest := m, history := ringAppend cap st.history (e.rev, m) } r := by
  cases bt with
  | nil => simp at hbt
  | cons e' bs =>
    simp only [List.head?_cons, Option.some.injEq] at hbt
    subst hbt
    have hpos : ∀ a ∈ e' :: bs, decide (a.rev = e'.rev) = true := fun a ha => by simp [he a ha]
    have htw : (e' :: (bs ++ r)).takeWhile (fun x => decide (x.rev = e'.rev)) = e' :: bs := by
      rw [← List.cons_append, List.takeWhile_append_of_pos hpos]
      cases r with
      | nil => simp
      | cons y ys =>
        rw [List.takeWhile_cons_of_neg (by simpa using hr y rfl)]; simp
    have hdw : (e' :: (bs ++ r)).dropWhile (fun x => decide (x.rev = e'.rev)) = r := by
      rw [← List.cons_append, List.dropWhile_append_of_pos hpos]
      cases r with
      | nil => simp
      | cons y ys => rw [List.dropWhile_cons_of_neg (by simpa using hr y rfl)]
    rw [List.cons_append, applyEvents.eq_2, htw, hm]
    simp only
    rw [hdw]

/-- An event `ev` of the current batch fails after `bt` succeeded: `applyEvents` stops there. -/
theorem applyEventsLocked_fail (cap : Nat) (st : StoreState) (bt rest : List EvModel)
    (e ev : EvModel) (hhead : (bt ++ ev :: rest).head? = some e)
    (he : ∀ x ∈ bt, x.rev = e.rev) (hev : ev.rev = e.rev) (m : KvMap)
    (hm : applyBatch st.latest bt = (m, true)) (hfail : applyEv m ev = none) :
    applyEvents cap st (bt ++ ev :: rest) = ({ st with latest := m }, false) := by
  have hpos : ∀ a ∈ bt ++ [ev], decide (a.rev = e.rev) = true := fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · simp [he a h]
    · rw [List.mem_singleton.1 h]; simp [hev]
  have hb : applyBatch st.latest
      ((bt ++ ev :: rest).takeWhile (fun x => decide (x.rev = e.rev))) = (m, false) := by
    rw [show bt ++ ev :: rest = (bt ++ [ev]) ++ rest by simp,
      List.takeWhile_append_of_pos hpos, List.append_assoc,
      applyEventsLocked_applyBatch_append, hm]
    simp [applyBatch, hfail]
  cases hbt : bt ++ ev :: rest with
  | nil => simp at hbt
  | cons e' es =>
    rw [hbt] at hhead hb
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [applyEvents.eq_2, hb]

theorem applyEventsLocked_revAbove {cap : Nat} {stc : StoreState} (hinv : StoreInv cap stc)
    {rev : w64} (hlt : sint.Z stc.latestRev < sint.Z rev) (m : KvMap) :
    RevAbove Prod.fst stc.history (rev, m) := by
  intro last hlast
  have := hinv.hist_le last (List.mem_of_getLast? hlast)
  simp only
  omega

theorem applyEventsLocked_inv_batch {cap : Nat} {stc : StoreState} (hinv : StoreInv cap stc)
    {rev : w64} (hlt : sint.Z stc.latestRev < sint.Z rev) {m : KvMap}
    (hm : m.Pairwise kvLess) :
    StoreInv cap
      { latestRev := rev, latest := m, history := ringAppend cap stc.history (rev, m) } where
  cap_pos := hinv.cap_pos
  cap_le := hinv.cap_le
  rev_nonneg := by have := hinv.rev_nonneg; simp only; omega
  latest_sorted := hm
  hist_len := applyEventsLocked_ringAppend_length hinv.cap_pos hinv.hist_len
  hist_sorted := hinv.hist_sorted.ringAppend_of (applyEventsLocked_revAbove hinv hlt m) cap
  hist_le h hh := by
    rcases applyEventsLocked_ringAppend_mem hh with rfl | hh
    · simp
    · have := hinv.hist_le h hh; simp only; omega
  hist_maps_sorted h hh := by
    rcases applyEventsLocked_ringAppend_mem hh with rfl | hh
    · exact hm
    · exact hinv.hist_maps_sorted h hh

theorem applyEventsLocked_inv_latest {cap : Nat} {stc : StoreState} (hinv : StoreInv cap stc)
    {m : KvMap} (hm : m.Pairwise kvLess) : StoreInv cap { stc with latest := m } where
  cap_pos := hinv.cap_pos
  cap_le := hinv.cap_le
  rev_nonneg := hinv.rev_nonneg
  latest_sorted := hm
  hist_len := hinv.hist_len
  hist_sorted := hinv.hist_sorted
  hist_le := hinv.hist_le
  hist_maps_sorted := hinv.hist_maps_sorted


theorem applyEventsLocked_mem_take {evs : List EvModel} {j k : Nat} {x : EvModel}
    (h : x ∈ (evs.drop j).take (k - j)) : ∃ n, j ≤ n ∧ n < k ∧ evs[n]? = some x := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_take] at hn
  split at hn
  · rw [List.getElem?_drop] at hn
    exact ⟨j + n, by omega, by omega, hn⟩
  · simp at hn

theorem applyEventsLocked_split (evs : List EvModel) {j k : Nat} (hjk : j ≤ k) :
    evs.drop j = (evs.drop j).take (k - j) ++ evs.drop k := by
  conv => lhs; rw [← List.take_append_drop (k - j) (evs.drop j)]
  rw [List.drop_drop, show j + (k - j) = k by omega]

theorem applyEventsLocked_take_succ {evs : List EvModel} {j k : Nat} {e1 : EvModel}
    (hjk : j ≤ k) (he1 : evs[k]? = some e1) :
    (evs.drop j).take (k + 1 - j) = (evs.drop j).take (k - j) ++ [e1] := by
  rw [show k + 1 - j = (k - j) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show j + (k - j) = k by omega, he1]
  rfl

theorem applyEventsLocked_drop_cons {evs : List EvModel} {k : Nat} {e1 : EvModel}
    (he1 : evs[k]? = some e1) : evs.drop k = e1 :: evs.drop (k + 1) := by
  have hk : k < evs.length := (List.getElem?_eq_some_iff.1 he1).1
  rw [List.drop_eq_getElem_cons hk, (List.getElem?_eq_some_iff.1 he1).2]

theorem applyEventsLocked_inner_step {stc : StoreState} {evs : List EvModel} {j k : Nat}
    {m m' : KvMap} {e1 : EvModel} (hjk : j ≤ k) (he1 : evs[k]? = some e1)
    (hb : applyBatch stc.latest ((evs.drop j).take (k - j)) = (m, true))
    (hev : applyEv m e1 = some m') :
    applyBatch stc.latest ((evs.drop j).take (k + 1 - j)) = (m', true) := by
  rw [applyEventsLocked_take_succ hjk he1, applyEventsLocked_applyBatch_append, hb]
  simp [applyBatch, hev]

theorem applyEventsLocked_inner_inv {stc : StoreState} {evs : List EvModel} {j k : Nat}
    {m m' : KvMap} {e0 e1 : EvModel} (hjk : j ≤ k) (he1 : evs[k]? = some e1)
    (hr1 : e1.rev = e0.rev)
    (hm : applyBatch stc.latest ((evs.drop j).take (k - j)) = (m, true) ∧
      (∀ (n : Nat) (e : EvModel), j ≤ n → n < k → evs[n]? = some e → e.rev = e0.rev) ∧
      m.Pairwise kvLess)
    (hev : applyEv m e1 = some m') (hs : m'.Pairwise kvLess) :
    applyBatch stc.latest ((evs.drop j).take (k + 1 - j)) = (m', true) ∧
      (∀ (n : Nat) (e : EvModel), j ≤ n → n < k + 1 → evs[n]? = some e → e.rev = e0.rev) ∧
      m'.Pairwise kvLess := by
  refine ⟨applyEventsLocked_inner_step hjk he1 hm.1 hev, fun n e h1 h2 h3 => ?_, hs⟩
  rcases Nat.lt_or_ge n k with h | h
  · exact hm.2.1 n e h1 h h3
  · have : n = k := by omega
    subst this; rw [he1] at h3; cases h3; exact hr1

theorem applyEventsLocked_sorted_le {evs : List EvModel} (h : EvRevSorted evs) {a b : Nat}
    {x y : EvModel} (hab : a ≤ b) (hx : evs[a]? = some x) (hy : evs[b]? = some y) :
    sint.Z x.rev ≤ sint.Z y.rev := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · unfold EvRevSorted at h
    rw [List.pairwise_iff_getElem] at h
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    exact h a b ha hb hlt
  · have : a = b := by omega
    subst this; rw [hx] at hy; cases hy; exact Int.le_refl _

theorem applyEventsLocked_batch_done {cap : Nat} {st stc : StoreState} {evs : List EvModel}
    {j k : Nat} {m : KvMap} {e0 : EvModel}
    (hsorted : EvRevSorted evs) (he0 : evs[j]? = some e0) (hjk : j < k) (hkl : k ≤ evs.length)
    (hm : applyBatch stc.latest ((evs.drop j).take (k - j)) = (m, true) ∧
      (∀ (n : Nat) (e : EvModel), j ≤ n → n < k → evs[n]? = some e → e.rev = e0.rev) ∧
      m.Pairwise kvLess)
    (hexit : ∀ y, evs[k]? = some y → y.rev ≠ e0.rev)
    (hstc : StoreInv cap stc ∧ applyEvents cap st evs = applyEvents cap stc (evs.drop j) ∧
      (∀ e ∈ evs.drop j, sint.Z stc.latestRev < sint.Z e.rev) ∧
      sint.Z st.latestRev ≤ sint.Z stc.latestRev) :
    RevAbove Prod.fst stc.history (e0.rev, m) ∧
    StoreInv cap
      { latestRev := e0.rev, latest := m, history := ringAppend cap stc.history (e0.rev, m) } ∧
    applyEvents cap st evs = applyEvents cap
      { latestRev := e0.rev, latest := m, history := ringAppend cap stc.history (e0.rev, m) }
      (evs.drop k) ∧
    (∀ e ∈ evs.drop k, sint.Z e0.rev < sint.Z e.rev) ∧
    sint.Z st.latestRev ≤ sint.Z e0.rev := by
  have hdj := applyEventsLocked_drop_cons he0
  have hlt0 : sint.Z stc.latestRev < sint.Z e0.rev := hstc.2.2.1 e0 (by rw [hdj]; simp)
  refine ⟨applyEventsLocked_revAbove hstc.1 hlt0 m,
    applyEventsLocked_inv_batch hstc.1 hlt0 hm.2.2, ?_, ?_, by have := hstc.2.2.2; omega⟩
  · rw [hstc.2.1, applyEventsLocked_split evs (Nat.le_of_lt hjk)]
    apply applyEventsLocked_step cap stc _ _ e0
    · rw [hdj, show k - j = (k - j - 1) + 1 by omega, List.take_succ_cons]; rfl
    · intro x hx
      obtain ⟨n, h1, h2, h3⟩ := applyEventsLocked_mem_take hx
      exact hm.2.1 n x h1 h2 h3
    · intro y hy
      rw [List.head?_drop] at hy
      exact hexit y hy
    · exact hm.1
  · intro e he
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
    rw [List.getElem?_drop] at hn
    have hkn : k < evs.length := by
      have := (List.getElem?_eq_some_iff.1 hn).1; omega
    obtain ⟨y, hy⟩ : ∃ y, evs[k]? = some y := ⟨_, List.getElem?_eq_getElem hkn⟩
    have h1 := applyEventsLocked_sorted_le hsorted (Nat.le_of_lt hjk) he0 hy
    have h2 := applyEventsLocked_sorted_le hsorted (Nat.le_add_right k n) hy hn
    have h3 := hexit y hy
    have h4 : sint.Z y.rev ≠ sint.Z e0.rev := fun h => h3 (by
      apply BitVec.eq_of_toInt_eq; exact h)
    omega

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem applyEventsLocked_kvsAt_sub {m m' : KvMap} (h : ∀ x ∈ m', x ∈ m) :
    kvsAt (GF := GF) m ⊢ kvsAt m' := by
  unfold kvsAt
  iintro #H
  imodintro
  iintro %x %hx
  iapply H
  ipureintro; exact h x hx

theorem applyEventsLocked_kvsAt_insert {m : KvMap} {e : KvEntry} :
    kvsAt (GF := GF) m ∗ kvAt e ⊢ kvsAt (btInsert kvLess e m) := by
  unfold kvsAt
  iintro ⟨#H, #He⟩
  imodintro
  iintro %x %hx
  rcases btInsert_mem hx with rfl | hx
  · iexact He
  · iapply H; ipureintro; exact hx

theorem store.applyEventsLocked.wp_proof
    (wp_Delete : btree.BTree.Delete.spec (GF := GF) (hG := hG))
    (wp_ReplaceOrInsert : btree.BTree.ReplaceOrInsert.spec (GF := GF) (hG := hG))
    (wp_newKVItem : newKVItem.spec (GF := GF) (hG := hG))
    (wp_newClonedSnapshot : newClonedSnapshot.spec (GF := GF) (hG := hG))
    (wp_Append : ringBuffer.Append.spec (GF := GF) (hG := hG)) :
    store.applyEventsLocked.spec (GF := GF) (hG := hG) := by
  have wp_Delete : btree.BTree.Delete.modelSpec (GF := GF) (hG := hG) := btree.BTree.Delete.modelSpec_of wp_Delete
  have wp_ReplaceOrInsert : btree.BTree.ReplaceOrInsert.modelSpec (GF := GF) (hG := hG) := btree.BTree.ReplaceOrInsert.modelSpec_of wp_ReplaceOrInsert
  intro s γ cap st evSl evs
  wp_start as ⟨#Hs, Hphys, %Hinv, #Hevs, % ⟨Hsorted, Habove⟩⟩
  iNamed Hs
  wp_auto
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hsl, %HlsLen, #Hev⟩
  ihave %HslLen := ownSlice_len _ _ _ $$ Hsl
  iunfold storeLockedPhys at Hphys
  icases Hphys with ⟨HlatestRev, Hhist, Htr⟩
  iunfold storeLatestTree at Htr
  icases Htr with ⟨%t, Htree, Hbt, #HkvsAt⟩
  ihave HI : iprop(∃ (j : w64) (stc : StoreState),
      "i" ∷ i_ptr ↦ j ∗
      "HlatestRev" ∷ storeLatestRevAddr s ↦ stc.latestRev ∗
      "Hhist" ∷ ownRingBuffer (storeHistAddr s) cap (snapIs (hG := hG)) Prod.fst stc.history ∗
      "Hbt" ∷ ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess stc.latest (DFrac.own 1) ∗
      "#HkvsAt" ∷ kvsAt stc.latest ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ evs.length⌝ ∗
      "%Hstc" ∷ ⌜StoreInv cap stc ∧
        applyEvents cap st evs = applyEvents cap stc (evs.drop (sint.nat j)) ∧
        (∀ e ∈ evs.drop (sint.nat j), sint.Z stc.latestRev < sint.Z e.rev) ∧
        sint.Z st.latestRev ≤ sint.Z stc.latestRev⌝) $$ [i HlatestRev Hhist Hbt]
  · iexists W64 0, st
    simp only [named]
    iframe
    isplitl []
    · iexact HkvsAt
    ipureintro
    have H0 : sint.nat (W64 0) = 0 := by word
    rw [H0, List.drop_zero]
    exact ⟨⟨by word, by omega⟩, Hinv, rfl, Habove, Int.le_refl _⟩
  iclear HkvsAt
  wp_for HI
  wp_if_destruct
  · -- a batch starts at `j`
    have Hlt : sint.Z j < sint.Z evSl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hjl : sint.nat j < evs.length := by word
    simp only [Hj.1, Hlt, _root_.and_self, ↓reduceIte]
    list_elem ls (sint.nat j) as evp
    list_elem evs (sint.nat j) as e0
    wp_apply wp_load_slice_index evSl (sint.Z j) ls DFrac.discard evp Hj.1 $$ [] as -
    · iframe Hsl; ipureintro; exact Hevp_lookup
    ihave He0 := Hev $$ %(sint.nat j) %evp %e0 %Hevp_lookup %He0_lookup
    iunfold eventAt at He0
    icases He0 with ⟨%keySl, #Htyp, #Hkv, #Hkey, #Hks, #Hmod⟩
    wp_auto
    have He0j : evs[sint.nat j] = e0 := by
      rw [List.getElem?_eq_some_iff] at He0_lookup; exact He0_lookup.2
    have Hdrop : evs.drop (sint.nat j) = e0 :: evs.drop (sint.nat j + 1) := by
      rw [List.drop_eq_getElem_cons Hjl, He0j]
    ihave HJ : iprop(∃ (k : w64) (m : KvMap),
        "i" ∷ i_ptr ↦ k ∗
        "Hbt" ∷ ownBTree kvItemPtrT t (kvItemIs (hG := hG)) kvLess m (DFrac.own 1) ∗
        "#HkvsAtm" ∷ kvsAt m ∗
        "%Hk" ∷ ⌜sint.nat j ≤ sint.nat k ∧ sint.nat k ≤ evs.length ∧ 0 ≤ sint.Z k⌝ ∗
        "%Hm" ∷ ⌜applyBatch stc.latest
            ((evs.drop (sint.nat j)).take (sint.nat k - sint.nat j)) = (m, true) ∧
          (∀ (n : Nat) (e : EvModel), sint.nat j ≤ n → n < sint.nat k → evs[n]? = some e →
            e.rev = e0.rev) ∧
          m.Pairwise kvLess⌝) $$ [i Hbt]
    · iexists j, stc.latest
      simp only [named]
      iframe
      isplitl []
      · iexact HkvsAt
      ipureintro
      refine ⟨⟨Nat.le_refl _, by omega, Hj.1⟩, by simp [applyBatch], fun n e h1 h2 => by omega,
        Hstc.1.latest_sorted⟩
    wp_for HJ
    wp_if_destruct
    · -- `k < len(events)`: compare the revision
      have Hklt : sint.Z k < sint.Z evSl.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have Hkl : sint.nat k < evs.length := by word
      simp only [Hk.2.2, Hklt, _root_.and_self, ↓reduceIte]
      list_elem ls (sint.nat k) as evp1
      list_elem evs (sint.nat k) as e1
      wp_apply wp_load_slice_index evSl (sint.Z k) ls DFrac.discard evp1 Hk.2.2 $$ [] as -
      · iframe Hsl; ipureintro; exact Hevp1_lookup
      ihave He1 := Hev $$ %(sint.nat k) %evp1 %e1 %Hevp1_lookup %He1_lookup
      iunfold eventAt at He1
      icases He1 with ⟨%keySl1, #Htyp1, #Hkv1, #Hkey1, #Hks1, #Hmod1⟩
      wp_auto
      rw [if_decide_bool_eq_true]
      by_cases hr : e1.rev = e0.rev
      · -- event `k` is in the batch
        simp only [hr, decide_true, ↓reduceIte]
        wp_auto
        simp only [Hk.2.2, Hklt, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index evSl (sint.Z k) ls DFrac.discard evp1 Hk.2.2 $$ [] as -
        · iframe Hsl; ipureintro; exact Hevp1_lookup
        have Hrev1 : e1.rev = e0.rev := hr
        wp_if_destruct
        · -- delete
          wp_apply wp_bytes_to_string keySl1 e1.key DFrac.discard $$ [] as -
          · iexact Hks1
          ipersist «$a0»
          ihave #Hprobe : kvItemIs (hG := hG) «$a0_ptr» (e1.key, null) $$ [«$a0»]
          · iunfold kvItemIs; iexact «$a0»
          wp_apply wp_Delete kvItemPtrT t (kvItemIs (hG := hG)) kvLess m «$a0_ptr» (e1.key, null) $$ [Hbt]
            as %old %ok ⟨Hbt, Hold⟩
          · iframe Hbt Hprobe; ipureintro; exact kvLess_swo
          cases Hf : btFind kvLess (e1.key, null) m with
          | none =>
            -- a delete of a missing key: the error
            icases Hold with % ⟨Hok, -⟩
            subst Hok
            wp_auto
            wp_apply wp_bytes_to_string keySl1 e1.key DFrac.discard $$ [] as -
            · iexact Hks1
            wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #e1.key]
            isplitr
            · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            wp_apply fmt.wp_Errorf $$ [$Hasl] as %err _
            wp_for_post
            wp_for_post
            have Happ : applyEvents cap st evs = ({ stc with latest := m }, false) := by
              rw [Hstc.2.1, applyEventsLocked_split evs Hk.1,
                applyEventsLocked_drop_cons He1_lookup]
              apply applyEventsLocked_fail cap stc _ _ e0 e1
              · rw [← applyEventsLocked_drop_cons He1_lookup, ← applyEventsLocked_split evs Hk.1,
                  Hdrop]; rfl
              · intro x hx
                obtain ⟨n, h1, h2, h3⟩ := applyEventsLocked_mem_take hx
                exact Hm.2.1 n x h1 h2 h3
              · exact Hrev1
              · exact Hm.1
              · simp [applyEv, Hif, Hf]
            rw [applyEventsLocked_btDelete_of_find_none Hf]
            iapply HΦ
            rw [Happ]
            iunfold storeLockedPhys
            iunfold storeLatestTree
            iframe HlatestRev Hhist
            isplitl [Htree Hbt]
            · iexists t; iframe; iexact HkvsAtm
            ipureintro
            exact ⟨⟨applyEventsLocked_inv_latest Hstc.1 Hm.2.2, Hstc.2.2.2⟩, ⟨err, rfl⟩⟩
          | some w =>
            -- the key was there: it is deleted
            icases Hold with ⟨%Hok, -⟩
            subst Hok
            wp_auto
            wp_for_post
            iframe
            have Hev1 : applyEv m e1 = some (btDelete kvLess (e1.key, null) m) := by
              simp [applyEv, Hif, Hf]
            iexists k + W64 1, btDelete kvLess (e1.key, null) m
            simp only [named]
            iframe
            isplitl []
            · iapply applyEventsLocked_kvsAt_sub (fun x hx => btDelete_mem hx); iexact HkvsAtm
            ipureintro
            rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
            exact ⟨⟨by omega, by omega, by word⟩,
              applyEventsLocked_inner_inv Hk.1 He1_lookup Hrev1 Hm Hev1 (btDelete_sorted Hm.2.2)⟩
        · rename ¬e1.typ = W32 1 => Hnd
          wp_if_destruct
          · -- put
            ihave #HkvAt : kvAt (hG := hG) (e1.key, e1.kv) $$ []
            · iunfold kvAt; iexists keySl1; iframe Hkey1 Hks1
            wp_apply wp_newKVItem (e1.key, e1.kv) $$ [] as %p #Hp
            · iexact HkvAt
            wp_apply wp_ReplaceOrInsert kvItemPtrT t (kvItemIs (hG := hG)) kvLess m p
              (e1.key, e1.kv) $$ [Hbt] as %old %ok ⟨Hbt, -⟩
            · iframe Hbt Hp; ipureintro; exact kvLess_swo
            wp_for_post
            iframe
            have Hev1 : applyEv m e1 = some (btInsert kvLess (e1.key, e1.kv) m) := by
              simp [applyEv, Hif]
            iexists k + W64 1, btInsert kvLess (e1.key, e1.kv) m
            simp only [named]
            iframe
            isplitl []
            · iapply applyEventsLocked_kvsAt_insert; iframe HkvsAtm HkvAt
            ipureintro
            rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
            exact ⟨⟨by omega, by omega, by word⟩, applyEventsLocked_inner_inv Hk.1 He1_lookup Hrev1
              Hm Hev1 (btInsert_sorted kvLess_swo Hm.2.2)⟩
          · -- another event type: nothing
            wp_for_post
            iframe
            have Hev1 : applyEv m e1 = some m := by
              simp only [applyEv, Hnd, Hif, ↓reduceIte]
            iexists k + W64 1, m
            simp only [named]
            iframe
            isplitl []
            · iexact HkvsAtm
            ipureintro
            rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
            exact ⟨⟨by omega, by omega, by word⟩,
              applyEventsLocked_inner_inv Hk.1 He1_lookup Hrev1 Hm Hev1 Hm.2.2⟩
      · -- event `k` starts the next batch: the batch is done
        simp only [hr, decide_false, decide_true, ↓reduceIte, Bool.false_eq_true]
        have Hjk : sint.nat j < sint.nat k := by
          rcases Nat.lt_or_ge (sint.nat j) (sint.nat k) with h | h
          · exact h
          · exfalso
            have hjk : sint.nat k = sint.nat j := by omega
            rw [hjk, He0_lookup] at He1_lookup
            cases He1_lookup
            exact hr rfl
        have hexit : ∀ y, evs[sint.nat k]? = some y → y.rev ≠ e0.rev := by
          intro y hy
          rw [He1_lookup] at hy; cases hy
          exact hr
        wp_auto
        obtain ⟨Habove', Hinv', Happ', Hgt', Hmono'⟩ :=
          applyEventsLocked_batch_done Hsorted He0_lookup Hjk Hk.2.1 Hm hexit Hstc
        wp_apply wp_newClonedSnapshot e0.rev t m $$ [Hbt] as %p ⟨Hbt, #Hsnap⟩
        · iframe Hbt; iframe HkvsAtm; ipureintro; exact Hm.2.2
        wp_apply wp_Append (go.GoType.PointerType snapshot.ty) (storeHistAddr s) cap
          (snapIs (hG := hG)) Prod.fst stc.history p (e0.rev, m) $$ [Hhist] as Hhist
        · iframe Hhist Hsnap; ipureintro; exact Habove'
        wp_apply sync.Cond.wp_Broadcast c lk $$ []
        · iexact Hcond
        wp_for_post
        iframe
        iexists k, StoreState.mk e0.rev m (ringAppend cap stc.history (e0.rev, m))
        simp only [named]
        iframe
        isplitl []
        · iexact HkvsAtm
        ipureintro
        exact ⟨⟨Hk.2.2, Hk.2.1⟩, Hinv', Happ', Hgt', Hmono'⟩
    · -- `k = len(events)`: the batch is done
      have Hkle : sint.nat k = evs.length := by word
      have Hjk : sint.nat j < sint.nat k := by
        rcases Nat.lt_or_ge (sint.nat j) (sint.nat k) with h | h
        · exact h
        · omega
      have hexit : ∀ y, evs[sint.nat k]? = some y → y.rev ≠ e0.rev := by
        intro y hy; rw [Hkle] at hy; simp at hy
      obtain ⟨Habove', Hinv', Happ', Hgt', Hmono'⟩ :=
        applyEventsLocked_batch_done Hsorted He0_lookup Hjk Hk.2.1 Hm hexit Hstc
      wp_apply wp_newClonedSnapshot e0.rev t m $$ [Hbt] as %p ⟨Hbt, #Hsnap⟩
      · iframe Hbt; iframe HkvsAtm; ipureintro; exact Hm.2.2
      wp_apply wp_Append (go.GoType.PointerType snapshot.ty) (storeHistAddr s) cap
        (snapIs (hG := hG)) Prod.fst stc.history p (e0.rev, m) $$ [Hhist] as Hhist
      · iframe Hhist Hsnap; ipureintro; exact Habove'
      wp_apply sync.Cond.wp_Broadcast c lk $$ []
      · iexact Hcond
      wp_for_post
      iframe
      iexists k, StoreState.mk e0.rev m (ringAppend cap stc.history (e0.rev, m))
      simp only [named]
      iframe
      isplitl []
      · iexact HkvsAtm
      ipureintro
      exact ⟨⟨Hk.2.2, Hk.2.1⟩, Hinv', Happ', Hgt', Hmono'⟩
  · -- all events applied
    have Hje : sint.nat j = evs.length := by word
    obtain ⟨Hinvc, Happ, -, Hmono⟩ := Hstc
    rw [Hje, List.drop_length, applyEvents.eq_1] at Happ
    iapply HΦ
    rw [Happ]
    iunfold storeLockedPhys
    iunfold storeLatestTree
    isplitl [HlatestRev Hhist Htree Hbt]
    · iframe HlatestRev Hhist; iexists t; iframe Htree Hbt; iexact HkvsAt
    ipureintro
    exact ⟨⟨Hinvc, Hmono⟩, rfl⟩

end proof


end EtcdGrove
end Perennial
