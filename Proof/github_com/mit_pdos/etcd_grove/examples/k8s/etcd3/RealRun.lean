/-
Lean-first (no Rocq counterpart).

# The bridge's run premises: a unary step keeps `RunOk` (k8s 7g step 5)

`notes/k8s-7g-scope.md` §2.3; B4's premise `hpres` (`RealB4.realReplay_ok`): along the driver's run, each unary step
(`kstepL`) keeps the configuration `RunOk`, with room left under `2^63`, and moves the revision by at most one.

- `OpFits x`: the input's fields fit an object (`crFits`) and its value is short;
- `rmWf_absR`: a store whose objects' revisions are at most its own abstracts to a well-formed model;
- `mstepL_ok`: the model's step keeps a store sorted, unannotated, its objects `itemOk` and at most its revision;
- **`kstepL_runOk`** (B4's `hpres`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealB4

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- **What a unary input needs for its step to keep `RunOk`**: its fields fit an object (`crFits`, as `Create`
needs) and its value is short (`call`'s premise bounds it by `2^20`). -/
def OpFits (x : Input) : Prop := crFits x ∧ x.Val'.length < 2 ^ 62

theorem ofList_lookup_mem {V : Type} (l : List (GoString × V)) (k : GoString) (v : V)
    (h : GMap.ofList l !! k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => change ((∅ : GMap GoString V) !! k) = some v at h; simp at h
  | cons a l ih =>
    obtain ⟨k', v'⟩ := a
    change (<[k' := v']> (GMap.ofList l) !! k) = some v at h
    rw [GMap.lookup_insert_eq_iff] at h
    by_cases e : k' = k
    · subst e; simp only [if_true, Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · simp only [e, if_false] at h; exact List.mem_cons_of_mem _ (ih h)

/-- **A store whose objects' revisions are at most its own abstracts to a well-formed model.** -/
theorem rmWf_absR (st : GSt) (h : ∀ it ∈ st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat st.rv) :
    rmWf (absR st) := by
  refine ⟨fun k o hk => ?_, fun k hk => ?_⟩
  · have hm := ofList_lookup_mem _ k o hk
    obtain ⟨it, hit, e⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact h it hit
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hk
    have hm := ofList_lookup_mem _ k b hb
    obtain ⟨it, hit, e⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, -⟩ := e
    have hit' := (List.mem_filter.1 hit).1
    show (GMap.ofList (st.items.map fun it => (storeKeyL it.key', it.obj')) !! storeKeyL it.key').isSome
    rw [ofList_isSome]
    exact List.mem_map.2 ⟨_, List.mem_map_of_mem hit', rfl⟩

theorem encodeWith_length (v : Obj) : (encodeWith tagV1 v).length =
    8 + v.Namespace'.length + v.Name'.length + v.UID'.length + v.Node'.length + v.App'.length +
      v.Value'.length := by
  simp [encodeWith, putF]; omega

theorem itemOk_of (o : Obj) (hf : fitsD o) (ha : o.Annotated' = false) (hv : o.Value'.length < 2 ^ 62) :
    itemOk o := by
  refine ⟨hf, ha, ?_⟩
  rw [encodeWith_length]; obtain ⟨h1, h2, h3, h4, h5⟩ := hf; omega

/-- `itemOk` does not read the resource version. -/
theorem itemOk_rv (o : Obj) (r : w64) (h : itemOk o) : itemOk { o with ResourceVersion' := r } := h

theorem lookupL_mem' (its : List item) (n : GoString) (h : (lookupL its n).2 = true) :
    (lookupL its n).1 ∈ its := by
  rw [lookupL_fI] at h ⊢
  cases e : fI its n with
  | none => rw [e] at h; cases h
  | some it => exact List.mem_of_find?_eq_some e

/-- What `mstepL` keeps of a store. -/
def StGood (st : GSt) : Prop :=
  StOk st ∧ (∀ it ∈ st.items, itemOk it.obj') ∧
    ∀ it ∈ st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat st.rv

theorem rv_succ (r : w64) (h : uint.nat r + 1 < 2 ^ 63) : uint.nat (r + W64 1) = uint.nat r + 1 := by
  word

/-- A store with a new item `it` set (at a revision above every object's). -/
theorem stGood_set (st : GSt) (it : item) (hg : StGood st) (hr : uint.nat st.rv + 1 < 2 ^ 63)
    (hok : itemOk it.obj') (hrv : it.obj'.ResourceVersion' = st.rv + W64 1) :
    StGood ⟨setItemL st.items it, st.rv + W64 1⟩ := by
  obtain ⟨⟨hs, ha⟩, hi, hv⟩ := hg
  have hm : ∀ e ∈ setItemL st.items it, e = it ∨ e ∈ st.items := fun e he => by
    rw [setItemL_eq _ _ hs] at he; exact mem_setRI _ _ _ he
  refine ⟨⟨sortedI_setItemL _ _ hs, fun e he => ?_⟩, fun e he => ?_, fun e he => ?_⟩
  · rcases hm e he with rfl | he
    · exact hok.2.1
    · exact ha e he
  · rcases hm e he with rfl | he
    · exact hok
    · exact hi e he
  · show _ ≤ uint.nat (st.rv + W64 1)
    rw [rv_succ _ hr]
    rcases hm e he with rfl | he
    · rw [hrv, rv_succ _ hr]; exact Nat.le_refl _
    · have := hv e he; omega

/-- A store with the key `k` deleted. -/
theorem stGood_del (st : GSt) (k : GoString) (hg : StGood st) (hr : uint.nat st.rv + 1 < 2 ^ 63) :
    StGood ⟨delItemL st.items k, st.rv + W64 1⟩ := by
  obtain ⟨⟨hs, ha⟩, hi, hv⟩ := hg
  have hm : ∀ e ∈ delItemL st.items k, e ∈ st.items := fun e he => (List.mem_filter.1 he).1
  refine ⟨⟨sortedI_delItemL _ _ hs, fun e he => ha e (hm e he)⟩, fun e he => hi e (hm e he), fun e he => ?_⟩
  show _ ≤ uint.nat (st.rv + W64 1)
  rw [rv_succ _ hr]; have := hv e (hm e he); omega

theorem zObj_itemOk : itemOk zObj := itemOk_of zObj (by unfold fitsD zObj; simp) rfl (by simp [zObj])

/-- **The model's step keeps a store good**, and leaves it or moves its revision by one. -/
theorem mstepL_ok (x : Input) (st : GSt) (hg : StGood st) (hr : uint.nat st.rv + 1 < 2 ^ 63)
    (hx : OpFits x) :
    StGood (mstepL x st).1 ∧ ((mstepL x st).1 = st ∨ (mstepL x st).1.rv = st.rv + W64 1) := by
  have hcur : ∀ b : Bool, b = (lookupL st.items x.Key').2 →
      itemOk (if b then (lookupL st.items x.Key').1.obj' else zObj) := by
    intro b hb
    cases b
    · exact zObj_itemOk
    · exact hg.2.1 _ (lookupL_mem' _ _ hb.symm)
  unfold mstepL
  split
  · unfold mcreateL
    split
    · exact ⟨hg, Or.inl rfl⟩
    · refine ⟨stGood_set st _ hg hr ?_ rfl, Or.inr rfl⟩
      exact itemOk_of _ (crFits_fitsD x hx.1 _) rfl hx.2
  split
  · unfold mdeleteL; dsimp only
    split
    · exact ⟨hg, Or.inl rfl⟩
    split
    · exact ⟨hg, Or.inl rfl⟩
    split
    · exact ⟨hg, Or.inl rfl⟩
    · exact ⟨stGood_del st _ hg hr, Or.inr rfl⟩
  split
  · unfold mupdateL; dsimp only
    have hc := hcur _ rfl
    generalize (if (lookupL st.items x.Key').2 = true then (lookupL st.items x.Key').1.obj' else zObj) = cur
      at hc ⊢
    split
    · exact ⟨hg, Or.inl rfl⟩
    split
    · exact ⟨hg, Or.inl rfl⟩
    split
    · exact ⟨hg, Or.inl rfl⟩
    split
    · exact ⟨hg, Or.inl rfl⟩
    · refine ⟨stGood_set st _ hg hr ?_ (by simp), Or.inr rfl⟩
      apply itemOk_rv
      show itemOk (updGo x cur)
      by_cases hn : x.NoOp' = true
      · have e : updGo x cur = cur := by simp [updGo, hn]
        rw [e]; exact hc
      · have hf := updGo_fitsD x cur hc.1 ⟨hx.1.1, hx.1.2.2.1, hx.1.2.2.2⟩
        have hv : (updGo x cur).Value' = x.Val' := by simp [updGo, hn]
        exact itemOk_of _ hf ((updGo_annotated x _).trans hc.2.1) (by rw [hv]; exact hx.2)
  · exact ⟨hg, Or.inl rfl⟩

/-! ## `HistGood` along the run -/

theorem fI_eq_of_lookupL {a b : List item} {k : GoString} (h : lookupL a k = lookupL b k) :
    fI a k = fI b k := by
  rw [lookupL_fI, lookupL_fI] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  cases ha : fI a k <;> cases hb : fI b k <;> simp_all

theorem fI_setItemL (its : List item) (it : item) (hs : SortedI its) (k : GoString) :
    fI (setItemL its it) k = if it.key' = k then some it else fI its k := by
  have h := lookupL_setItemL its it hs k
  by_cases e : it.key' = k
  · rw [if_pos e] at h; rw [if_pos e]
    rw [lookupL_fI] at h
    simp only [Prod.mk.injEq] at h
    cases hf : fI (setItemL its it) k <;> simp_all
  · rw [if_neg e] at h; rw [if_neg e]; exact fI_eq_of_lookupL h

theorem fI_delItemL (its : List item) (k k' : GoString) :
    fI (delItemL its k) k' = if k = k' then none else fI its k' := by
  have h := lookupL_delItemL its k k'
  by_cases e : k = k'
  · rw [if_pos e] at h; rw [if_pos e]
    rw [lookupL_fI] at h
    simp only [Prod.mk.injEq] at h
    cases hf : fI (delItemL its k) k' <;> simp_all
  · rw [if_neg e] at h; rw [if_neg e]; exact fI_eq_of_lookupL h

/-- **A write changes one name**, whose new item (if any) is at the new revision. -/
theorem mstepL_one (x : Input) (st : GSt) (hs : SortedI st.items) :
    (mstepL x st).1 = st ∨ ∃ n, (∀ k, k ≠ n → fI (mstepL x st).1.items k = fI st.items k) ∧
      ∀ it, fI (mstepL x st).1.items n = some it → it.obj'.ResourceVersion' = (mstepL x st).1.rv := by
  have hset : ∀ (it : item), it.obj'.ResourceVersion' = st.rv + W64 1 →
      ∃ n, (∀ k, k ≠ n → fI (setItemL st.items it) k = fI st.items k) ∧
        ∀ it', fI (setItemL st.items it) n = some it' → it'.obj'.ResourceVersion' = st.rv + W64 1 := by
    intro it hrv
    refine ⟨it.key', fun k hk => ?_, fun it' h => ?_⟩
    · rw [fI_setItemL _ _ hs, if_neg (Ne.symm hk)]
    · rw [fI_setItemL _ _ hs, if_pos rfl] at h; cases h; exact hrv
  unfold mstepL
  split
  · unfold mcreateL
    split
    · exact Or.inl rfl
    · exact Or.inr (hset _ (by rfl))
  split
  · unfold mdeleteL; dsimp only
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    · refine Or.inr ⟨x.Key', fun k hk => ?_, fun it h => ?_⟩
      · rw [fI_delItemL, if_neg (Ne.symm hk)]
      · rw [fI_delItemL, if_pos rfl] at h; cases h
  split
  · unfold mupdateL; dsimp only
    generalize (if (lookupL st.items x.Key').2 = true then (lookupL st.items x.Key').1.obj' else zObj) = cur
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    · exact Or.inr (hset _ (by rfl))
  · exact Or.inl rfl

/-- **`HistGood` of a history grown by a store** that changes one name of the last store, its new item at
the new revision. -/
theorem histGood_snoc (hs : List GSt) (st st' : GSt) (n : GoString) (hg : HistGood hs)
    (hlast : hs.getLast? = some st) (hst : StOk st) (hst' : StGood st')
    (hrv' : uint.nat st'.rv = hs.length + 1)
    (hone : ∀ k, k ≠ n → fI st'.items k = fI st.items k)
    (hnew : ∀ it, fI st'.items n = some it → it.obj'.ResourceVersion' = st'.rv) :
    HistGood (hs ++ [st']) := by
  have hN : k8s_etcd3.histN hs hs.length = st := histN_last hs st hlast
  have hN' : k8s_etcd3.histN (hs ++ [st']) (hs.length + 1) = st' := by
    unfold k8s_etcd3.histN; rw [List.take_of_length_le (by simp)]; simp
  have hold : ∀ it ∈ st.items, 1 ≤ uint.nat it.obj'.ResourceVersion' ∧
      uint.nat it.obj'.ResourceVersion' ≤ hs.length ∧ it.obj'.Annotated' = false := by
    intro it hit; exact hg.1 hs.length it (Nat.le_refl _) (hN ▸ hit)
  refine ⟨fun r it hr hit => ?_, fun r ch h2 hr hch => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hr
    by_cases hle : r ≤ hs.length
    · rw [histN_append_le _ _ _ hle] at hit; exact hg.1 r it hle hit
    · have hr1 : r = hs.length + 1 := by omega
      subst hr1
      rw [hN'] at hit
      have hf : fI st'.items it.key' = some it := by
        have := lookupL_mem _ hst'.1.1 it hit
        rw [lookupL_fI] at this
        simp only [Prod.mk.injEq] at this
        cases e : fI st'.items it.key' <;> simp_all
      refine ⟨?_, ?_, hst'.1.2 it hit⟩
      · by_cases hk : it.key' = n
        · rw [hk] at hf; rw [hnew it hf, hrv']; omega
        · rw [hone _ hk] at hf
          exact (hold it (List.mem_of_find?_eq_some hf)).1
      · have := hst'.2.2 it hit; omega
  · simp only [List.length_append, List.length_singleton] at hr
    by_cases hle : r ≤ hs.length
    · rw [histN_append_le _ _ _ hle, histN_append_le _ _ _ (by omega)] at hch
      exact hg.2 r ch h2 hle hch
    · have hr1 : r = hs.length + 1 := by omega
      subst hr1
      rw [hN', show hs.length + 1 - 1 = hs.length from rfl, histN_append_le _ _ _ (Nat.le_refl _), hN] at hch
      rw [changeAtL_one n _ st.items st'.items hst.1 hst'.1.1 (fun k hk => (hone k hk).symm)] at hch
      unfold chgL at hch
      split at hch
      · cases hch
      · rename_i p hp _
        simp only [Option.some.injEq] at hch; subst hch
        refine ⟨fun o ho => (by cases ho), fun o ho => ?_⟩
        simp only [Option.some.injEq] at ho; subst ho
        exact hst.2 p (List.mem_of_find?_eq_some hp)
      · rename_i q _ hq
        simp only [Option.some.injEq] at hch; subst hch
        refine ⟨fun o ho => ?_, fun o ho => by cases ho⟩
        simp only [Option.some.injEq] at ho; subst ho
        exact ⟨by rw [hnew q hq, hrv'], hst'.1.2 q (List.mem_of_find?_eq_some hq)⟩
      · rename_i p q hp hq
        split at hch
        · cases hch
        simp only [Option.some.injEq] at hch; subst hch
        refine ⟨fun o ho => ?_, fun o ho => ?_⟩
        · simp only [Option.some.injEq] at ho; subst ho
          exact ⟨by rw [hnew q hq, hrv'], hst'.1.2 q (List.mem_of_find?_eq_some hq)⟩
        · simp only [Option.some.injEq] at ho; subst ho
          exact hst.2 p (List.mem_of_find?_eq_some hp)

/-- **B5's `HistWf`, for any watch**, from `HistGood` and a history shorter than `2^63`. -/
theorem histWf_of_histGood (x : Input) (hs : List GSt) (hg : HistGood hs) (hlen : hs.length < 2 ^ 63) :
    HistWf x hs := by
  refine ⟨hlen, hg.1, fun r e he => ?_⟩
  unfold evAtL at he
  split at he
  · rename_i h2
    cases hch : changeAtL (k8s_etcd3.histN hs (r - 1)).items (k8s_etcd3.histN hs r).items r with
    | none => rw [hch] at he; cases he
    | some ch =>
      rw [hch] at he
      simp only [Option.bind_some] at he
      have hr : r ≤ hs.length := by
        refine Classical.byContradiction fun hgt => ?_
        have e1 : k8s_etcd3.histN hs (r - 1) = k8s_etcd3.histN hs r := by
          unfold k8s_etcd3.histN; rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [e1, changeAtL_self] at hch; cases hch
      obtain ⟨hcur, hprev⟩ := hg.2 r ch h2 hr hch
      split at he
      · unfold toEventL at he
        simp only at he
        split at he
        · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 he; exact hcur o ho
        split at he
        · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 he; exact hcur o ho
        split at he
        · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 he
          exact ⟨by rw [changeAtL_rv _ _ _ _ hch]; exact W64_nat r (by omega), hprev o ho⟩
        · cases he
      · cases he
  · cases he

/-- **B4's `hpres`: a unary step keeps `RunOk`**, with room under `2^63`, moving the revision by at most one. -/
theorem kstepL_runOk (x : Input) (h : HSt) (hrun : RunOk h) (hr : uint.nat h.st.rv + 1 < 2 ^ 63)
    (hx : OpFits x) :
    RunOk (kstepL x h).1 ∧ uint.nat (kstepL x h).1.st.rv ≤ uint.nat h.st.rv + 1 := by
  unfold kstepL
  split
  · exact ⟨hrun, Nat.le_succ _⟩
  obtain ⟨hcfg, hhc, hsort, hgood, hrvb⟩ := hrun
  have hg : StGood h.st := ⟨hcfg.1, hcfg.2.1, fun it hit => hcfg.2.2.1.1 _ _ (by
    show (GMap.ofList (h.st.items.map fun it => (storeKeyL it.key', it.obj'))) !! storeKeyL it.key' = _
    rw [ofList_items, fI_mem _ hcfg.1.1 it hit]; rfl)⟩
  obtain ⟨hg', hc⟩ := mstepL_ok x h.st hg hr hx
  have hone := mstepL_one x h.st hcfg.1.1
  generalize (mstepL x h.st).1 = st' at hg' hc hone
  rcases hc with rfl | hc
  · have : advanceL h h.st = h := by unfold advanceL; rw [if_neg (fun e => e rfl)]
    rw [this]; exact ⟨⟨hcfg, hhc, hsort, hgood, hrvb⟩, Nat.le_succ _⟩
  have hne : st'.rv ≠ h.st.rv := by rw [hc]; intro e; have := congrArg (fun r => uint.nat r) e; simp at this; word
  have ha : advanceL h st' = ⟨st', h.hist ++ [st']⟩ := by unfold advanceL; rw [if_pos hne]
  rw [ha]
  show RunOk ⟨st', h.hist ++ [st']⟩ ∧ uint.nat st'.rv ≤ uint.nat h.st.rv + 1
  have hrv' : uint.nat st'.rv = uint.nat h.st.rv + 1 := by rw [hc]; exact rv_succ _ hr
  have hlen := hhc.1
  have hat : ∀ q : w64, uint.nat q ≤ uint.nat st'.rv → uint.nat h.st.rv < uint.nat q →
      histAtL (h.hist ++ [st']) q = st' := fun q _ hq => histAtL_snoc_gt _ _ _ (by omega)
  have hold : ∀ q : w64, uint.nat q ≤ uint.nat h.st.rv →
      histAtL (h.hist ++ [st']) q = histAtL h.hist q := fun q hq => histAtL_snoc_le _ _ _ (by omega)
  refine ⟨⟨⟨hg'.1, hg'.2.1, rmWf_absR _ hg'.2.2, by dsimp only; omega, fun q hq0 hq => ?_⟩,
    ⟨by simp; omega, by simp, fun q hq0 hq => ?_⟩, fun r hr' => ?_, ?_, by dsimp only; omega⟩, by omega⟩
  · dsimp only at hq ⊢
    by_cases hle : uint.nat q ≤ uint.nat h.st.rv
    · rw [hold q hle]; exact hcfg.2.2.2.2 q hq0 hle
    · rw [hat q hq (by omega)]
      have : uint.nat q = uint.nat st'.rv := by omega
      word
  · dsimp only at hq ⊢
    by_cases hle : uint.nat q ≤ uint.nat h.st.rv
    · rw [hold q hle]; exact hhc.2.2 q hq0 hle
    · rw [hat q hq (by omega)]; exact ⟨hg'.1, hg'.2.1⟩
  · simp only [List.length_append, List.length_singleton] at hr'
    by_cases hle : r ≤ h.hist.length
    · have e : k8s_etcd3.histN (h.hist ++ [st']) r = k8s_etcd3.histN h.hist r := by
        unfold k8s_etcd3.histN; rw [List.take_append_of_le_length hle]
      rw [e]; exact hsort r hle
    · have e : k8s_etcd3.histN (h.hist ++ [st']) r = st' := by
        unfold k8s_etcd3.histN; rw [List.take_of_length_le (by simp; omega)]; simp
      rw [e]; exact hg'.1.1
  · rcases hone with e | ⟨n, hn1, hn2⟩
    · exact absurd (congrArg GSt.rv e) hne
    exact histGood_snoc h.hist h.st st' n hgood hhc.2.1 hcfg.1 hg' (by omega) hn1 hn2

end go

end k8s_correctness
end EtcdGrove
end Perennial
