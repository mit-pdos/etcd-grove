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

/-- **B4's `hpres`: a unary step keeps `RunOk`**, with room under `2^63`, moving the revision by at most one. -/
theorem kstepL_runOk (x : Input) (h : HSt) (hrun : RunOk h) (hr : uint.nat h.st.rv + 1 < 2 ^ 63)
    (hx : OpFits x) :
    RunOk (kstepL x h).1 ∧ uint.nat (kstepL x h).1.st.rv ≤ uint.nat h.st.rv + 1 := by
  unfold kstepL
  split
  · exact ⟨hrun, Nat.le_succ _⟩
  obtain ⟨hcfg, hhc, hsort, hrvb⟩ := hrun
  have hg : StGood h.st := ⟨hcfg.1, hcfg.2.1, fun it hit => hcfg.2.2.1.1 _ _ (by
    show (GMap.ofList (h.st.items.map fun it => (storeKeyL it.key', it.obj'))) !! storeKeyL it.key' = _
    rw [ofList_items, fI_mem _ hcfg.1.1 it hit]; rfl)⟩
  obtain ⟨hg', hc⟩ := mstepL_ok x h.st hg hr hx
  generalize (mstepL x h.st).1 = st' at hg' hc
  rcases hc with rfl | hc
  · have : advanceL h h.st = h := by unfold advanceL; rw [if_neg (fun e => e rfl)]
    rw [this]; exact ⟨⟨hcfg, hhc, hsort, hrvb⟩, Nat.le_succ _⟩
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
    ⟨by simp; omega, by simp, fun q hq0 hq => ?_⟩, fun r hr' => ?_, by dsimp only; omega⟩, by omega⟩
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
    · have e : histN (h.hist ++ [st']) r = histN h.hist r := by
        unfold histN; rw [List.take_append_of_le_length hle]
      rw [e]; exact hsort r hle
    · have e : histN (h.hist ++ [st']) r = st' := by
        unfold histN; rw [List.take_of_length_le (by simp; omega)]; simp
      rw [e]; exact hg'.1.1

end go

end k8s_correctness
end EtcdGrove
end Perennial
