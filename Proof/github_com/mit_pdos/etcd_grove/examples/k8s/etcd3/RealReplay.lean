/-
Lean-first (no Rocq counterpart).

# The bridge to Kubernetes' checker, B3: the replay is determined by the responses (k8s 7g step 4)

`notes/k8s-7g-scope.md` §2.3, B3. Porcupine's second run over `correctness.Model` may pick another
linearization than the driver's (`kSpec`'s, projected on the unary operations); `NewReplay` then
runs along that one. Two facts make the checks after porcupine independent of the choice:

- **`replayL_perm`** (B3a): two linearizations of the same operations (`List.Perm`) that both
  replay give the same `RReplay`: the same state at every resource version and the same changes.
  Every write that moves the resource version answers its object at the new one (create, a writing
  update, delete); a write that does not (a no-op update, a failed one) leaves the state as it was.
  So the writes that move it come in the order of their responses' resource versions, and the
  state at each is a function of the operations. (Which of two updates with equal answers writes
  and which is the no-op can differ between linearizations; the states and changes cannot.)
- **`simR_step`** (B3b): along the driver's run, the replay's accumulator tracks the driver's
  configuration (`SimR`): its state is the configuration's store (`absR`), its states map holds
  `absR (histAtL hist r)` at every revision `r` from the seeded store's `s0` on, and its changes
  are the history's (`chgListL`). `ReplayAt s0 R h` is what the checks of a read or a watch at a
  configuration `h` use of the final replay `R` (B4, B5).

The premises on the states: `rmWf` (the stored objects' resource versions at most the state's, the
rewrite flags only on stored keys: `absR` of a seeded store satisfies it) and `HistSorted` (the
stores of the history keep their items in strictly increasing key order, as the store does).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.RReplay
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge

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

/-! ## Vocabulary -/

/-- **A well-formed model state**: every stored object's resource version is at most the state's,
and only stored keys carry a rewrite flag (`absR` of a seeded store; kept by every step). -/
def rmWf (m : RM) : Prop :=
  (∀ k o, m.items !! k = some o → uint.nat o.ResourceVersion' ≤ uint.nat m.rv) ∧
  (∀ k, (m.rewrites !! k).isSome → (m.items !! k).isSome)

/-- **The stores of a history keep their items in strictly increasing key order** (the store's
`setItem`; read off `KRelH`). -/
def HistSorted (hs : List GSt) : Prop :=
  ∀ r ≤ hs.length, ((histN hs r).items.map (·.key')).Pairwise go.GoStringLt

/-- **The changes of a history from revision `s0` on**, as the checker's `Change`s: for each
revision `r` in `(s0, |hs|]`, the item that differs between the stores at `r - 1` and `r`
(`changeAtL`), at its store key. -/
def chgListL (s0 : Nat) (hs : List GSt) : List RChange :=
  (List.range' (s0 + 1) (hs.length - s0)).filterMap fun r =>
    (changeAtL (histN hs (r - 1)).items (histN hs r).items r).map fun ch =>
      ⟨storeKeyL ch.key, W64 (r : Int), ch.cur, ch.prev⟩

/-- **The replay `R` agrees with the driver's configuration `h` up to its revision**: the state at
every resource version from `s0` to `h`'s is `h`'s store there, and the changes up to `h`'s
revision are its history's. -/
def ReplayAt (s0 : w64) (R : RReplay) (h : HSt) : Prop :=
  (∀ r : w64, uint.nat s0 ≤ uint.nat r → uint.nat r ≤ uint.nat h.st.rv →
    R.states !! r = some (absR (histAtL h.hist r))) ∧
  R.changes.filter (fun c => decide (uint.nat c.rv ≤ uint.nat h.st.rv)) =
    chgListL (uint.nat s0) h.hist

/-- **The replay's accumulator (state, states map, changes) tracks the configuration `h`**: the
state is `h`'s store, the states map is defined exactly from `s0` to `h`'s revision, every change
is at most `h`'s revision, `s0` is at most `h`'s revision, the state is well formed (`rmWf`), and
`ReplayAt`. -/
def SimR (s0 : w64) (acc : RM × GMap w64 RM × List RChange) (h : HSt) : Prop :=
  acc.1 = absR h.st ∧ uint.nat s0 ≤ uint.nat h.st.rv ∧ rmWf acc.1 ∧
  (∀ r : w64, (acc.2.1 !! r).isSome ↔ (uint.nat s0 ≤ uint.nat r ∧ uint.nat r ≤ uint.nat h.st.rv)) ∧
  (∀ c ∈ acc.2.2, uint.nat c.rv ≤ uint.nat h.st.rv) ∧
  ReplayAt s0 ⟨acc.2.1, acc.2.2⟩ h

/-! ## History facts -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem histN_append_le (l t : List GSt) (r : Nat) (h : r ≤ l.length) :
    histN (l ++ t) r = histN l r := by
  unfold histN; rw [List.take_append_of_le_length h]

theorem histAtL_append_le (l t : List GSt) (r : w64) (h : uint.nat r ≤ l.length) :
    histAtL (l ++ t) r = histAtL l r := by
  unfold histAtL; rw [List.take_append_of_le_length h]

theorem histAtL_last (hs : List GSt) (st : GSt) (r : w64) (hlen : hs.length = uint.nat r)
    (hlast : hs.getLast? = some st) : histAtL hs r = st := by
  unfold histAtL; rw [List.take_of_length_le (by omega), hlast]; rfl

theorem histN_last (hs : List GSt) (st : GSt) (hlast : hs.getLast? = some st) :
    histN hs hs.length = st := by
  unfold histN; rw [List.take_length, hlast]; rfl

theorem W64_nat (r : Nat) (h : r < 2 ^ 64) : uint.nat (W64 (r : Int)) = r := by
  simp only [W64, BitVec.toNat_ofInt]; omega

/-- The changes of a longer history, up to the shorter one's length, are the shorter one's. -/
theorem chgListL_filter (s0 : Nat) (l t : List GSt) (hb : (l ++ t).length < 2 ^ 64) :
    (chgListL s0 (l ++ t)).filter (fun c => decide (uint.nat c.rv ≤ l.length)) = chgListL s0 l := by
  unfold chgListL
  rw [List.filter_filterMap]
  have hlt : (l ++ t).length = l.length + t.length := List.length_append
  by_cases hs : s0 ≤ l.length
  · have hr : List.range' (s0 + 1) ((l ++ t).length - s0) =
        List.range' (s0 + 1) (l.length - s0) ++ List.range' (l.length + 1) t.length := by
      rw [show l.length + 1 = s0 + 1 + 1 * (l.length - s0) by omega, List.range'_append]
      congr 1; omega
    rw [hr, List.filterMap_append]
    have h2 : (List.range' (l.length + 1) t.length).filterMap (fun r =>
        ((changeAtL (histN (l ++ t) (r - 1)).items (histN (l ++ t) r).items r).map fun ch =>
          (⟨storeKeyL ch.key, W64 (r : Int), ch.cur, ch.prev⟩ : RChange)).filter
          (fun c => decide (uint.nat c.rv ≤ l.length))) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro r hr
      rw [List.mem_range'_1] at hr
      cases changeAtL (histN (l ++ t) (r - 1)).items (histN (l ++ t) r).items r with
      | none => rfl
      | some ch =>
        simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
        rw [W64_nat r (by omega)]; simp; omega
    rw [h2, List.append_nil]
    apply filterMap_congr'
    intro r hr
    rw [List.mem_range'_1] at hr
    rw [histN_append_le l t r (by omega), histN_append_le l t (r - 1) (by omega)]
    cases changeAtL (histN l (r - 1)).items (histN l r).items r with
    | none => rfl
    | some ch =>
      simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
      rw [W64_nat r (by omega)]; simp; omega
  · have h0 : l.length - s0 = 0 := by omega
    rw [h0, List.range'_zero, List.filterMap_nil, List.filterMap_eq_nil_iff]
    intro r hr
    rw [List.mem_range'_1] at hr
    cases changeAtL (histN (l ++ t) (r - 1)).items (histN (l ++ t) r).items r with
    | none => rfl
    | some ch =>
      simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
      rw [W64_nat r (by omega)]; simp; omega

/-- The changes of a history one store longer: the last revision's change appended. -/
theorem chgListL_snoc (s0 : Nat) (l : List GSt) (st : GSt) (hs : s0 ≤ l.length) :
    chgListL s0 (l ++ [st]) = chgListL s0 l ++
      ((changeAtL (histN l l.length).items st.items (l.length + 1)).map fun ch =>
        (⟨storeKeyL ch.key, W64 ((l.length + 1 : Nat) : Int), ch.cur, ch.prev⟩ : RChange)).toList := by
  unfold chgListL
  have hr : List.range' (s0 + 1) ((l ++ [st]).length - s0) =
      List.range' (s0 + 1) (l.length - s0) ++ [l.length + 1] := by
    rw [show [l.length + 1] = List.range' (s0 + 1 + 1 * (l.length - s0)) 1 by
      simp only [List.range'_one]; congr 1; omega, List.range'_append]
    congr 1; simp; omega
  rw [hr, List.filterMap_append]
  congr 1
  · apply filterMap_congr'
    intro r hr
    rw [List.mem_range'_1] at hr
    rw [histN_append_le l [st] r (by omega), histN_append_le l [st] (r - 1) (by omega)]
  · have h1 : histN (l ++ [st]) (l.length + 1) = st := by
      have := histN_last (l ++ [st]) st (by simp)
      simpa using this
    simp only [List.filterMap_cons, List.filterMap_nil, Nat.add_sub_cancel, h1,
      histN_append_le l [st] l.length (Nat.le_refl _)]
    cases changeAtL (histN l l.length).items st.items (l.length + 1) <;> rfl

theorem kstepL_hist (x : Input) (h : HSt) :
    (kstepL x h).1.hist =
      if (kstepL x h).1.st.rv = h.st.rv then h.hist else h.hist ++ [(kstepL x h).1.st] := by
  unfold kstepL
  split
  · simp
  · unfold advanceL
    split <;> simp_all

/-! ## One model step -/

/-- An accepted `Step` moves to `execute`'s state with its change (a read: the state itself). -/
theorem rstepL_true (x : Input) (m : RM) (resp : RResp) (h : (rstepL x m resp).1 = true) :
    (rstepL x m resp).2 = (rexecL x m).2 := by
  unfold rstepL at h ⊢
  by_cases k4 : x.Kind' = W64 4
  · simp only [k4, ite_true] at h ⊢
    rw [rexecL_read x m (by rw [k4]; decide)]
  · simp only [k4, ite_false] at h ⊢
    by_cases kw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
    · simp only [kw, ite_true] at h ⊢
      by_cases he : respEqL (rexecL x m).1 resp = true
      · simp [he]
      · simp [he] at h
    · simp only [kw, ite_false]
      rw [rexecL_read x m kw]

theorem storeKeyL_inj {a b : GoString} (h : storeKeyL a = storeKeyL b) : a = b := by
  unfold storeKeyL at h; exact List.append_cancel_left h

/-- A write that moves the resource version: by one, its change is the one key it writes, which
it changes, and no other key's item or rewrite flag moves. -/
theorem rexecL_bump (x : Input) (m : RM) (hwf : rmWf m) (hb : uint.nat m.rv + 1 < 2 ^ 64)
    (hne : (rexecL x m).2.1.rv ≠ m.rv) :
    (rexecL x m).2.1.rv = m.rv + W64 1 ∧
    (rexecL x m).2.2 = some ⟨storeKeyL x.Key', (rexecL x m).2.1.rv,
      (rexecL x m).2.1.items !! storeKeyL x.Key', m.items !! storeKeyL x.Key'⟩ ∧
    (rexecL x m).2.1.items !! storeKeyL x.Key' ≠ m.items !! storeKeyL x.Key' ∧
    (rexecL x m).2.1.pfx = m.pfx ∧
    (∀ o, (rexecL x m).2.1.items !! storeKeyL x.Key' = some o →
      o.ResourceVersion' = (rexecL x m).2.1.rv) ∧
    (rexecL x m).2.1.rewrites !! storeKeyL x.Key' = none ∧
    ∀ k, k ≠ storeKeyL x.Key' →
      (rexecL x m).2.1.items !! k = m.items !! k ∧ (rexecL x m).2.1.rewrites !! k = m.rewrites !! k := by
  have hrv : ∀ o : Obj, m.items !! storeKeyL x.Key' = some o → o.ResourceVersion' ≠ m.rv + W64 1 := by
    intro o ho e
    have := hwf.1 _ _ ho
    rw [e] at this
    have : uint.nat (m.rv + W64 1) = uint.nat m.rv + 1 := by
      simp only [uint.nat, BitVec.toNat_add, W64]; simp; omega
    omega
  have hk4 : x.Kind' ≠ W64 4 := by
    intro e; apply hne; unfold rexecL; rw [if_pos e]
  have hkw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by
    apply Classical.byContradiction; intro hk; apply hne; rw [rexecL_read x m hk]
  unfold rexecL at hne ⊢
  rw [if_neg hk4] at hne ⊢
  rcases hkw with k | k | k
  · simp only [k, ite_true] at hne ⊢
    unfold rcreateL failR at hne ⊢
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    split at hne
    · simp at hne
    next h1 h2 =>
    rw [if_neg h1, if_neg h2]
    have hn : m.items !! storeKeyL x.Key' = none := by
      rw [GMap.mem_iff] at h2; simpa using h2
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp [hn]
    · simp [hn]
    · intro o ho; simp only [GMap.lookup_insert, Option.some.injEq] at ho; rw [← ho]
    · cases e : m.rewrites !! storeKeyL x.Key' with
      | none => rfl
      | some _ => have := hwf.2 _ (by rw [e]; rfl); rw [hn] at this; simp at this
    · intro k' hk'; exact ⟨GMap.lookup_insert_ne _ _ (Ne.symm hk'), rfl⟩
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    rw [if_neg k0, if_pos k] at hne ⊢
    unfold rdeleteL failR at hne ⊢
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next h1 =>
    rw [if_neg h1]
    split at hne
    · simp at hne
    next s hs =>
    try rw [hs]
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next hp =>
    try rw [hp]
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next hr =>
    rw [if_neg hr]
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro o ho; simp at ho
    · simp
    · intro k' hk'
      exact ⟨GMap.lookup_delete_ne _ (Ne.symm hk'), GMap.lookup_delete_ne _ (Ne.symm hk')⟩
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    have k1 : x.Kind' ≠ W64 1 := by rw [k]; decide
    rw [if_neg k0, if_neg k1, if_pos k] at hne ⊢
    have hw : ∀ st u, m.items !! storeKeyL x.Key' = st →
        (updWriteL m (storeKeyL x.Key') st u).2.1.rv = m.rv + W64 1 ∧
        (updWriteL m (storeKeyL x.Key') st u).2.2 = some ⟨storeKeyL x.Key',
          (updWriteL m (storeKeyL x.Key') st u).2.1.rv,
          (updWriteL m (storeKeyL x.Key') st u).2.1.items !! storeKeyL x.Key',
          m.items !! storeKeyL x.Key'⟩ ∧
        (updWriteL m (storeKeyL x.Key') st u).2.1.items !! storeKeyL x.Key' ≠
          m.items !! storeKeyL x.Key' ∧
        (updWriteL m (storeKeyL x.Key') st u).2.1.pfx = m.pfx ∧
        (∀ o, (updWriteL m (storeKeyL x.Key') st u).2.1.items !! storeKeyL x.Key' = some o →
          o.ResourceVersion' = (updWriteL m (storeKeyL x.Key') st u).2.1.rv) ∧
        (updWriteL m (storeKeyL x.Key') st u).2.1.rewrites !! storeKeyL x.Key' = none ∧
        ∀ k, k ≠ storeKeyL x.Key' →
          (updWriteL m (storeKeyL x.Key') st u).2.1.items !! k = m.items !! k ∧
          (updWriteL m (storeKeyL x.Key') st u).2.1.rewrites !! k = m.rewrites !! k := by
      intro st u hst
      unfold updWriteL
      refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
      · simp [hst]
      · simp only [GMap.lookup_insert]
        intro e
        cases ho : m.items !! storeKeyL x.Key' with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho] at e
          exact hrv o ho (by simp only [Option.some.injEq] at e; rw [← e])
      · intro o ho; simp only [GMap.lookup_insert, Option.some.injEq] at ho; rw [← ho]
      · exact GMap.lookup_delete _ _
      · intro k' hk'
        exact ⟨GMap.lookup_insert_ne _ _ (Ne.symm hk'), GMap.lookup_delete_ne _ (Ne.symm hk')⟩
    unfold rupdateL failR at hne ⊢
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next h1 =>
    rw [if_neg h1]
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next h2 =>
    rw [if_neg h2]
    split at hne
    · simp at hne
    next hp =>
    try rw [hp]
    try dsimp only at hne ⊢
    split at hne
    · simp at hne
    next hr =>
    rw [if_neg hr]
    split at hne
    · next s hs =>
      try rw [hs]
      try dsimp only at hne ⊢
      split at hne
      · simp at hne
      next hn =>
      simp only [hs] at hn; rw [if_neg hn]
      have H := hw _ (updGo x ((some s).getD zObj)) hs
      rw [hs] at H; exact H
    · next hs =>
      try rw [hs]
      have H := hw _ (updGo x ((none : Option Obj).getD zObj)) hs
      rw [hs] at H; exact H

/-! ## The abstraction of a store -/

theorem ofList_items (its : List item) (n : GoString) :
    (GMap.ofList (its.map fun it => (storeKeyL it.key', it.obj'))) !! storeKeyL n =
      (fI its n).map (·.obj') := by
  induction its with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, fI_cons]
    show (<[storeKeyL a.key' := a.obj']> (GMap.ofList (t.map fun it => (storeKeyL it.key', it.obj'))))
      !! storeKeyL n = _
    rw [GMap.lookup_insert_eq_iff]
    by_cases h : a.key' = n
    · simp [h]
    · have : storeKeyL a.key' ≠ storeKeyL n := fun e => h (storeKeyL_inj e)
      simp only [this, h, if_false, ih]

/-- The rewrite flags of a sorted store: a non-canonical item's key. -/
def rwOf : Option item → Option Bool
  | some it => if it.canon' then none else some true
  | none => none

theorem ofList_rewrites (its : List item) (hs : SortedI its) (n : GoString) :
    (GMap.ofList ((its.filter fun it => !it.canon').map fun it => (storeKeyL it.key', true))) !!
      storeKeyL n = rwOf (fI its n) := by
  induction its with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨hs', hlt⟩ := sortedI_cons' hs
    rw [fI_cons]
    by_cases h : a.key' = n
    · subst h
      rw [if_pos rfl]
      have hnone : (GMap.ofList ((t.filter fun it => !it.canon').map
          fun it => (storeKeyL it.key', true))) !! storeKeyL a.key' = none := by
        rw [ih hs', fI_none_of_lt t a.key' hlt]; rfl
      by_cases hc : a.canon' = true
      · simp only [List.filter_cons, hc, Bool.not_true, Bool.false_eq_true, if_false]
        rw [hnone]; simp [rwOf, hc]
      · simp only [List.filter_cons, hc, Bool.not_false, if_true, List.map_cons]
        show (<[storeKeyL a.key' := true]> _) !! storeKeyL a.key' = _
        rw [GMap.lookup_insert]; simp [rwOf, hc]
    · rw [if_neg h, ← ih hs']
      have : storeKeyL a.key' ≠ storeKeyL n := fun e => h (storeKeyL_inj e)
      by_cases hc : a.canon' = true
      · simp only [List.filter_cons, hc, Bool.not_true, Bool.false_eq_true, if_false]
      · simp only [List.filter_cons, hc, Bool.not_false, if_true, List.map_cons]
        show (<[storeKeyL a.key' := true]> _) !! storeKeyL n = _
        rw [GMap.lookup_insert_ne _ _ this]

/-- Two sorted stores whose abstractions agree at the key of `n` have the same item there. -/
theorem fI_eq_of_absR (p q : GSt) (hp : SortedI p.items) (hq : SortedI q.items) (n : GoString)
    (hi : (absR p).items !! storeKeyL n = (absR q).items !! storeKeyL n)
    (hr : (absR p).rewrites !! storeKeyL n = (absR q).rewrites !! storeKeyL n) :
    fI p.items n = fI q.items n := by
  have hi' := hi; have hr' := hr
  simp only [absR] at hi' hr'
  rw [ofList_items, ofList_items] at hi'
  rw [ofList_rewrites _ hp, ofList_rewrites _ hq] at hr'
  cases ea : fI p.items n with
  | none =>
    cases eb : fI q.items n with
    | none => rfl
    | some b => rw [ea, eb] at hi'; simp at hi'
  | some a =>
    cases eb : fI q.items n with
    | none => rw [ea, eb] at hi'; simp at hi'
    | some b =>
      rw [ea, eb] at hi' hr'
      have hka := fI_key ea; have hkb := fI_key eb
      simp only [Option.map_some, Option.some.injEq] at hi'
      have hc : a.canon' = b.canon' := by
        unfold rwOf at hr'
        cases ha : a.canon' <;> cases hb : b.canon' <;> simp_all
      cases a; cases b
      simp_all

/-! ## B3a: any two linearizations that replay give the same replay -/

/-- **B3a.** Two orders `l1`, `l2` of the same operations from a well-formed state, both accepted
by `NewReplay` (every `Step` true), give the same states and changes. The bound keeps the
resource versions from wrapping. -/
theorem replayL_perm (init : RM) (l1 l2 : List (Input × RResp)) (R1 R2 : RReplay)
    (hwf : rmWf init) (hn : uint.nat init.rv + l1.length < 2 ^ 64) (hp : l1.Perm l2)
    (h1 : replayL init l1 = some R1) (h2 : replayL init l2 = some R2) : R1 = R2 := by
  sorry

/-! ## B3b: along the driver's run, the replay is the driver's history -/

/-- **B3b, the start**: before any operation, the accumulator of `NewReplay` from the seeded
store's model tracks the seeded configuration. -/
theorem simR_init (h0 : HSt) (hlen : h0.hist.length = uint.nat h0.st.rv)
    (hlast : h0.hist.getLast? = some h0.st) (hwf : rmWf (absR h0.st)) :
    SimR h0.st.rv (absR h0.st, {[h0.st.rv := absR h0.st]}, []) h0 := by
  refine ⟨rfl, Nat.le_refl _, hwf, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [GMap.lookup_singleton_iff]
    constructor
    · intro hr
      have e : h0.st.rv = r := Classical.byContradiction fun e => by simp [e] at hr
      subst e; omega
    · intro hr
      have e : h0.st.rv = r := by
        apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at hr ⊢; omega
      simp [e]
  · intro c hc; simp at hc
  · intro r h1 h2
    have e : h0.st.rv = r := by
      apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at h1 h2 ⊢; omega
    subst e
    rw [GMap.lookup_singleton_iff, if_pos rfl, histAtL_last _ _ _ hlen hlast]
  · show ([] : List RChange).filter _ = _
    unfold chgListL; rw [hlen, Nat.sub_self]; rfl

/-- **B3b, one step**: a unary operation the driver's model takes from `h` to `h'` (`kstepL`), whose
`Step` on the replay's state is accepted and lands on `h'`'s store (B1), keeps the accumulator
tracking the configuration. -/
theorem simR_step (s0 : w64) (acc : RM × GMap w64 RM × List RChange) (h : HSt)
    (x : Input) (resp : RResp) (acc' : RM × GMap w64 RM × List RChange)
    (hsim : SimR s0 acc h)
    (hlen : h.hist.length = uint.nat h.st.rv) (hlast : h.hist.getLast? = some h.st)
    (hsort : HistSorted (kstepL x h).1.hist)
    (hlen' : (kstepL x h).1.hist.length = uint.nat (kstepL x h).1.st.rv)
    (hrv : uint.nat (kstepL x h).1.st.rv < 2 ^ 63)
    (hstep : replayStepL (some acc) (x, resp) = some acc')
    (habs : acc'.1 = absR (kstepL x h).1.st) :
    SimR s0 acc' (kstepL x h).1 := by
  obtain ⟨m, ss, cs⟩ := acc
  obtain ⟨hm, hs0, hwf, hdom, hcs, hst, hch⟩ := hsim
  simp only at hm hdom hcs hst hch hwf
  simp only [replayStepL] at hstep
  have hT : (rstepL x m resp).1 = true := by
    apply Classical.byContradiction; intro hT; rw [if_neg hT] at hstep; simp at hstep
  rw [if_pos hT, Option.some.injEq] at hstep
  subst hstep
  have h2 := rstepL_true x m resp hT
  simp only [h2] at habs ⊢
  have hH := kstepL_hist x h
  generalize (kstepL x h).1 = h' at habs hH hsort hlen' hrv ⊢
  have hmrv : m.rv = h.st.rv := by rw [hm]; rfl
  have hm'rv : (rexecL x m).2.1.rv = h'.st.rv := by rw [habs]; rfl
  by_cases hr : (rexecL x m).2.1.rv = m.rv
  · have hrv' : h'.st.rv = h.st.rv := by rw [← hmrv, ← hr, hm'rv]
    have hH' : h'.hist = h.hist := by rw [hH, if_pos hrv']
    have e := rexecL_rv_same x m hr
    rw [e] at habs ⊢
    simp only [Option.toList_none, List.append_nil] at habs ⊢
    refine ⟨habs, by rw [hrv']; exact hs0, hwf, ?_, ?_, ?_, ?_⟩
    · intro r
      rw [GMap.lookup_insert_eq_iff, hrv']
      by_cases e2 : m.rv = r
      · subst e2; simp only [if_true, Option.isSome_some, true_iff]; rw [hmrv]; omega
      · rw [if_neg e2]; exact hdom r
    · intro c hc; rw [hrv']; exact hcs c hc
    · intro r h1 h3
      rw [hrv'] at h3
      rw [hH', GMap.lookup_insert_eq_iff]
      by_cases e2 : m.rv = r
      · subst e2; rw [if_pos rfl, hmrv, histAtL_last _ _ _ hlen hlast, hm]
      · rw [if_neg e2]; exact hst r h1 h3
    · show cs.filter _ = _
      rw [hH', hrv']; exact hch
  · have hrv' : h'.st.rv ≠ h.st.rv := by rw [← hm'rv, ← hmrv]; exact hr
    have hH' : h'.hist = h.hist ++ [h'.st] := by rw [hH, if_neg hrv']
    have hnat : uint.nat h'.st.rv = uint.nat h.st.rv + 1 := by
      rw [← hlen', hH', List.length_append, hlen]; rfl
    obtain ⟨_, hb2, hb3, _, hb5, hb6, hb7⟩ :=
      rexecL_bump x m hwf (by rw [hmrv]; omega) hr
    have hsortH : SortedI h.st.items := by
      have := hsort h.hist.length (by rw [hH']; simp)
      rw [hH', histN_append_le _ _ _ (Nat.le_refl _), histN_last _ _ hlast] at this
      exact this
    have hsortH' : SortedI h'.st.items := by
      have := hsort h'.hist.length (Nat.le_refl _)
      rw [histN_last _ h'.st (by rw [hH']; simp)] at this
      exact this
    rw [hb2]
    have hm'nat : uint.nat (rexecL x m).2.1.rv = uint.nat h'.st.rv := by rw [hm'rv]
    refine ⟨habs, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro k o ho
        by_cases ek : k = storeKeyL x.Key'
        · subst ek; rw [hb5 o ho]; exact Nat.le_refl _
        · rw [(hb7 k ek).1] at ho
          have := hwf.1 k o ho
          rw [hm'nat, hnat, ← hmrv]; omega
      · intro k hk
        by_cases ek : k = storeKeyL x.Key'
        · subst ek; rw [hb6] at hk; simp at hk
        · rw [(hb7 k ek).2] at hk; rw [(hb7 k ek).1]; exact hwf.2 k hk
    · intro r
      rw [GMap.lookup_insert_eq_iff]
      by_cases e2 : (rexecL x m).2.1.rv = r
      · subst e2; simp only [if_true, Option.isSome_some, true_iff]; omega
      · rw [if_neg e2, hdom r]
        have hne : uint.nat r ≠ uint.nat h'.st.rv := by
          intro e3; apply e2; rw [hm'rv]; exact (BitVec.eq_of_toNat_eq e3).symm
        omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · have := hcs c hc; omega
      · simp only [Option.toList_some, List.mem_singleton] at hc
        subst hc; exact Nat.le_of_eq hm'nat
    · intro r h1 h3
      rw [GMap.lookup_insert_eq_iff]
      by_cases e2 : (rexecL x m).2.1.rv = r
      · subst e2
        rw [if_pos rfl, hH', histAtL_snoc_gt _ _ _ (by rw [hlen]; omega), habs]
      · rw [if_neg e2]
        have hne : uint.nat r ≠ uint.nat h'.st.rv := by
          intro e3; apply e2; rw [hm'rv]; exact (BitVec.eq_of_toNat_eq e3).symm
        rw [hH', histAtL_snoc_le _ _ _ (by omega)]
        exact hst r h1 (by omega)
    · show (cs ++ _).filter _ = _
      rw [List.filter_append, hH', chgListL_snoc _ _ _ (by omega), ← hch]
      congr 1
      · rw [List.filter_eq_self.2 (fun c hc => by have := hcs c hc; simp; omega),
          List.filter_eq_self.2 (fun c hc => by have := hcs c hc; simp; omega)]
      · rw [Option.toList_some, List.filter_cons, if_pos (by simp; omega), List.filter_nil]
        rw [histN_last _ _ hlast]
        rw [changeAtL_one (x.Key') _ _ _ hsortH hsortH' (fun k hk =>
          fI_eq_of_absR _ _ hsortH hsortH' k
            (by rw [← hm, ← habs]; exact ((hb7 _ (fun e => hk (storeKeyL_inj e))).1).symm)
            (by rw [← hm, ← habs]; exact ((hb7 _ (fun e => hk (storeKeyL_inj e))).2).symm))]
        have hi : (rexecL x m).2.1.items !! storeKeyL x.Key' =
            (fI h'.st.items x.Key').map (·.obj') := by rw [habs]; exact ofList_items _ _
        have hi0 : m.items !! storeKeyL x.Key' = (fI h.st.items x.Key').map (·.obj') := by
          rw [hm]; exact ofList_items _ _
        have hW : (rexecL x m).2.1.rv = W64 ((h.hist.length + 1 : Nat) : Int) := by
          apply BitVec.eq_of_toNat_eq
          rw [show (W64 ((h.hist.length + 1 : Nat) : Int)).toNat = h.hist.length + 1 from
            W64_nat _ (by rw [hlen]; omega)]
          show uint.nat _ = _
          omega
        rw [hi, hi0] at hb3 ⊢
        rw [hW]
        unfold chgL
        generalize fI h.st.items x.Key' = a at hb3 ⊢
        generalize fI h'.st.items x.Key' = b at hb3 ⊢
        cases a <;> cases b
        · simp at hb3
        · simp
        · simp
        · rename_i p q
          have hpq : p ≠ q := fun e => hb3 (by rw [e])
          simp [hpq]

/-- **B3b, earlier configurations**: the final replay agrees with every configuration whose
history is a prefix of the final one's. -/
theorem replayAt_prefix (s0 : w64) (R : RReplay) (h hF : HSt)
    (hR : ReplayAt s0 R hF) (hpre : h.hist <+: hF.hist)
    (hlen : h.hist.length = uint.nat h.st.rv) (hlenF : hF.hist.length = uint.nat hF.st.rv) :
    ReplayAt s0 R h := by
  obtain ⟨t, ht⟩ := hpre
  have hle : uint.nat h.st.rv ≤ uint.nat hF.st.rv := by
    rw [← hlen, ← hlenF, ← ht, List.length_append]; omega
  refine ⟨fun r h1 h2 => ?_, ?_⟩
  · rw [hR.1 r h1 (Nat.le_trans h2 hle), ← ht, histAtL_append_le _ _ _ (by omega)]
  · have hf : R.changes.filter (fun c => decide (uint.nat c.rv ≤ uint.nat h.st.rv)) =
        (R.changes.filter (fun c => decide (uint.nat c.rv ≤ uint.nat hF.st.rv))).filter
          (fun c => decide (uint.nat c.rv ≤ uint.nat h.st.rv)) := by
      rw [List.filter_filter]; congr; funext c
      by_cases hc : uint.nat c.rv ≤ uint.nat h.st.rv <;> simp [hc] <;> omega
    rw [hf, hR.2, ← ht, ← hlen]
    exact chgListL_filter _ _ _ (by rw [ht, hlenF]; exact hF.st.rv.isLt)

end go

end k8s_correctness
end EtcdGrove
end Perennial
