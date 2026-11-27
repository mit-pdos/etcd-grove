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
  ∀ r ≤ hs.length, ((k8s_etcd3.histN hs r).items.map (·.key')).Pairwise go.GoStringLt

theorem changeAtL_rv : ∀ (p q : List item) (r : Nat) (ch : Chg), changeAtL p q r = some ch → ch.rv = r
  | [], [], _, _, h => by simp [changeAtL] at h
  | _ :: _, [], _, _, h => by simp only [changeAtL, Option.some.injEq] at h; subst h; rfl
  | [], _ :: _, _, _, h => by simp only [changeAtL, Option.some.injEq] at h; subst h; rfl
  | p :: ps, q :: qs, r, ch, h => by
    simp only [changeAtL] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · split at h
        · exact changeAtL_rv ps qs r ch h
        · simp only [Option.some.injEq] at h; subst h; rfl

/-- **A history's objects carry their revisions** (what B5's `HistWf` needs, for every watch): an object
of the store at revision `r` has a revision in `[1, r]` and no annotation, and the change at each revision
`r` (`changeAtL`) carries objects with no annotation, its new object at revision `r`. Kept by every step
(`kstepL_runOk`). -/
def HistGood (hs : List GSt) : Prop :=
  (∀ r it, r ≤ hs.length → it ∈ (k8s_etcd3.histN hs r).items →
    1 ≤ uint.nat it.obj'.ResourceVersion' ∧ uint.nat it.obj'.ResourceVersion' ≤ r ∧
      it.obj'.Annotated' = false) ∧
  ∀ r ch, 2 ≤ r → r ≤ hs.length → changeAtL (k8s_etcd3.histN hs (r - 1)).items (k8s_etcd3.histN hs r).items r = some ch →
    (∀ o, ch.cur = some o → uint.nat o.ResourceVersion' = r ∧ o.Annotated' = false) ∧
      ∀ o, ch.prev = some o → o.Annotated' = false

/-- **The changes of a history from revision `s0` on**, as the checker's `Change`s: for each
revision `r` in `(s0, |hs|]`, the item that differs between the stores at `r - 1` and `r`
(`changeAtL`), at its store key. -/
def chgListL (s0 : Nat) (hs : List GSt) : List RChange :=
  (List.range' (s0 + 1) (hs.length - s0)).filterMap fun r =>
    (changeAtL (k8s_etcd3.histN hs (r - 1)).items (k8s_etcd3.histN hs r).items r).map fun ch =>
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
    k8s_etcd3.histN (l ++ t) r = k8s_etcd3.histN l r := by
  unfold k8s_etcd3.histN; rw [List.take_append_of_le_length h]

theorem histAtL_append_le (l t : List GSt) (r : w64) (h : uint.nat r ≤ l.length) :
    histAtL (l ++ t) r = histAtL l r := by
  unfold histAtL; rw [List.take_append_of_le_length h]

theorem histAtL_last (hs : List GSt) (st : GSt) (r : w64) (hlen : hs.length = uint.nat r)
    (hlast : hs.getLast? = some st) : histAtL hs r = st := by
  unfold histAtL; rw [List.take_of_length_le (by omega), hlast]; rfl

theorem histN_last (hs : List GSt) (st : GSt) (hlast : hs.getLast? = some st) :
    k8s_etcd3.histN hs hs.length = st := by
  unfold k8s_etcd3.histN; rw [List.take_length, hlast]; rfl

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
        ((changeAtL (k8s_etcd3.histN (l ++ t) (r - 1)).items (k8s_etcd3.histN (l ++ t) r).items r).map fun ch =>
          (⟨storeKeyL ch.key, W64 (r : Int), ch.cur, ch.prev⟩ : RChange)).filter
          (fun c => decide (uint.nat c.rv ≤ l.length))) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro r hr
      rw [List.mem_range'_1] at hr
      cases changeAtL (k8s_etcd3.histN (l ++ t) (r - 1)).items (k8s_etcd3.histN (l ++ t) r).items r with
      | none => rfl
      | some ch =>
        simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
        rw [W64_nat r (by omega)]; simp; omega
    rw [h2, List.append_nil]
    apply filterMap_congr'
    intro r hr
    rw [List.mem_range'_1] at hr
    rw [histN_append_le l t r (by omega), histN_append_le l t (r - 1) (by omega)]
    cases changeAtL (k8s_etcd3.histN l (r - 1)).items (k8s_etcd3.histN l r).items r with
    | none => rfl
    | some ch =>
      simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
      rw [W64_nat r (by omega)]; simp; omega
  · have h0 : l.length - s0 = 0 := by omega
    rw [h0, List.range'_zero, List.filterMap_nil, List.filterMap_eq_nil_iff]
    intro r hr
    rw [List.mem_range'_1] at hr
    cases changeAtL (k8s_etcd3.histN (l ++ t) (r - 1)).items (k8s_etcd3.histN (l ++ t) r).items r with
    | none => rfl
    | some ch =>
      simp only [Option.map_some, Option.filter_some, decide_eq_true_eq]
      rw [W64_nat r (by omega)]; simp; omega

/-- The changes of a history one store longer: the last revision's change appended. -/
theorem chgListL_snoc (s0 : Nat) (l : List GSt) (st : GSt) (hs : s0 ≤ l.length) :
    chgListL s0 (l ++ [st]) = chgListL s0 l ++
      ((changeAtL (k8s_etcd3.histN l l.length).items st.items (l.length + 1)).map fun ch =>
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
  · have h1 : k8s_etcd3.histN (l ++ [st]) (l.length + 1) = st := by
      have := histN_last (l ++ [st]) st (by simp)
      simpa using this
    simp only [List.filterMap_cons, List.filterMap_nil, Nat.add_sub_cancel, h1,
      histN_append_le l [st] l.length (Nat.le_refl _)]
    cases changeAtL (k8s_etcd3.histN l l.length).items st.items (l.length + 1) <;> rfl

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

/-! ### A write's answer -/

theorem rcreateL_obj (x : Input) (m : RM) (o : Obj) (h : (rcreateL x m).1.obj = .obj o) :
    o.ResourceVersion' = m.rv + W64 1 ∧ (rcreateL x m).2.1.items !! storeKeyL x.Key' = some o ∧
      (rcreateL x m).2.1.rv = m.rv + W64 1 := by
  unfold rcreateL failR at h ⊢
  dsimp only at h ⊢
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  rw [if_neg h1, if_neg h2]
  simp only [DeepV.obj.injEq] at h
  subst h
  simp

theorem rdeleteL_obj (x : Input) (m : RM) (o : Obj) (h : (rdeleteL x m).1.obj = .obj o) :
    o.ResourceVersion' = m.rv + W64 1 ∧ (rdeleteL x m).2.1.items !! storeKeyL x.Key' = none ∧
      (rdeleteL x m).2.1.rv = m.rv + W64 1 := by
  unfold rdeleteL failR at h ⊢
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i h1
  rw [if_neg h1]
  split at h
  · simp at h
  rename_i s hs
  try rw [hs]
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i hp
  try rw [hp]
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i hr
  rw [if_neg hr]
  simp only [DeepV.obj.injEq] at h
  subst h
  simp

theorem rupdateL_obj (x : Input) (m : RM) (o : Obj) (h : (rupdateL x m).1.obj = .obj o) :
    (o.ResourceVersion' = m.rv + W64 1 ∧ (rupdateL x m).2.1.items !! storeKeyL x.Key' = some o ∧
      (rupdateL x m).2.1.rv = m.rv + W64 1) ∨
    ((rupdateL x m).2 = (m, none) ∧ m.items !! storeKeyL x.Key' = some o) := by
  unfold rupdateL failR updWriteL at h ⊢
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i h1
  rw [if_neg h1]
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i h2
  rw [if_neg h2]
  split at h
  · simp at h
  rename_i hp
  try rw [hp]
  try dsimp only at h ⊢
  split at h
  · simp at h
  rename_i hr
  rw [if_neg hr]
  split at h
  · rename_i s hs
    try rw [hs]
    try dsimp only at h ⊢
    split at h
    · rename_i hn
      simp only [hs] at hn; rw [if_pos hn]
      simp only [DeepV.obj.injEq] at h
      subst h
      exact .inr ⟨rfl, by simp [hs]⟩
    · rename_i hn
      simp only [hs] at hn; rw [if_neg hn]
      simp only [DeepV.obj.injEq] at h
      subst h
      left; simp [hs]
  · rename_i hs
    try rw [hs]
    try dsimp only at h ⊢
    simp only [DeepV.obj.injEq] at h
    subst h
    left; simp [hs]

theorem rcreateL_obj_or (x : Input) (m : RM) :
    (∃ o, (rcreateL x m).1.obj = .obj o) ∨ (rcreateL x m).2 = (m, none) := by
  unfold rcreateL failR
  dsimp only
  (repeat' split) <;> simp

theorem rdeleteL_obj_or (x : Input) (m : RM) :
    (∃ o, (rdeleteL x m).1.obj = .obj o) ∨ (rdeleteL x m).2 = (m, none) := by
  unfold rdeleteL failR
  dsimp only
  (repeat' split) <;> simp

theorem rupdateL_obj_or (x : Input) (m : RM) :
    (∃ o, (rupdateL x m).1.obj = .obj o) ∨ (rupdateL x m).2 = (m, none) := by
  unfold rupdateL failR updWriteL
  dsimp only
  (repeat' split) <;> simp


/-- A write (create, delete, update) answered with an object: that object. -/
def wrObj (op : Input × RResp) : Option Obj :=
  if op.1.Kind' = W64 0 ∨ op.1.Kind' = W64 1 ∨ op.1.Kind' = W64 2 then
    match op.2.obj with
    | .obj o => some o
    | _ => none
  else none

/-- What a write answered with `o` does when it moves the resource version: its key, and the
object it leaves there (none for a delete). -/
def gOf (op : Input × RResp) (o : Obj) : GoString × Option Obj :=
  (storeKeyL op.1.Key', if op.1.Kind' = W64 1 then none else some o)

theorem respEqL_obj {a b : RResp} (h : respEqL a b = true) : a.obj = b.obj := by
  unfold respEqL at h
  split at h
  · exact (of_decide_eq_true h).1
  · cases h

/-- An accepted write answered with `o` either moves the resource version, to `o`'s, leaving
`gOf`'s object at its key, or is a no-op update answering the object stored at its key. -/
theorem rexecL_wr (x : Input) (m : RM) (resp : RResp) (o : Obj)
    (hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)
    (heq : respEqL (rexecL x m).1 resp = true) (ho : resp.obj = .obj o) :
    (o.ResourceVersion' = m.rv + W64 1 ∧ (rexecL x m).2.1.rv = m.rv + W64 1 ∧
      (rexecL x m).2.1.items !! storeKeyL x.Key' = (gOf (x, resp) o).2) ∨
    (x.Kind' = W64 2 ∧ (rexecL x m).2 = (m, none) ∧ m.items !! storeKeyL x.Key' = some o) := by
  have h := (respEqL_obj heq).trans ho
  have hk4 : x.Kind' ≠ W64 4 := by rcases hw with e | e | e <;> rw [e] <;> decide
  unfold rexecL at h ⊢
  rw [if_neg hk4] at h ⊢
  unfold gOf
  simp only []
  rcases hw with k | k | k
  · rw [if_pos k] at h ⊢
    have hk1 : x.Kind' ≠ W64 1 := by rw [k]; decide
    rw [if_neg hk1]
    obtain ⟨a, b, c⟩ := rcreateL_obj x m o h
    exact .inl ⟨a, c, b⟩
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    rw [if_neg k0, if_pos k] at h ⊢
    rw [if_pos k]
    obtain ⟨h1, h2, h3⟩ := rdeleteL_obj x m o h
    exact .inl ⟨h1, h3, h2⟩
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    have k1 : x.Kind' ≠ W64 1 := by rw [k]; decide
    rw [if_neg k0, if_neg k1, if_pos k] at h ⊢
    rw [if_neg k1]
    rcases rupdateL_obj x m o h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h3, h2⟩
    · exact .inr ⟨k, h1, h2⟩

/-- A write that moves the resource version answers with an object. -/
theorem rexecL_bump_obj (x : Input) (m : RM) (hne : (rexecL x m).2.1.rv ≠ m.rv) :
    (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) ∧ ∃ o, (rexecL x m).1.obj = .obj o := by
  have hk4 : x.Kind' ≠ W64 4 := by
    intro e; apply hne; unfold rexecL; rw [if_pos e]
  have hkw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by
    apply Classical.byContradiction; intro hk; apply hne; rw [rexecL_read x m hk]
  refine ⟨hkw, ?_⟩
  unfold rexecL at hne ⊢
  rw [if_neg hk4] at hne ⊢
  rcases hkw with k | k | k
  · rw [if_pos k] at hne ⊢
    rcases rcreateL_obj_or x m with h | h
    · exact h
    · rw [h] at hne; exact absurd rfl hne
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    rw [if_neg k0, if_pos k] at hne ⊢
    rcases rdeleteL_obj_or x m with h | h
    · exact h
    · rw [h] at hne; exact absurd rfl hne
  · have k0 : x.Kind' ≠ W64 0 := by rw [k]; decide
    have k1 : x.Kind' ≠ W64 1 := by rw [k]; decide
    rw [if_neg k0, if_neg k1, if_pos k] at hne ⊢
    rcases rupdateL_obj_or x m with h | h
    · exact h
    · rw [h] at hne; exact absurd rfl hne

/-! ### A replay as the sequence of its writes -/

/-- The state after a write of `v` at the key `k` (none: deleted) at the next resource version. -/
def bumpL (m : RM) (k : GoString) (v : Option Obj) : RM :=
  ⟨match v with
    | some o => <[k := o]> m.items
    | none => GMap.delete k m.items,
   m.rv + W64 1, m.pfx, GMap.delete k m.rewrites⟩

/-- One write of `runOf`. -/
def runStep (acc : RM × GMap w64 RM × List RChange) (p : GoString × Option Obj) :
    RM × GMap w64 RM × List RChange :=
  (bumpL acc.1 p.1 p.2, <[(bumpL acc.1 p.1 p.2).rv := bumpL acc.1 p.1 p.2]> acc.2.1,
    acc.2.2 ++ [⟨p.1, (bumpL acc.1 p.1 p.2).rv, p.2, acc.1.items !! p.1⟩])

/-- **`NewReplay`'s accumulator after the writes `kv`** (each a key and what it leaves there), in
order from `init`. -/
def runOf (init : RM) (kv : List (GoString × Option Obj)) : RM × GMap w64 RM × List RChange :=
  kv.foldl runStep (init, {[init.rv := init]}, [])

theorem runOf_snoc (init : RM) (kv : List (GoString × Option Obj)) (p : GoString × Option Obj) :
    runOf init (kv ++ [p]) = runStep (runOf init kv) p := by
  unfold runOf; rw [List.foldl_append]; rfl

theorem runOf_self (init : RM) (kv : List (GoString × Option Obj)) :
    (runOf init kv).2.1 !! (runOf init kv).1.rv = some (runOf init kv).1 := by
  rcases List.eq_nil_or_concat kv with rfl | ⟨kv, p, rfl⟩
  · show ({[init.rv := init]} : GMap w64 RM) !! init.rv = some init; simp
  · rw [List.concat_eq_append, runOf_snoc]; unfold runStep; simp only []; exact GMap.lookup_insert _ _ _

theorem insert_self {V : Type} (M : GMap w64 V) (k : w64) (v : V) (h : M !! k = some v) :
    <[k := v]> M = M := by
  refine GMap.ext (fun k' => ?_); rw [GMap.lookup_insert_eq_iff]
  split
  · rename_i e; subst e; exact h.symm
  · rfl

/-- A write that moves the resource version, as `bumpL` of its key and what it leaves there. -/
theorem rexecL_bumpL (x : Input) (m : RM) (hwf : rmWf m) (hb : uint.nat m.rv + 1 < 2 ^ 64)
    (hne : (rexecL x m).2.1.rv ≠ m.rv) :
    (rexecL x m).2.1 = bumpL m (storeKeyL x.Key') ((rexecL x m).2.1.items !! storeKeyL x.Key') ∧
    (rexecL x m).2.2 = some ⟨storeKeyL x.Key', m.rv + W64 1,
      (rexecL x m).2.1.items !! storeKeyL x.Key', m.items !! storeKeyL x.Key'⟩ := by
  obtain ⟨h1, h2, -, h4, -, h6, h7⟩ := rexecL_bump x m hwf hb hne
  refine ⟨?_, by rw [h2, h1]⟩
  generalize hm' : (rexecL x m).2.1 = m' at h1 h4 h6 h7 ⊢
  obtain ⟨its, rv, pfx, rws⟩ := m'
  simp only at h1 h4 h6 h7 ⊢
  unfold bumpL
  simp only [h1, h4, RM.mk.injEq, true_and, and_true]
  constructor
  · refine GMap.ext (fun k => ?_)
    by_cases hk : k = storeKeyL x.Key'
    · subst hk
      cases e : its !! storeKeyL x.Key' with
      | none => simp only []; rw [GMap.lookup_delete]
      | some o => simp only []; rw [GMap.lookup_insert]
    · have := (h7 k hk).1
      cases e : its !! storeKeyL x.Key' with
      | none => simp only []; rw [GMap.lookup_delete_ne _ (Ne.symm hk)]; exact this
      | some o => simp only []; rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact this
  · refine GMap.ext (fun k => ?_)
    by_cases hk : k = storeKeyL x.Key'
    · subst hk; rw [h6, GMap.lookup_delete]
    · rw [(h7 k hk).2, GMap.lookup_delete_ne _ (Ne.symm hk)]


/-! ### The invariant of a replay -/

/-- **What `NewReplay` has done after the operations `P`**: its accumulator is `runOf init kv`
for the writes `kv` that moved the resource version (one per revision after `init`'s); the state is
well formed; each object stored past `init`'s revision was left by the write at its revision; each
of those writes is the answer of an operation of `P` at its revision; and every operation of `P`
that answered an object past `init`'s revision answered the write at that revision. -/
def RInv (init : RM) (P : List (Input × RResp)) (kv : List (GoString × Option Obj))
    (acc : RM × GMap w64 RM × List RChange) : Prop :=
  acc = runOf init kv ∧ rmWf acc.1 ∧ uint.nat acc.1.rv = uint.nat init.rv + kv.length ∧
  kv.length ≤ P.length ∧
  (∀ k o, acc.1.items !! k = some o → uint.nat init.rv < uint.nat o.ResourceVersion' →
    ∃ i, ∃ hi : i < kv.length, kv[i] = (k, some o) ∧
      uint.nat o.ResourceVersion' = uint.nat init.rv + i + 1) ∧
  (∀ i, ∀ hi : i < kv.length, ∃ A ∈ P, ∃ o, wrObj A = some o ∧
    uint.nat o.ResourceVersion' = uint.nat init.rv + i + 1 ∧ kv[i] = gOf A o) ∧
  (∀ A ∈ P, ∀ o, wrObj A = some o → uint.nat init.rv < uint.nat o.ResourceVersion' →
    ∃ i, ∃ hi : i < kv.length, uint.nat o.ResourceVersion' = uint.nat init.rv + i + 1 ∧
      kv[i] = gOf A o)

theorem wrObj_some {A : Input × RResp} {o : Obj} (h : wrObj A = some o) :
    (A.1.Kind' = W64 0 ∨ A.1.Kind' = W64 1 ∨ A.1.Kind' = W64 2) ∧ A.2.obj = .obj o := by
  unfold wrObj at h
  split at h
  · rename_i hk
    refine ⟨hk, ?_⟩
    split at h
    · rename_i o' ho; simp only [Option.some.injEq] at h; subst h; exact ho
    · cases h
  · cases h

theorem rinv_step (init : RM) (P : List (Input × RResp)) (kv : List (GoString × Option Obj))
    (acc acc' : RM × GMap w64 RM × List RChange) (A : Input × RResp)
    (hinv : RInv init P kv acc) (hb : uint.nat init.rv + P.length + 1 < 2 ^ 64)
    (hstep : replayStepL (some acc) A = some acc') :
    ∃ kv', RInv init (P ++ [A]) kv' acc' := by
  obtain ⟨hacc, hwf, hrv, hlenP, hst, hP1, hP2⟩ := hinv
  obtain ⟨m, ss, cs⟩ := acc
  simp only at hwf hrv hst
  simp only [replayStepL] at hstep
  have hT : (rstepL A.1 m A.2).1 = true := by
    apply Classical.byContradiction; intro hT; rw [if_neg hT] at hstep; simp at hstep
  rw [if_pos hT, Option.some.injEq] at hstep
  subst hstep
  have h2 := rstepL_true A.1 m A.2 hT
  simp only [h2]
  -- an accepted write answered with an object: `respEqL` of `execute`'s answer
  have hresp : ∀ o, wrObj A = some o → respEqL (rexecL A.1 m).1 A.2 = true := by
    intro o ho
    obtain ⟨hk, -⟩ := wrObj_some ho
    have hk4 : A.1.Kind' ≠ W64 4 := by rcases hk with e | e | e <;> rw [e] <;> decide
    unfold rstepL at hT
    rw [if_neg hk4, if_pos hk] at hT
    apply Classical.byContradiction; intro hn; rw [if_neg hn] at hT; cases hT
  have hmem : ∀ A' ∈ P, A' ∈ P ++ [A] := fun A' h => List.mem_append_left _ h
  by_cases hr : (rexecL A.1 m).2.1.rv = m.rv
  · -- no write: the accumulator is unchanged
    have e := rexecL_rv_same A.1 m hr
    rw [e]
    simp only [Option.toList_none, List.append_nil]
    have hself := runOf_self init kv
    rw [← hacc] at hself
    simp only at hself
    rw [insert_self ss m.rv m hself]
    refine ⟨kv, hacc, hwf, hrv, by simp; omega, hst, ?_, ?_⟩
    · intro i hi
      obtain ⟨A', hA', o, h1, h2, h3⟩ := hP1 i hi
      exact ⟨A', hmem A' hA', o, h1, h2, h3⟩
    · intro A' hA' o ho hgt
      rcases List.mem_append.1 hA' with hA' | hA'
      · exact hP2 A' hA' o ho hgt
      · simp only [List.mem_singleton] at hA'; subst hA'
        obtain ⟨hk, hob⟩ := wrObj_some ho
        rcases rexecL_wr A'.1 m A'.2 o hk (hresp o ho) hob with ⟨h1, h3, -⟩ | ⟨hk2, -, hs⟩
        · exact ((w64_add_one_ne m.rv).1 (h3.symm.trans hr)).elim
        · obtain ⟨i, hi, hkv, hrvi⟩ := hst _ o hs hgt
          refine ⟨i, hi, hrvi, ?_⟩
          rw [hkv]; unfold gOf
          have : A'.1.Kind' ≠ W64 1 := by rw [hk2]; decide
          rw [if_neg this]
  · -- a write at the next revision
    have hbm : uint.nat m.rv + 1 < 2 ^ 64 := by omega
    obtain ⟨hB1, hB2⟩ := rexecL_bumpL A.1 m hwf hbm hr
    obtain ⟨-, -, -, -, hB5, hB6, hB7⟩ := rexecL_bump A.1 m hwf hbm hr
    obtain ⟨hk, o, ho⟩ := rexecL_bump_obj A.1 m hr
    have hAo : A.2.obj = .obj o := by
      rw [← ho]
      have hk4 : A.1.Kind' ≠ W64 4 := by rcases hk with e | e | e <;> rw [e] <;> decide
      have : respEqL (rexecL A.1 m).1 A.2 = true := by
        unfold rstepL at hT
        rw [if_neg hk4, if_pos hk] at hT
        apply Classical.byContradiction; intro hn; rw [if_neg hn] at hT; cases hT
      exact (respEqL_obj this).symm
    have hwr : wrObj A = some o := by unfold wrObj; rw [if_pos hk, hAo]
    obtain ⟨hO1, hO2, hO3⟩ : o.ResourceVersion' = m.rv + W64 1 ∧ (rexecL A.1 m).2.1.rv = m.rv + W64 1 ∧
        (rexecL A.1 m).2.1.items !! storeKeyL A.1.Key' = (gOf (A.1, A.2) o).2 := by
      rcases rexecL_wr A.1 m A.2 o hk (hresp o hwr) hAo with h | ⟨-, hO2, -⟩
      · exact h
      · rw [hO2] at hr; exact absurd rfl hr
    have hrv1 : uint.nat (m.rv + W64 1) = uint.nat m.rv + 1 := by
      simp only [uint.nat, BitVec.toNat_add, W64]; simp; omega
    refine ⟨kv ++ [gOf A o], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runOf_snoc, ← hacc]
      unfold runStep
      simp only []
      have hk' : (gOf A o).1 = storeKeyL A.1.Key' := rfl
      rw [hk', ← hO3, ← hB1, hB2, hO2]
      rfl
    · -- well formed
      simp only []
      refine ⟨fun k o' hk' => ?_, fun k hk' => ?_⟩
      · by_cases e : k = storeKeyL A.1.Key'
        · subst e; rw [hB5 o' hk']; exact Nat.le_refl _
        · rw [(hB7 k e).1] at hk'
          have := hwf.1 k o' hk'
          rw [hO2, hrv1]; omega
      · by_cases e : k = storeKeyL A.1.Key'
        · subst e; rw [hB6] at hk'; cases hk'
        · rw [(hB7 k e).2] at hk'; rw [(hB7 k e).1]; exact hwf.2 k hk'
    · simp only [List.length_append, List.length_singleton]; rw [hO2, hrv1, hrv]; omega
    · simp; omega
    · -- stored objects
      intro k o' hk' hgt
      simp only [] at hk'
      by_cases e : k = storeKeyL A.1.Key'
      · subst e
        have hr' := hB5 o' hk'
        refine ⟨kv.length, by simp, ?_, ?_⟩
        · rw [List.getElem_append_right (by omega)]
          simp only [Nat.sub_self, List.getElem_singleton]
          unfold gOf
          rw [← hk', hO3]; rfl
        · rw [hr', hO2, hrv1, hrv]
      · rw [(hB7 k e).1] at hk'
        obtain ⟨i, hi, hkv, hrvi⟩ := hst k o' hk' hgt
        exact ⟨i, by simp; omega, by rw [List.getElem_append_left hi]; exact hkv, hrvi⟩
    · -- each write is an answer
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases e : i < kv.length
      · obtain ⟨A', hA', o', h1, h2, h3⟩ := hP1 i e
        exact ⟨A', hmem A' hA', o', h1, h2, by rw [List.getElem_append_left e]; exact h3⟩
      · have ei : i = kv.length := by omega
        subst ei
        refine ⟨A, by simp, o, hwr, ?_, ?_⟩
        · rw [hO1, hrv1, hrv]
        · rw [List.getElem_append_right (by omega)]; simp
    · -- each answer is a write
      intro A' hA' o' ho' hgt
      rcases List.mem_append.1 hA' with hA' | hA'
      · obtain ⟨i, hi, h1, h2⟩ := hP2 A' hA' o' ho' hgt
        exact ⟨i, by simp; omega, h1, by rw [List.getElem_append_left hi]; exact h2⟩
      · simp only [List.mem_singleton] at hA'; subst hA'
        rw [hwr, Option.some.injEq] at ho'; subst ho'
        refine ⟨kv.length, by simp, by rw [hO1, hrv1, hrv], ?_⟩
        rw [List.getElem_append_right (by omega)]; simp

theorem rinv_foldl (init : RM) : ∀ (l P : List (Input × RResp)) (kv : List (GoString × Option Obj))
    (acc fin : RM × GMap w64 RM × List RChange),
    RInv init P kv acc → uint.nat init.rv + P.length + l.length < 2 ^ 64 →
    l.foldl replayStepL (some acc) = some fin → ∃ kv', RInv init (P ++ l) kv' fin
  | [], P, kv, acc, fin, hinv, _, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h; subst h
    exact ⟨kv, by simpa using hinv⟩
  | A :: l, P, kv, acc, fin, hinv, hb, h => by
    rw [List.foldl_cons] at h
    cases hs : replayStepL (some acc) A with
    | none => rw [hs, replayStepL_none] at h; cases h
    | some acc' =>
      rw [hs] at h
      obtain ⟨kv', hinv'⟩ := rinv_step init P kv acc acc' A hinv
        (by simp only [List.length_cons] at hb; omega) hs
      obtain ⟨kv'', hinv''⟩ := rinv_foldl init l (P ++ [A]) kv' acc' fin hinv'
        (by simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil] at hb ⊢
            omega) h
      exact ⟨kv'', by simpa using hinv''⟩

/-- **B3a.** Two orders `l1`, `l2` of the same operations from a well-formed state, both accepted
by `NewReplay` (every `Step` true), give the same states and changes. The bound keeps the
resource versions from wrapping. -/
theorem replayL_perm (init : RM) (l1 l2 : List (Input × RResp)) (R1 R2 : RReplay)
    (hwf : rmWf init) (hn : uint.nat init.rv + l1.length < 2 ^ 64) (hp : l1.Perm l2)
    (h1 : replayL init l1 = some R1) (h2 : replayL init l2 = some R2) : R1 = R2 := by
  unfold replayL at h1 h2
  obtain ⟨fin1, hf1, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨fin2, hf2, rfl⟩ := Option.map_eq_some_iff.1 h2
  have hinit : RInv init [] [] (init, {[init.rv := init]}, []) := by
    refine ⟨rfl, hwf, by simp, by simp, ?_, ?_, ?_⟩
    · intro k o hk hgt; have := hwf.1 k o hk; omega
    · intro i hi; simp at hi
    · intro A hA; simp at hA
  obtain ⟨kv1, hI1⟩ := rinv_foldl init l1 [] [] _ fin1 hinit (by simpa using hn) hf1
  obtain ⟨kv2, hI2⟩ := rinv_foldl init l2 [] [] _ fin2 hinit
    (by rw [← hp.length_eq]; simpa using hn) hf2
  simp only [List.nil_append] at hI1 hI2
  have key : ∀ (la lb : List (Input × RResp)) (kva kvb : List (GoString × Option Obj))
      (fa fb : RM × GMap w64 RM × List RChange), RInv init la kva fa → RInv init lb kvb fb →
      la.Perm lb → ∀ i (hi : i < kva.length), ∃ hi' : i < kvb.length, kvb[i] = kva[i] := by
    intro la lb kva kvb fa fb ha hb hab i hi
    obtain ⟨A, hA, o, ho, hrv, hkv⟩ := ha.2.2.2.2.2.1 i hi
    obtain ⟨j, hj, hrv', hkv'⟩ := hb.2.2.2.2.2.2 A (hab.mem_iff.1 hA) o ho (by omega)
    have : j = i := by omega
    subst this
    exact ⟨hj, hkv'.trans hkv.symm⟩
  have hlen : kv1.length = kv2.length := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_lt; intro h
      exact absurd (key l1 l2 kv1 kv2 fin1 fin2 hI1 hI2 hp kv2.length h).1 (Nat.lt_irrefl _)
    · apply Nat.le_of_not_lt; intro h
      exact absurd (key l2 l1 kv2 kv1 fin2 fin1 hI2 hI1 hp.symm kv1.length h).1 (Nat.lt_irrefl _)
  have hkv : kv1 = kv2 :=
    List.ext_getElem hlen (fun i h1 _ => (key l1 l2 kv1 kv2 fin1 fin2 hI1 hI2 hp i h1).2.symm)
  rw [hI1.1, hI2.1, hkv]

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
