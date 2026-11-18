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
    refine ⟨rfl, ?_, ?_, rfl, ?_⟩
    · simp [hn]
    · simp [hn]
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
    refine ⟨rfl, ?_, ?_, rfl, ?_⟩
    · simp
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
        ∀ k, k ≠ storeKeyL x.Key' →
          (updWriteL m (storeKeyL x.Key') st u).2.1.items !! k = m.items !! k ∧
          (updWriteL m (storeKeyL x.Key') st u).2.1.rewrites !! k = m.rewrites !! k := by
      intro st u hst
      unfold updWriteL
      refine ⟨rfl, ?_, ?_, rfl, ?_⟩
      · simp [hst]
      · simp only [GMap.lookup_insert]
        intro e
        cases ho : m.items !! storeKeyL x.Key' with
        | none => rw [ho] at e; simp at e
        | some o =>
          rw [ho] at e
          exact hrv o ho (by simp only [Option.some.injEq] at e; rw [← e])
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
  sorry

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
