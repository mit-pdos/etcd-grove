/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-1..K8-4: the shared seed is one `realCheck` runs from (`notes/k8s-dist-k8-scope.md` §2)

- `seedAt r1 r2 r`: the store of the shared seed's history (`seedSharedL r1 r2`, `SeedShared`/`SeededAt`)
  at revision `r`: empty below `r1`, the first seed from `r1` to below `r2`, both seeds at `r2`;
- `seedSharedL_hist`: that history is `seedAt` at `1, ..., r2`;
- `runOk_seedShared`: for `1 < r1 < r2 < 2^63`, `RunOk (seedSharedL r1 r2)`, what `realCheck`'s pure core
  (`realCheck_pure`) takes of the configuration it starts from (`runOk_g0s`'s generalization: the
  driver's seed is `r1 = 2`, `r2 = 3`; the padded stores between them are the foreign revisions).

- `noForeign_erase` (K8-4): a failure-free run of the semantic model (`SRun`) whose history shows no
  foreign revision (`NoForeignOk`) is a run of the driver's model (`PRun`, no foreign step). Step 3
  (`sRun_jr`): a successful write answers the revision it writes or an item's (a no-op update), and items
  carry only written revisions, so no foreign step comes before `m`; after it, `erase_go` takes K4's
  `CRel.op` with every target at most `m` (`targetL_le_anchors`) and `stepL_sound`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedSharedDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealB4
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedRename
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedComplete
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.NoForeignDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3 k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section pure
variable [GooseExts]

/-- The shared seed's store at revision `r` (see the file header). -/
def seedAt (r1 r2 : w64) (r : Nat) : GSt :=
  if r < uint.nat r1 then ⟨[], W64 (r : Int)⟩
  else if r < uint.nat r2 then ⟨[seedItem kA r1], W64 (r : Int)⟩
  else ⟨[seedItem kA r1, seedItem kB r2], W64 (r : Int)⟩

theorem setItemL_seedA (r1 : w64) : setItemL [] (seedItem kA r1) = [seedItem kA r1] := by
  rw [seedItem_kA]; rfl

theorem setItemL_seedB (r1 r2 : w64) :
    setItemL [seedItem kA r1] (seedItem kB r2) = [seedItem kA r1, seedItem kB r2] := by
  rw [seedItem_kA, seedItem_kB]; rfl

theorem seedSharedL_st (r1 r2 : w64) (h12 : uint.nat r1 < uint.nat r2) :
    (seedSharedL r1 r2).st = seedAt r1 r2 (uint.nat r2) := by
  simp only [seedSharedL, seedStepL, seedInitL, setItemL_seedA, setItemL_seedB, seedAt,
    show ¬ uint.nat r2 < uint.nat r1 by omega, Nat.lt_irrefl, ite_false]
  congr 1; word

theorem range'_seedShared (a b : Nat) (ha : 2 ≤ a) (hab : a < b) :
    List.range' 1 b = 1 :: (List.range' 2 (a - 2) ++ a :: (List.range' (a + 1) (b - (a + 1)) ++ [b])) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, b = c + 2 + d + 1 := ⟨b - (c + 2) - 1, by omega⟩
  rw [show c + 2 + d + 1 = (c + (d + 2)) + 1 by omega, List.range'_succ, ← List.range'_append_1,
    show c + 2 - 2 = c by omega, show c + (d + 2) + 1 - (c + 2 + 1) = d by omega,
    show 1 + 1 + c = c + 2 by omega, List.range'_succ, List.range'_concat, Nat.one_mul,
    show c + 2 + 1 + d = c + (d + 2) + 1 by omega]

/-- **The shared seed's history** (see the file header). -/
theorem seedSharedL_hist (r1 r2 : w64) (h1 : 1 < uint.nat r1) (h12 : uint.nat r1 < uint.nat r2) :
    (seedSharedL r1 r2).hist = (List.range' 1 (uint.nat r2)).map (seedAt r1 r2) := by
  rw [range'_seedShared (uint.nat r1) (uint.nat r2) (by omega) h12]
  have hA : (List.range' 2 (uint.nat r1 - 2)).map (seedAt r1 r2) = padL [] 2 (uint.nat r1) := by
    unfold padL
    refine List.map_congr_left fun r hr => ?_
    rw [List.mem_range'_1] at hr
    simp only [seedAt, show r < uint.nat r1 by omega, ite_true]
  have hB : (List.range' (uint.nat r1 + 1) (uint.nat r2 - (uint.nat r1 + 1))).map (seedAt r1 r2) =
      padL [seedItem kA r1] (uint.nat r1 + 1) (uint.nat r2) := by
    unfold padL
    refine List.map_congr_left fun r hr => ?_
    rw [List.mem_range'_1] at hr
    simp only [seedAt, show ¬ r < uint.nat r1 by omega, show r < uint.nat r2 by omega, ite_true, ite_false]
  have h1' : seedAt r1 r2 1 = ⟨[], W64 1⟩ := by
    simp only [seedAt, show 1 < uint.nat r1 from h1, ite_true]; rfl
  have hr1 : seedAt r1 r2 (uint.nat r1) = ⟨[seedItem kA r1], r1⟩ := by
    simp only [seedAt, Nat.lt_irrefl, h12, ite_true, ite_false]; congr 1; word
  have hr2 : seedAt r1 r2 (uint.nat r2) = ⟨[seedItem kA r1, seedItem kB r2], r2⟩ := by
    simp only [seedAt, Nat.lt_irrefl, show ¬ uint.nat r2 < uint.nat r1 by omega, ite_false]
    congr 1; word
  have e1 : uint.nat (W64 1) + 1 = 2 := rfl
  simp only [List.map_cons, List.map_append, hA, hB, h1', hr1, hr2, seedSharedL, seedStepL, seedInitL,
    setItemL_seedA, setItemL_seedB, e1, List.append_assoc, List.cons_append,
    List.nil_append]
  rfl

theorem histN_seedShared (r1 r2 : w64) (h1 : 1 < uint.nat r1) (h12 : uint.nat r1 < uint.nat r2)
    (r : Nat) (hr0 : 1 ≤ r) (hr : r ≤ uint.nat r2) :
    histN (seedSharedL r1 r2).hist r = seedAt r1 r2 r := by
  rw [seedSharedL_hist r1 r2 h1 h12]
  have e : List.range' 1 (uint.nat r2) = List.range' 1 r ++ List.range' (1 + r) (uint.nat r2 - r) := by
    rw [List.range'_append_1]; congr 1; omega
  have e2 : List.range' 1 r = List.range' 1 (r - 1) ++ [r] := by
    have := List.range'_concat (s := 1) (n := r - 1) (step := 1)
    rw [show r - 1 + 1 = r by omega, Nat.one_mul, show 1 + (r - 1) = r by omega] at this
    exact this
  unfold histN
  rw [e, List.map_append, List.take_left' (by simp), e2, List.map_append, List.map_cons, List.map_nil,
    List.getLast?_concat]
  rfl

/-- The shared seed's stores: sorted, unannotated, their objects `itemOk` with revisions in `[1, r]`. -/
theorem seedAt_ok (r1 r2 : w64) (h1 : 1 < uint.nat r1) (r : Nat) (hr0 : 1 ≤ r) (hr : r ≤ uint.nat r2) :
    StOk (seedAt r1 r2 r) ∧ ∀ it ∈ (seedAt r1 r2 r).items,
      itemOk it.obj' ∧ 1 ≤ uint.nat it.obj'.ResourceVersion' ∧ uint.nat it.obj'.ResourceVersion' ≤ r := by
  unfold seedAt
  rw [seedItem_kA, seedItem_kB]
  split
  · exact ⟨⟨by simp [SortedI], by simp⟩, by simp⟩
  split
  · refine ⟨⟨by simp only [SortedI, List.map]; decide, fun it hit => ?_⟩, fun it hit => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; subst hit; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; subst hit
      exact ⟨itemOk_dA _, by simp; omega, by simp; omega⟩
  · refine ⟨⟨by simp only [SortedI, List.map]; decide, fun it hit => ?_⟩, fun it hit => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit; rcases hit with rfl | rfl <;> rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl
      · exact ⟨itemOk_dA _, by simp; omega, by simp; omega⟩
      · exact ⟨itemOk_dB _, by simp; omega, by simp; omega⟩

theorem seedAt_rv (r1 r2 : w64) (r : Nat) : (seedAt r1 r2 r).rv = W64 (r : Int) := by
  unfold seedAt; split <;> (try split) <;> rfl

/-- The changes of the shared seed's history: only the two seeds, each its object at its revision. -/
theorem seedAt_change (r1 r2 : w64) (_h1 : 1 < uint.nat r1) (h12 : uint.nat r1 < uint.nat r2)
    (r : Nat) (hr2 : 2 ≤ r) (hr : r ≤ uint.nat r2) (ch : Chg)
    (ho : changeAtL (seedAt r1 r2 (r - 1)).items (seedAt r1 r2 r).items r = some ch) :
    (∀ o, ch.cur = some o → uint.nat o.ResourceVersion' = r ∧ o.Annotated' = false) ∧
      ∀ o, ch.prev = some o → o.Annotated' = false := by
  unfold seedAt at ho
  rw [seedItem_kA, seedItem_kB] at ho
  by_cases ha : r < uint.nat r1
  · simp only [show r - 1 < uint.nat r1 by omega, ha, ite_true, changeAtL] at ho; cases ho
  by_cases hb : r < uint.nat r2
  · by_cases hc : r - 1 < uint.nat r1
    · have : r = uint.nat r1 := by omega
      subst this
      simp only [hc, ha, hb, ite_true, ite_false, changeAtL, Option.some.injEq] at ho; subst ho
      exact ⟨fun o h => by cases h; exact ⟨by simp, rfl⟩, fun o h => by cases h⟩
    · simp only [hc, ha, hb, show r - 1 < uint.nat r2 by omega, ite_true, ite_false, changeAtL_self] at ho
      cases ho
  · have : r = uint.nat r2 := by omega
    subst this
    simp only [show ¬ uint.nat r2 - 1 < uint.nat r1 by omega, show uint.nat r2 - 1 < uint.nat r2 by omega,
      ha, hb, ite_true, ite_false] at ho
    simp only [changeAtL, show ¬ go.GoStringLt kA kA from go.goStringLt_irrefl kA, decide_false,
      Bool.false_eq_true, ↓reduceIte, decide_true, Option.some.injEq] at ho
    subst ho
    exact ⟨fun o h => by cases h; exact ⟨by simp, rfl⟩, fun o h => by cases h⟩

/-- **The shared seed is a configuration `realCheck`'s pure core runs from** (see the file header). -/
theorem runOk_seedShared (r1 r2 : w64) (h1 : 1 < uint.nat r1) (h12 : uint.nat r1 < uint.nat r2)
    (h2 : uint.nat r2 < 2 ^ 63) : RunOk (seedSharedL r1 r2) := by
  have hlen : (seedSharedL r1 r2).hist.length = uint.nat r2 := by
    rw [seedSharedL_hist r1 r2 h1 h12]; simp
  have hst := seedSharedL_st r1 r2 h12
  have hrv : uint.nat (seedSharedL r1 r2).st.rv = uint.nat r2 := rfl
  have hall := seedAt_ok r1 r2 h1 (uint.nat r2) (by omega) (Nat.le_refl _)
  have hat : ∀ q : w64, 0 < uint.nat q → uint.nat q ≤ uint.nat r2 →
      histAtL (seedSharedL r1 r2).hist q = seedAt r1 r2 (uint.nat q) := fun q hq0 hq =>
    histN_seedShared r1 r2 h1 h12 (uint.nat q) hq0 hq
  have hN : ∀ r ≤ (seedSharedL r1 r2).hist.length, r = 0 ∨
      histN (seedSharedL r1 r2).hist r = seedAt r1 r2 r ∧ 1 ≤ r := by
    intro r hr
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inl h
    · exact Or.inr ⟨histN_seedShared r1 r2 h1 h12 r h (by omega), h⟩
  refine ⟨⟨?_, ?_, ?_, by rw [hrv]; omega, fun q hq0 hq => ?_⟩,
    ⟨by rw [hlen]; rfl, by unfold seedSharedL seedStepL; exact List.getLast?_concat, fun q hq0 hq => ?_⟩,
    fun r hr => ?_, ⟨fun r it hr hit => ?_, fun r ch hr2 hr ho => ?_⟩, by rw [hrv]; omega⟩
  · rw [hst]; exact hall.1
  · rw [hst]; exact fun it hit => (hall.2 it hit).1
  · rw [hst]
    refine rmWf_absR _ fun it hit => ?_
    rw [seedAt_rv]
    have := (hall.2 it hit).2.2
    word
  · rw [hrv] at hq; rw [hat q hq0 hq, seedAt_rv]; word
  · rw [hrv] at hq; rw [hat q hq0 hq]
    have := seedAt_ok r1 r2 h1 _ hq0 hq
    exact ⟨this.1, fun it hit => (this.2 it hit).1⟩
  · rcases hN r hr with rfl | ⟨e, h0⟩
    · simp [histN, zSt]
    · rw [e]; exact (seedAt_ok r1 r2 h1 r h0 (by omega)).1.1
  · rcases hN r hr with rfl | ⟨e, h0⟩
    · simp [histN, zSt] at hit
    · rw [e] at hit
      have := seedAt_ok r1 r2 h1 r h0 (by omega)
      exact ⟨(this.2 it hit).2.1, (this.2 it hit).2.2, this.1.2 it hit⟩
  · rw [histN_seedShared r1 r2 h1 h12 r (by omega) (by omega),
      histN_seedShared r1 r2 h1 h12 (r - 1) (by omega) (by omega)] at ho
    exact seedAt_change r1 r2 h1 h12 r hr2 (by omega) ch ho

/-- **A run of the driver's model** (`kSpec h0`, no foreign step): `SRun` with only `kSpec`'s silent
steps (`linkv.PReach`). The target of `noForeign_erase` (Handoff K8-2). -/
inductive PRun (h0 : HSt) : GCfg → List (Input × Output) → GCfg → Prop where
  | nil (c : GCfg) : PRun h0 c [] c
  | cons {c c₁ c₂ c' : GCfg} {x : Input} {y : Output} {ops : List (Input × Output)} :
      linkv.PReach (kSpec h0) c c₁ → linkv.PStep (kSpec h0) c₁ x (ansOf y) c₂ → PRun h0 c₂ ops c' →
      PRun h0 c ((x, y) :: ops) c'

/-- **A run of the driver's model is one its sequential model allows**: from a model state holding the
run's first configuration, `pSeq (kSpec h0)` runs the operations (as `(input, ansOf output)`) to a state
holding the last, if that state is closed under late effects. -/
theorem pRun_run {h0 : HSt} {c c' : GCfg} {xs : List (Input × Output)} (hr : PRun h0 c xs c') :
    ∀ (S : linkv.PSet HSt Input), S c → linkv.PSet.Closed (kSpec h0) S →
      ∃ S', github_com.anishathalye.porcupine.Theory.run (linkv.pSeq (kSpec h0)) S
        (xs.map fun p => (p.1, ansOf p.2)) = some S' ∧ S' c' := by
  induction hr with
  | nil c => exact fun S hS _ => ⟨S, rfl, hS⟩
  | cons hreach hstep _ ih =>
    intro S hS hcl
    obtain ⟨S1, e1, h1⟩ := linkv.pSeq_step_of_pstep (hcl _ _ hS hreach) hstep (.refl _)
    obtain ⟨S', e', h'⟩ := ih S1 h1 (by rw [linkv.pSeq_step_some e1]; exact linkv.ppost_closed _ _ _)
    refine ⟨S', ?_, h'⟩
    simp only [List.map_cons, github_com.anishathalye.porcupine.Theory.run, e1]
    exact e'

/-! ## Step 2: a failure-free run has no pending write -/

/-- **A failure-free history** (Go's `failureFree`, `failureFree.spec`'s post): no unary answer
`EOther` (error 4), no failed watch the driver did not skip. -/
def FailureFreeL (xs : List (Input × Output)) : Prop := ∀ p ∈ xs, okOut p.1 p.2 = true

/-- A step on a failure-free answer adds no pending write. -/
theorem pStep_pend_nil {h0 : HSt} {c c' : GCfg} {x : Input} {y : Output}
    (hs : linkv.PStep (kSpec h0) c x (ansOf y) c') (hok : okOut x y = true) (hp : c.pend = []) :
    c'.pend = [] := by
  generalize ha : ansOf y = a at hs
  cases hs with
  | ok => exact hp
  | errW _ ho =>
    exfalso
    have h4 : y.Err' = W64 4 := by
      unfold ansOf at ha; split at ha
      · assumption
      · cases ha
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    rw [okOut, if_neg hk, h4] at hok; simp at hok
  | errR => exact hp
  | obs => exact hp

/-- With no pending write, `kSpec`'s silent step changes nothing. -/
theorem pSilent_nil {h0 : HSt} {c c' : GCfg} (hs : linkv.PSilent (kSpec h0) c c') (hp : c.pend = []) :
    c' = c := by
  cases hs with
  | apply i hi => rw [hp] at hi; cases hi
  | perm q hq =>
    rw [hp] at hq
    rw [List.Perm.eq_nil hq]
    cases c; simp_all

theorem repeat_foreignL_succ (k : Nat) (h : HSt) :
    Nat.repeat foreignL k (foreignL h) = foreignL (Nat.repeat foreignL k h) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.repeat]; rw [ih]

/-- **Silent steps from no pending write are foreign revisions.** -/
theorem sReach_nil {h0 : HSt} {c c₁ : GCfg} (hr : SReach h0 c c₁) (hp : c.pend = []) :
    ∃ k, c₁ = ⟨Nat.repeat foreignL k c.st, []⟩ := by
  induction hr with
  | refl c => exact ⟨0, by cases c; simp_all [Nat.repeat]⟩
  | step hs _ ih =>
    cases hs with
    | pend _ hps =>
      have e := pSilent_nil hps hp
      subst e
      exact ih hp
    | foreign _ =>
      obtain ⟨k, hk⟩ := ih hp
      exact ⟨k + 1, by rw [hk, repeat_foreignL_succ]; rfl⟩

/-! ## Step 4's bound: an operation naming revisions up to `m` has its target at most `m` -/

theorem evMaxL_le (evs : List WEv) (m : Nat)
    (h : ∀ e ∈ evs, e.t < 4 → uint.nat e.o.ResourceVersion' ≤ m) : evMaxL evs ≤ m :=
  evMaxL_foldl_le m _ 0 (Nat.zero_le _) fun e he => by
    obtain ⟨he, ht⟩ := List.mem_filter.1 he
    exact h e he (by simpa using ht)

/-- **The target of an operation whose revisions are all at most `m`** (`OpAnchors` over `0, ..., m`,
`NoForeignOk`'s second half) is at most `m`, from any revision. -/
theorem targetL_le_anchors (x : Input) (y : Output) (rv m : Nat)
    (h1 : 1 ≤ m) (h : OpAnchors (List.range (m + 1)) x y) : targetL x y rv ≤ m := by
  obtain ⟨hmin, -, hw, hnw⟩ := h
  simp only [List.mem_range] at hmin hw hnw
  unfold targetL
  split
  · next h5 =>
    have hm := fun req (hq : parseRVD x.MinRV' = some req) => hmin (Or.inl h5) req hq
    split
    · omega
    · next hf =>
      have hwf : y.WFailed' = false := by
        cases hy' : y.WFailed' <;> simp_all
      split
      · omega
      · next evs hevs =>
        have hev := evMaxL_le evs m fun e he ht => by have := hw h5 hwf evs hevs e he ht; omega
        split
        · split
          · next req hreq => have := hm req hreq; omega
          · exact hev
        · exact hev
  · next h5 =>
    obtain ⟨hE, hL, hR, -, -⟩ := hnw h5
    split
    · omega
    split
    · omega
    next h0' =>
    have h0 : y.Err' = W64 0 := by simpa using h0'
    have hm := fun req (hq : parseRVD x.MinRV' = some req) =>
      hmin (Or.inr (by rw [h0]; decide)) req hq
    have hR' := hR h0
    split
    · split
      · omega
      · next req hreq =>
        split
        · have := hm req hreq; omega
        · omega
    split
    · split <;> omega
    · split
      · omega
      · next req hreq => have := hm req hreq; omega

/-! ## Step 3: no foreign revision below `m`

A successful write answers either the revision it writes (a write that changes the store) or the
revision of an item it finds (a no-op update). Items carry only revisions writes wrote (or the seed's),
so a revision passed by a foreign step is never a write's answer (`sRun_jr`); `NoForeignOk`'s first
half then leaves no foreign step below `m`. -/

/-- A step's items are its store's, or carry the new revision of a step that advanced it. -/
theorem mstepL_items (x : Input) (st : GSt) (it : item) (hi : it ∈ (mstepL x st).1.items) :
    it ∈ st.items ∨ ((mstepL x st).1.rv = st.rv + W64 1 ∧ it.obj'.ResourceVersion' = st.rv + W64 1) := by
  revert hi
  simp only [mstepL, mcreateL, mdeleteL, mupdateL]
  repeat' split
  all_goals
    intro h
    dsimp only at h ⊢
    first
    | exact Or.inl h
    | (unfold delItemL at h; exact Or.inl (List.mem_filter.1 h).1)
    | (rcases setItemL_mem _ _ _ h with rfl | h
       · exact Or.inr ⟨rfl, rfl⟩
       · exact Or.inl h)

/-- A step that advances the store is a successful write answering the new revision. -/
theorem mstepL_bump (x : Input) (st : GSt) (h : (mstepL x st).1.rv ≠ st.rv) :
    isWriteL x = true ∧ (mstepL x st).2.Err' = W64 0 ∧ (mstepL x st).2.RV' = (mstepL x st).1.rv := by
  revert h
  simp only [mstepL, mcreateL, mdeleteL, mupdateL]
  repeat' split
  all_goals
    simp only [notFoundL, errOutL, existsL, invalidObjL, invalidOutL, rejectedL, objOutL]
    first
    | (intro h; exact absurd rfl h)
    | (intro; refine ⟨?_, ?_, ?_⟩ <;> simp_all [isWriteL])

/-- A successful write that keeps the store's revision answers an item's revision. -/
theorem mstepL_keep (x : Input) (st : GSt) (hw : isWriteL x = true)
    (h0 : (mstepL x st).2.Err' = W64 0) (h : (mstepL x st).1.rv = st.rv) :
    ∃ it ∈ st.items, (mstepL x st).2.RV' = it.obj'.ResourceVersion' := by
  revert h0 h
  simp only [mstepL, mcreateL, mdeleteL, mupdateL]
  repeat' split
  all_goals
    simp only [notFoundL, errOutL, existsL, invalidObjL, invalidOutL, rejectedL, objOutL]
    first
    | (intro h; exact absurd h (by decide))
    | (intro _ h; exfalso; revert h; word)
    | (intro _ _; exact ⟨_, lookupL_mem _ _ ‹(lookupL _ _).2 = true ∧ _›.1, rfl⟩)
    | (exfalso; simp_all [isWriteL])

/-- **A revision no item carries**, at most the store's: `r` stays so through every step. -/
def JR (r : Nat) (st : GSt) : Prop :=
  r ≤ uint.nat st.rv ∧ ∀ it ∈ st.items, uint.nat it.obj'.ResourceVersion' ≠ r

/-- `JR` is kept by a step, whose successful write does not answer `r`. -/
theorem jr_step (r : Nat) (x : Input) (st : GSt) (hj : JR r st) (hb : uint.nat st.rv + 1 < 2 ^ 64) :
    JR r (mstepL x st).1 ∧
      (isWriteL x = true → (mstepL x st).2.Err' = W64 0 → uint.nat (mstepL x st).2.RV' ≠ r) := by
  have hs : uint.nat (st.rv + W64 1) = uint.nat st.rv + 1 := by word
  have hj1 := hj.1
  by_cases he : (mstepL x st).1.rv = st.rv
  · refine ⟨⟨by rw [he]; exact hj1, fun it hi => ?_⟩, fun hw h0 => ?_⟩
    · rcases mstepL_items x st it hi with hi | ⟨hr, -⟩
      · exact hj.2 it hi
      · exfalso; rw [hr] at he; revert he; word
    · obtain ⟨it, hi, hrv⟩ := mstepL_keep x st hw h0 he
      rw [hrv]; exact hj.2 it hi
  · obtain ⟨-, -, hrv⟩ := mstepL_bump x st he
    have hr1 : (mstepL x st).1.rv = st.rv + W64 1 := (mstepL_rv x st).resolve_left he
    refine ⟨⟨by rw [hr1, hs]; omega, fun it hi => ?_⟩, fun _ _ => ?_⟩
    · rcases mstepL_items x st it hi with hi | ⟨-, hr⟩
      · exact hj.2 it hi
      · rw [hr, hs]; omega
    · rw [hrv, hr1, hs]; omega

/-- `kstepL` is `mstepL` on the store, or a non-write that changes nothing. -/
theorem kstepL_parts (x : Input) (h : HSt) :
    ((kstepL x h).1.st = (mstepL x h.st).1 ∧ (kstepL x h).2 = (mstepL x h.st).2) ∨
      (isWriteL x = false ∧ (kstepL x h).1 = h) := by
  unfold kstepL
  split
  · next h4 => right; exact ⟨by simp [isWriteL, h4], rfl⟩
  · left; exact ⟨advanceL_items _ _, rfl⟩

theorem kjr_step (r : Nat) (x : Input) (h : HSt) (hj : JR r h.st) (hb : uint.nat h.st.rv + 1 < 2 ^ 64) :
    JR r (kstepL x h).1.st ∧
      (isWriteL x = true → (kstepL x h).2.Err' = W64 0 → uint.nat (kstepL x h).2.RV' ≠ r) := by
  rcases kstepL_parts x h with ⟨e1, e2⟩ | ⟨hw, e⟩
  · rw [e1, e2]; exact jr_step r x h.st hj hb
  · rw [e]; exact ⟨hj, fun h' => by rw [hw] at h'; cases h'⟩

theorem ansOf_ok {y z : Output} (h : ansOf y = .ok z) : z = y ∧ y.Err' ≠ W64 4 := by
  unfold ansOf at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, ‹_›⟩

/-- `JR` is kept by an operation's step, whose successful write does not answer `r`. -/
theorem pStep_jr {h0 : HSt} {c₁ c₂ : GCfg} {x : Input} {y : Output} {r : Nat}
    (hs : linkv.PStep (kSpec h0) c₁ x (ansOf y) c₂) (hj : JR r c₁.st.st) (hb : NoWrap c₁) :
    JR r c₂.st.st ∧ (isWriteL x = true → y.Err' = W64 0 → uint.nat y.RV' ≠ r) := by
  generalize ha : ansOf y = a at hs
  cases hs with
  | ok ho =>
    obtain ⟨hy, -⟩ := ansOf_ok ha
    subst hy
    exact kjr_step r x c₁.st hj hb
  | errW _ _ =>
    have h4 := (ansOf_err y).1 ha
    exact ⟨hj, fun _ h0 => by rw [h4] at h0; exact absurd h0 (by decide)⟩
  | errR _ _ =>
    have h4 := (ansOf_err y).1 ha
    exact ⟨hj, fun _ h0 => by rw [h4] at h0; exact absurd h0 (by decide)⟩
  | obs o hob _ =>
    have hk : x.Kind' = W64 5 := by simpa using hob
    exact ⟨hj, fun hw => by simp [isWriteL, hk] at hw⟩

theorem sReach_jr {h0 : HSt} {c c₁ : GCfg} {r : Nat} (hr : SReach h0 c c₁) (hj : JR r c.st.st) :
    JR r c₁.st.st := by
  induction hr with
  | refl => exact hj
  | step hs _ ih =>
    apply ih
    cases hs with
    | pend hnw hps =>
      cases hps with
      | apply i _ => exact (kjr_step r i _ hj hnw).1
      | perm _ _ => exact hj
    | foreign hnw =>
      have hj1 := hj.1
      exact ⟨by rw [foreignL_rv _ hnw]; omega, fun it hi => hj.2 it hi⟩

/-- **No successful write of a run answers a revision `JR` excludes.** -/
theorem sRun_jr {h0 : HSt} {c c' : GCfg} {xs : List (Input × Output)} {r : Nat}
    (hr : SRun h0 c xs c') (hj : JR r c.st.st) :
    ∀ p ∈ xs, isWriteL p.1 = true → p.2.Err' = W64 0 → uint.nat p.2.RV' ≠ r := by
  induction hr with
  | nil => intro p hp; cases hp
  | cons hre hnw hps _ ih =>
    obtain ⟨h2, ha⟩ := pStep_jr hps (sReach_jr hre hj) hnw
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ha
    · exact ih h2 p hp

/-- From no pending write, silent steps do nothing or start with a foreign step. -/
theorem sReach_first {h0 : HSt} {c c₁ : GCfg} (hr : SReach h0 c c₁) (hp : c.pend = []) :
    c₁ = c ∨ (NoWrap c ∧ SReach h0 ⟨foreignL c.st, []⟩ c₁) := by
  induction hr with
  | refl => exact Or.inl rfl
  | step hs hr' ih =>
    cases hs with
    | pend hnw hps =>
      have e := pSilent_nil hps hp
      subst e
      exact ih hp
    | foreign hnw =>
      right; rw [hp] at hr'; exact ⟨hnw, hr'⟩

/-! ## The erasure -/

theorem settleL_nil {A : List Nat} {e d : GCfg} (h : SettleL A e d) (hp : e.pend = []) : d = e := by
  cases h with
  | refl => rfl
  | drop _ hi => rw [hp] at hi; simp at hi
  | land _ _ hi => rw [hp] at hi; simp at hi

theorem pStep_hk {h0 : HSt} {g g₂ : GCfg} {x : Input} {y : Output}
    (hs : linkv.PStep (kSpec h0) g x (ansOf y) g₂) : x.Kind' = W64 5 → y.Err' ≠ W64 4 := by
  intro hk
  generalize ha : ansOf y = a at hs
  cases hs with
  | ok ho => simp [hk] at ho
  | errW _ ho => simp [hk] at ho
  | errR _ ho => simp [hk] at ho
  | obs o _ _ => exact (ansOf_ok ha).2

/-- An operation's step is from a configuration at least at its target. -/
theorem pStep_target {h0 : HSt} {g₁ g₂ : GCfg} {x : Input} {y : Output}
    (hs : linkv.PStep (kSpec h0) g₁ x (ansOf y) g₂)
    (hit : ∀ it ∈ g₁.st.st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat g₁.st.st.rv)
    (hnw : NoWrap g₁) (r : Nat) : targetL x y r ≤ uint.nat g₁.st.st.rv := by
  generalize ha : ansOf y = a at hs
  cases hs with
  | ok ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    obtain ⟨hy, -⟩ := ansOf_ok ha
    exact kstepL_target x y g₁.st hit hnw hk hy.symm r
  | errW _ ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    rw [targetL_err x y r hk ((ansOf_err y).1 ha)]; exact Nat.zero_le _
  | errR _ ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    rw [targetL_err x y r hk ((ansOf_err y).1 ha)]; exact Nat.zero_le _
  | obs o hob hoo =>
    have hk : x.Kind' = W64 5 := by simpa using hob
    obtain ⟨hy, -⟩ := ansOf_ok ha
    subst hy
    exact watchOkL_target x o g₁.st hk r hoo

theorem pStep_det {h0 : HSt} {c c₁ c₂ : GCfg} {x : Input} {a : linkv.Ans Output}
    (h1 : linkv.PStep (kSpec h0) c x a c₁) (h2 : linkv.PStep (kSpec h0) c x a c₂) : c₁ = c₂ := by
  cases h1 <;> cases h2 <;> simp_all

/-- An operation's step keeps the revision, a successful write then answering an item's; or advances
it by one, a successful write answering the new revision. -/
theorem pStep_rv {h0 : HSt} {c c₂ : GCfg} {x : Input} {y : Output}
    (hs : linkv.PStep (kSpec h0) c x (ansOf y) c₂) (hb : NoWrap c) :
    (c₂.st.st.rv = c.st.st.rv ∧ (isWriteL x = true → y.Err' = W64 0 →
        ∃ it ∈ c.st.st.items, y.RV' = it.obj'.ResourceVersion')) ∨
      (uint.nat c₂.st.st.rv = uint.nat c.st.st.rv + 1 ∧ isWriteL x = true ∧ y.Err' = W64 0 ∧
        y.RV' = c₂.st.st.rv) := by
  generalize ha : ansOf y = a at hs
  cases hs with
  | ok ho =>
    obtain ⟨hy, -⟩ := ansOf_ok ha
    subst hy
    show ((kstepL x c.st).1.st.rv = _ ∧ _) ∨ (uint.nat (kstepL x c.st).1.st.rv = _ ∧ _)
    rcases kstepL_parts x c.st with ⟨e1, e2⟩ | ⟨hw, e⟩
    · rw [e1, e2]
      by_cases he : (mstepL x c.st.st).1.rv = c.st.st.rv
      · exact Or.inl ⟨he, fun hw h0 => mstepL_keep x _ hw h0 he⟩
      · obtain ⟨hw, h0, hrv⟩ := mstepL_bump x _ he
        have hr1 := (mstepL_rv x c.st.st).resolve_left he
        have hb' : uint.nat c.st.st.rv + 1 < 2 ^ 64 := hb
        refine Or.inr ⟨by rw [hr1]; word, hw, h0, hrv⟩
    · rw [e]; exact Or.inl ⟨rfl, fun h' => by rw [hw] at h'; cases h'⟩
  | errW _ _ =>
    have h4 := (ansOf_err y).1 ha
    exact Or.inl ⟨rfl, fun _ h0 => by rw [h4] at h0; exact absurd h0 (by decide)⟩
  | errR _ _ =>
    have h4 := (ansOf_err y).1 ha
    exact Or.inl ⟨rfl, fun _ h0 => by rw [h4] at h0; exact absurd h0 (by decide)⟩
  | obs o hob _ =>
    have hk : x.Kind' = W64 5 := by simpa using hob
    exact Or.inl ⟨rfl, fun hw => by simp [isWriteL, hk] at hw⟩

theorem nfWriteRV_some {f v : w64} {p : Input × Output} (h : nfWriteRV f p = some v) :
    isWriteL p.1 = true ∧ p.2.Err' = W64 0 ∧ uint.nat f < uint.nat p.2.RV' ∧ p.2.RV' = v := by
  unfold nfWriteRV at h
  split at h
  · next hc => cases h; exact ⟨hc.1, hc.2.1, hc.2.2, rfl⟩
  · cases h

theorem nfWriteRV_of {f : w64} {p : Input × Output} (hw : isWriteL p.1 = true) (h0 : p.2.Err' = W64 0)
    (hf : uint.nat f < uint.nat p.2.RV') : nfWriteRV f p = some p.2.RV' := by
  unfold nfWriteRV; rw [if_pos ⟨hw, h0, hf⟩]

/-- Every revision in `(lo, m]` is a successful write's answer in `xs`. -/
def CovL (f : w64) (lo m : Nat) (xs : List (Input × Output)) : Prop :=
  ∀ v : w64, lo < uint.nat v → uint.nat v ≤ m → ∃ p ∈ xs, nfWriteRV f p = some v

theorem covL_step {f : w64} {lo lo' m : Nat} {x : Input} {y : Output} {rest : List (Input × Output)}
    (hc : CovL f lo m ((x, y) :: rest)) (hlo : lo ≤ lo')
    (hb : ∀ v, nfWriteRV f (x, y) = some v → uint.nat v ≤ lo') : CovL f lo' m rest := by
  intro v h1 h2
  obtain ⟨p, hp, hv⟩ := hc v (by omega) h2
  rcases List.mem_cons.1 hp with rfl | hp
  · have := hb v hv; omega
  · exact ⟨p, hp, hv⟩

/-- **The erasure's induction.** The search's configuration `e` (related to the cluster's `g` by
`CRel`, no pending write) is either the cluster's own, below `m`, every revision up to `m` still to be
answered by a write (`CovL`): then no foreign step comes before the next operation (`sRun_jr`); or at
`m`, where every operation's target is (`targetL_le_anchors`) and no write advances it. Either way the
search's step (`CRel.op`) is from `e` itself, a step of `kSpec` (`stepL_sound`). -/
theorem erase_go {h0 : HSt} {f : w64} {m : Nat} (hn0 : 1 ≤ uint.nat h0.st.rv) (hfm : uint.nat f ≤ m)
    (hm1 : 1 ≤ m) {g : GCfg} {xs : List (Input × Output)} {g' : GCfg} (hr : SRun h0 g xs g') :
    FailureFreeL xs → (∀ p ∈ xs, OpAnchors (List.range (m + 1)) p.1 p.2) →
    (∀ p ∈ xs, ∀ v, nfWriteRV f p = some v → uint.nat v ≤ m) →
    ∀ e, CRel (List.range (m + 1)) (uint.nat h0.st.rv) e g → e.pend = [] →
    ((e = g ∧ uint.nat f ≤ uint.nat g.st.st.rv ∧ uint.nat g.st.st.rv < m ∧
        CovL f (uint.nat g.st.st.rv) m xs) ∨ uint.nat e.st.st.rv = m) →
    ∃ e'', PRun h0 e xs e'' := by
  induction hr with
  | nil c => intro _ _ _ e _ _ _; exact ⟨e, .nil e⟩
  | @cons g g₁ g₂ g' x y rest hre hnw hps _ ih =>
    intro hff hanc hle e hc hep hph
    have hxy : (x, y) ∈ (x, y) :: rest := List.mem_cons_self
    have hgp : g.pend = [] := by have := hc.perm; rw [hep] at this; exact this.symm.eq_nil
    obtain ⟨d, hsd, hcd⟩ := CRel.reach hre hc
    have hde : d = e := settleL_nil hsd hep
    subst hde
    obtain ⟨ρ, W, hh⟩ := hcd.rel
    -- phase 1: no foreign step before this operation
    have hph1 : (d = g₁ ∧ uint.nat f ≤ uint.nat g₁.st.st.rv ∧ uint.nat g₁.st.st.rv < m ∧
        CovL f (uint.nat g₁.st.st.rv) m ((x, y) :: rest)) ∨ uint.nat d.st.st.rv = m := by
      rcases hph with ⟨rfl, hf, hlt, hcov⟩ | hm
      · rcases sReach_first hre hgp with rfl | ⟨hnw0, hre'⟩
        · exact Or.inl ⟨rfl, hf, hlt, hcov⟩
        · exfalso
          obtain ⟨ρ0, W0, hh0⟩ := hc.rel
          have hb0 : uint.nat d.st.st.rv + 1 < 2 ^ 64 := hnw0
          have hj : JR (uint.nat d.st.st.rv + 1) (foreignL d.st).st :=
            ⟨Nat.le_of_eq (foreignL_rv _ hnw0).symm, fun it hi => by have := hh0.items_le it hi; omega⟩
          have hno := sRun_jr (SRun.cons hre' hnw hps ‹_›) hj
          have hv : uint.nat (W64 ((uint.nat d.st.st.rv + 1 : Nat) : Int)) = uint.nat d.st.st.rv + 1 := by
            word
          obtain ⟨p, hp, hpv⟩ := hcov (W64 ((uint.nat d.st.st.rv + 1 : Nat) : Int)) (by rw [hv]; omega)
            (by rw [hv]; omega)
          obtain ⟨hw, h0, -, hrv⟩ := nfWriteRV_some hpv
          exact hno p hp hw h0 (by rw [hrv, hv])
      · exact Or.inr hm
    have tb : targetL x y (uint.nat d.st.st.rv) ≤ uint.nat d.st.st.rv := by
      rcases hph1 with ⟨rfl, -⟩ | hm
      · exact pStep_target hps (fun it hi => hh.items_le it hi) hnw _
      · rw [hm]; exact targetL_le_anchors x y _ m hm1 (hanc _ hxy)
    obtain ⟨e', ⟨d', hsd', he'⟩, hc'⟩ := CRel.op hn0 hc hre hnw hps (hanc _ hxy)
    have hd' : d' = d := settleL_nil hsd' hep
    subst hd'
    rw [skipToL_le _ _ tb] at he'
    have hpe : linkv.PStep (kSpec h0) d' x (ansOf y) e' := stepL_sound d' x y (pStep_hk hps) e' he'
    have hep' := pStep_pend_nil hpe (hff _ hxy) hep
    have hle' : ∀ v, nfWriteRV f (x, y) = some v → uint.nat v ≤ m := hle _ hxy
    obtain ⟨e'', hrun⟩ := ih (fun p hp => hff p (List.mem_cons_of_mem _ hp))
      (fun p hp => hanc p (List.mem_cons_of_mem _ hp)) (fun p hp => hle p (List.mem_cons_of_mem _ hp))
      e' hc' hep' (by
        rcases hph1 with ⟨rfl, hf, hlt, hcov⟩ | hm
        · have e2 : e' = g₂ := pStep_det hpe hps
          subst e2
          have hb : uint.nat d'.st.st.rv + 1 < 2 ^ 64 := hnw
          rcases pStep_rv hps hnw with ⟨hrv, hans⟩ | ⟨hrv, hw, hz, hry⟩
          · rw [hrv]
            refine Or.inl ⟨rfl, hf, hlt, covL_step hcov (Nat.le_refl _) fun v hv => ?_⟩
            obtain ⟨hw, hz, -, rfl⟩ := nfWriteRV_some hv
            obtain ⟨it, hi, hit⟩ := hans hw hz
            rw [hit]; exact hh.items_le it hi
          · have hm' := hle' _ (nfWriteRV_of (p := (x, y)) hw hz (by rw [hry, hrv]; omega))
            rw [hry, hrv] at hm'
            have hcs := covL_step hcov (Nat.le_succ _) fun v hv => by
              obtain ⟨-, -, -, rfl⟩ := nfWriteRV_some hv
              rw [hry, hrv]; exact Nat.le_refl _
            replace hcs : CovL f (uint.nat e'.st.st.rv) m rest := by rw [hrv]; exact hcs
            by_cases hlt' : uint.nat e'.st.st.rv < m
            · exact Or.inl ⟨rfl, by omega, hlt', hcs⟩
            · exact Or.inr (by omega)
        · right
          have hb : uint.nat d'.st.st.rv + 1 < 2 ^ 64 := by
            have := hh.le; have : uint.nat g₁.st.st.rv + 1 < 2 ^ 64 := hnw; omega
          rcases pStep_rv hpe hb with ⟨hrv, -⟩ | ⟨hrv, hw, hz, hry⟩
          · rw [hrv]; exact hm
          · exfalso
            have hm' := hle' _ (nfWriteRV_of (p := (x, y)) hw hz (by rw [hry, hrv]; omega))
            rw [hry, hrv] at hm'
            omega)
    exact ⟨e'', .cons (.refl _) hpe hrun⟩

/-- **Foreign erasure**: a failure-free run of the semantic model from the seeded store `h0` (K4's
seed premises, `FullComplete`'s), whose history shows no foreign revision (`NoForeignOk`), is a run of
the driver's model `kSpec h0` (no foreign step): the foreign steps all come after the last write
(`erase_go`'s first phase) and the operations after it answer as at `m` (`CRel.op`). -/
theorem noForeign_erase (h0 : HSt) (xs : List (Input × Output)) (c' : GCfg) (m : w64)
    (hlen : h0.hist.length = uint.nat h0.st.rv) (hlast : h0.hist.getLast? = some h0.st)
    (hseed : ∀ g ∈ h0.hist, ∀ it ∈ g.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat h0.st.rv)
    (hnf : NoForeignOk h0.st.rv xs m) (hff : FailureFreeL xs) (hr : SRun h0 ⟨h0, []⟩ xs c') :
    ∃ c'', PRun h0 ⟨h0, []⟩ xs c'' := by
  have hn0 : 1 ≤ uint.nat h0.st.rv := by
    rw [← hlen]
    cases hh : h0.hist with
    | nil => rw [hh] at hlast; cases hlast
    | cons _ _ => simp
  obtain ⟨M, hM⟩ : ∃ M, M = max (uint.nat m) (uint.nat h0.st.rv) := ⟨_, rfl⟩
  have hA : ∀ p ∈ xs, OpAnchors (List.range (M + 1)) p.1 p.2 := fun p hp =>
    opAnchors_mono (hnf.2.2 p hp) fun a ha => by simp only [List.mem_range] at ha ⊢; omega
  have hle : ∀ p ∈ xs, ∀ v, nfWriteRV h0.st.rv p = some v → uint.nat v ≤ M := fun p hp v hv => by
    have := ((hnf.1 v).2 ⟨p, hp, hv⟩).2; omega
  have hinit : CRel (List.range (M + 1)) (uint.nat h0.st.rv) ⟨h0, []⟩ ⟨h0, []⟩ :=
    ⟨⟨id, [], HRel.init h0 hlen hlast hseed⟩, List.Perm.refl _, by simp, by simp⟩
  refine erase_go hn0 (by omega) (by omega) hr hff hA hle _ hinit rfl ?_
  by_cases hfm : uint.nat h0.st.rv < uint.nat m
  · exact Or.inl ⟨rfl, Nat.le_refl _, by dsimp only; omega, fun v h1 h2 => (hnf.1 v).1 ⟨h1, by omega⟩⟩
  · exact Or.inr (by show uint.nat h0.st.rv = M; omega)

end pure

end k8s_dist
end EtcdGrove
end Perennial
