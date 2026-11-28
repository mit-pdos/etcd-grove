/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-1/K8-2: the shared seed is one `realCheck` runs from (`notes/k8s-dist-k8-scope.md` §2)

- `seedAt r1 r2 r`: the store of the shared seed's history (`seedSharedL r1 r2`, `SeedShared`/`SeededAt`)
  at revision `r`: empty below `r1`, the first seed from `r1` to below `r2`, both seeds at `r2`;
- `seedSharedL_hist`: that history is `seedAt` at `1, ..., r2`;
- `runOk_seedShared`: for `1 < r1 < r2 < 2^63`, `RunOk (seedSharedL r1 r2)`, what `realCheck`'s pure core
  (`realCheck_pure`) takes of the configuration it starts from (`runOk_g0s`'s generalization: the
  driver's seed is `r1 = 2`, `r2 = 3`; the padded stores between them are the foreign revisions).

`noForeign_erase` (a run of the semantic model showing no foreign revision is one of `kSpec`) is not
here yet: Handoff K8-2.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedSharedDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealB4
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedRename
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedComplete
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS

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

end pure

end k8s_dist
end EtcdGrove
end Perennial
