/-
Helper lemmas of the executor's proofs: the stack's truncation, the empty search state.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof tarjan

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-! ## Pure -/

/-- The search state `findSCC` starts with. -/
def St.init : St InstId := ⟨[], [], fun _ => none, id, 1⟩

theorem TInv_init (g : Gr InstId) : TInv g St.init := by
  constructor <;> simp [St.init, St.vis]

theorem VisCount_init : VisCount St.init := ⟨[], List.nodup_nil, by simp [St.init, St.vis], rfl, by simp⟩

/-- No active call: the stack is empty (a finished node's parent is below it, on the stack). -/
theorem TInv_noActive {g : Gr InstId} {t : St InstId} (h : TInv g t) (hA : t.A = []) : t.S = [] := by
  have : ∀ k, ∀ x ∈ t.S, t.num x = k → False := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro x hx hk
      obtain ⟨-, hpS, hpn, -⟩ := h.fin x hx (by rw [hA]; simp)
      exact ih _ (by omega) _ hpS rfl
  rcases hS : t.S with _ | ⟨x, T⟩
  · rfl
  · exact (this _ x (by rw [hS]; simp) rfl).elim

/-- The ids of the rows: `q < N`, `i < M`. -/
def allIds (N M : Nat) : List InstId := (List.range N).flatMap (fun q => (List.range M).map (⟨q, ·⟩))

theorem allIds_length (N M : Nat) : (allIds N M).length = N * M := by
  induction N with
  | zero => simp [allIds]
  | succ N ih =>
    unfold allIds at *
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [Nat.succ_mul]

theorem mem_allIds (N M : Nat) (x : InstId) (hq : x.q < N) (hi : x.i < M) : x ∈ allIds N M := by
  unfold allIds
  rw [List.mem_flatMap]
  exact ⟨x.q, List.mem_range.mpr hq, List.mem_map.mpr ⟨x.i, List.mem_range.mpr hi, rfl⟩⟩

/-- The counter stays small (no overflow of `*index`, nor of the stack's `2*l`). -/
theorem visCount_bound {t : St InstId} (h : VisCount t) : t.n ≤ nR * MAX_INSTANCE + 1 := by
  obtain ⟨V, hnd, -, hn, hb⟩ := h
  have := hnd.length_le_of_subset (l₂ := allIds nR MAX_INSTANCE)
    (fun x hx => mem_allIds _ _ x (hb x hx).1 (hb x hx).2)
  rw [allIds_length] at this
  omega

theorem stack_le_n {g : Gr InstId} {t : St InstId} (hT : TInv g t) (h : VisCount t) :
    t.S.length + 1 ≤ t.n := by
  obtain ⟨V, hnd, hV, hn, -⟩ := h
  have := hT.nodup.length_le_of_subset (l₂ := V) (fun x hx => (hV x).mp (hT.onS x hx).1)
  omega

theorem push_vis {t : St InstId} {v x : InstId} : (t.push v).vis x ↔ x = v ∨ t.vis x := by
  unfold St.vis St.push; by_cases h : x = v <;> simp [h]

theorem push_visCount {t : St InstId} {v : InstId} (h : VisCount t) (hv : ¬ t.vis v)
    (hq : v.q < nR) (hi : v.i < MAX_INSTANCE) : VisCount (t.push v) := by
  obtain ⟨V, hnd, hV, hn, hb⟩ := h
  refine ⟨V ++ [v], ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hnd, by simp, fun a ha b hb' hab => by simp at hb'; subst hb'; subst hab; exact hv ((hV a).mpr ha)⟩
  · intro x; rw [push_vis, hV x]; simp only [List.mem_append, List.mem_singleton]; exact Or.comm
  · show t.n + 1 = _; simp [hn]
  · intro x hx; simp at hx; rcases hx with hx | rfl
    · exact hb x hx
    · exact ⟨hq, hi⟩

theorem push_ext {g : Gr InstId} {t : St InstId} {v : InstId} (hv : ¬ t.vis v) :
    Ext g t g (t.push v) := by
  refine ⟨⟨[v], rfl⟩, fun x hx => ?_, fun _ h => h, rfl, fun x hx => ?_⟩
  · have : x ≠ v := fun e => hv (e ▸ hx)
    simp [St.push, this]
  · have : x ≠ v := fun e => hv (e ▸ hx)
    simp [St.push, this]

theorem push_winv {g : Gr InstId} {t : St InstId} (h : TInv g t) (v : InstId) :
    WInv g (t.push v) := by
  intro x hx hne
  show x ∈ t.S ++ [v]
  rcases push_vis.mp hx with rfl | hx
  · simp
  · exact List.mem_append_left _ (h.visS x hx hne)

/-- The state of `strongconnect(v)`'s edge loops (from the caller's `σ`, `t`): the search state
`tc` over `σc`, `v` the innermost active call, every edge of `v` to a target `B`-before the loop
position handled. -/
structure LoopOk (σ : RState) (t : St InstId) (v : InstId) (σc : RState) (tc : St InstId)
    (B : InstId → Prop) : Prop where
  rel : ExRel σ σc
  wf : ExecWf σc
  ib : instBounds σc.inst
  cnt : VisCount tc
  ext : Ext (gr σ) t (gr σc) tc
  n : t.n + 1 ≤ tc.n
  inv : TInv (gr σc) tc
  act : tc.A = t.A ++ [v]
  ixv : ∃ lv, tc.ix v = some (t.n, lv)
  parv : tc.par v = t.A.getLast?.getD v
  stk : ∃ T, tc.S = t.S ++ v :: T
  done : ∀ y, σc.depEdge v y → B y → Done (gr σc) tc v y

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- `s[0:k]`: the prefix, the rest absorbed into the capacity. -/
theorem slice_trunc (s : GoSlice) (xs : List Loc) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len) :
    (s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) : IProp GF) ⊢
      slice.slice s Loc (W64 0) k ↦* xs.take (sint.nat k) ∗
        ownSliceCap Loc (slice.slice s Loc (W64 0) k) (DFrac.own 1) := by
  iintro ⟨Hs, Hcap⟩
  ihave ⟨-, Hpre, Hrest⟩ := (ownSlice_slice (W64 0) k s (DFrac.own 1) xs
    ⟨by decide, hk.1, hk.2⟩).1 $$ Hs
  ihave Hcap := ownSlice_slice_absorb_capacity s _ (W64 0) k ⟨by decide, hk.1, hk.2⟩ $$ [Hrest Hcap]
  · iframe
  iframe Hcap
  have : subslice (sint.nat (W64 0)) (sint.nat k) xs = xs.take (sint.nat k) := by
    simp only [subslice]; rw [show sint.nat (W64 0) = 0 by rfl, List.drop_zero]
  rw [this]; iexact Hpre

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
