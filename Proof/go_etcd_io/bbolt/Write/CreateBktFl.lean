/-
U7j (`notes/bbolt-proof-plan.md`): **the exclusive part's `flViewU` across `CreateBucket`'s put**
(the review's U1, as `Write/FlViewU` for `Put`): the new root entry is the empty inline bucket,
which covers no slot (`emptyBktVal_noHas`), and the root's other bucket entries are kept
(`rootEnts_filter_ne`); the logical trees' positions and extents are unchanged (a leaf's entries
only). `lCovers_congrB`/`covU_congrB`: `lCovers_congr`/`covU_congr` with the root entries compared
only where they cover; `flViewU_createPut` on `withWs`, then on the node record (`setNode`, the
same page id and leaf flag: `flViewU_setNode_of_withWs`, the second half of U7i's
`flViewU_setNode`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.FlViewU
public import Proof.go_etcd_io.bbolt.Write.CreateBktData
public import Proof.go_etcd_io.bbolt.Write.CreateBktVal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section createbktfl
variable [GooseExts]

/-- **The cover from its parts**, the root entries compared where they cover. -/
theorem lCovers_congrB (X X' : WX) (hv : X'.v = X.v)
    (hroot : ∀ n v s, ((n, v) ∈ rootEnts X' ∧ bucketCovers X.v.pages v s) ↔
      ((n, v) ∈ rootEnts X ∧ bucketCovers X.v.pages v s))
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hext : ∀ c, (X.t.bs !! c).isSome → X'.extents c = X.extents c) :
    ∀ s, lCovers X' s ↔ lCovers X s := by
  intro s
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  unfold lCovers
  rw [hv]
  simp only [hbkt]
  constructor
  · rintro (⟨c, e, hc, he, h1⟩ | ⟨n, v, h1, h2, h3⟩)
    · have hc' := (hne c).1 hc
      rw [hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · obtain ⟨h1', -⟩ := (hroot n v s).1 ⟨h1, h3⟩
      exact Or.inr ⟨n, v, h1', h2, h3⟩
  · rintro (⟨c, e, hc, he, h1⟩ | ⟨n, v, h1, h2, h3⟩)
    · have hc' := (hne c).2 hc
      rw [← hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · obtain ⟨h1', -⟩ := (hroot n v s).2 ⟨h1, h3⟩
      exact Or.inr ⟨n, v, h1', h2, h3⟩

/-- **`covU` from its parts**, the root entries compared where they cover. -/
theorem covU_congrB (X X' : WX) (hv : X'.v = X.v)
    (hroot : ∀ n v s, ((n, v) ∈ rootEnts X' ∧ bucketCovers X.v.pages v s) ↔
      ((n, v) ∈ rootEnts X ∧ bucketCovers X.v.pages v s))
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hpos : ∀ c, (X.t.bs !! c).isSome → X'.positions c = X.positions c)
    (hpe : ∀ c pid, (X.t.bs !! c).isSome → X'.posExtent c pid = X.posExtent c pid)
    (h : covU X) : covU X' := by
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  have hsome : ∀ c, X.t.bs !! c ≠ none → (X.t.bs !! c).isSome := by
    intro c hc; cases e : X.t.bs !! c <;> simp_all
  have hcw : ∀ s c, coverW X' s c → coverW X s c := by
    intro s c hc
    cases c with
    | pos bl pid =>
      obtain ⟨h1, h2, e, h3, h4⟩ := hc
      have h1' := (hne bl).1 h1
      refine ⟨h1', ?_, e, ?_, h4⟩
      · rw [← hpos bl (hsome bl h1')]; exact h2
      · rw [← hpe bl pid (hsome bl h1')]; exact h3
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      rw [hv] at h3
      refine ⟨v, ((hroot n v s).1 ⟨h1, h3⟩).1, ?_, ?_⟩
      · rw [← hbkt]; exact h2
      · exact h3
  intro s c1 c2 h1 h2
  exact h s c1 c2 (hcw s c1 h1) (hcw s c2 h2)

section put
variable (X : WX) (l : Loc) (B : BRec) (r : NRec) (bnd : Loc → Bnd) (e : WEntry) (ib : InBucket)
  (hok : wOK X) (hB : X.t.bs !! X.rl = some B) (hr : B.ns !! l = some r)
  (hleaf : r.nv.isLeaf' = true) (hbk : bktKeysB X.v B bnd)
  (hkin : keyIn (bnd l).1 (bnd l).2 e.key)
  (hflag : isBktFlag e.flags) (hval : e.value = emptyBktVal ib) (h0 : ib.root' = W64 0)
  (hnone : ∀ v, (e.key, v) ∉ rootEnts X)
include hok hB hr hleaf hbk hkin hflag hval h0 hnone

/-- The root entries that cover a slot are kept by the put. -/
theorem rootCov_createPut (n : GoString) (v : List w8) (s : Nat) :
    ((n, v) ∈ rootEnts (X.withWs X.rl l (wsPut r.ws e)) ∧ bucketCovers X.v.pages v s) ↔
      ((n, v) ∈ rootEnts X ∧ bucketCovers X.v.pages v s) := by
  by_cases hn : n = e.key
  · subst hn
    constructor
    · rintro ⟨h1, ⟨id, pg, hh, -⟩⟩
      have := (rootEnts_key_eq X l B r bnd e hok hB hr hleaf hbk hkin hflag).1 _ h1 rfl
      simp only [Prod.mk.injEq] at this
      rw [this.2, hval] at hh
      exact absurd hh (emptyBktVal_noHas _ ib h0 id)
    · rintro ⟨h1, -⟩; exact absurd h1 (hnone v)
  · have hF := rootEnts_filter_ne X l B r bnd e hok hB hr hleaf hbk hkin
    have hmem : ∀ L : List (GoString × List w8), (n, v) ∈ L ↔
        (n, v) ∈ L.filter (fun x => decide (x.1 ≠ e.key)) := by
      intro L; rw [List.mem_filter]; simp [hn]
    rw [hmem (rootEnts (X.withWs X.rl l (wsPut r.ws e))), hF, ← hmem]

/-- **`flViewU` across the put** (on `withWs`). -/
theorem flViewU_createPut (fl : FLPg) (h : flViewU X fl) :
    flViewU (X.withWs X.rl l (wsPut r.ws e)) fl := by
  have hroot := rootCov_createPut X l B r bnd e ib hok hB hr hleaf hbk hkin hflag hval h0 hnone
  let ws' := wsPut r.ws e
  have hvv : (X.withWs X.rl l ws').v = X.v := rfl
  have hfuel : (X.withWs X.rl l ws').fuel = X.fuel := withWs_fuel X X.rl l ws' B r hB hr
  have hbkt : ∀ n, bktLoc (X.withWs X.rl l ws') n = bktLoc X n := withWs_bktLoc X X.rl l ws' B r hB hr
  have hbs : ∀ c, ((X.withWs X.rl l ws').t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [withWs_bs_at]; cases X.t.bs !! c <;> simp
  have hshape : ∀ c pid, shp (ltree (X.withWs X.rl l ws') c pid) = shp (ltree X c pid) := by
    intro c pid
    rw [withWs_ltree X X.rl l ws' B r hB hr hleaf]
    split
    · rename_i h
      obtain ⟨rfl, hres⟩ := h
      have hL : ltree X X.rl pid = some (r.nv.isLeaf', r.ws) := by simp [ltree, hB, hres, hr]
      rw [hL, hleaf]; rfl
    · rfl
  have hpos : ∀ c, (X.withWs X.rl l ws').positions c = X.positions c := by
    intro c
    unfold WX.positions
    rw [hfuel, withWs_rootPid X X.rl l ws' B r hB hr]
    exact lposF_congr _ _ c (hshape c) _ _
  have hpe : ∀ c pid, (X.withWs X.rl l ws').posExtent c pid = X.posExtent c pid := by
    intro c pid
    unfold WX.posExtent
    rw [withWs_bs_at, hvv]
    cases hBc : X.t.bs !! c with
    | none => rfl
    | some C =>
      simp only [Option.map_some]
      by_cases hc : c = X.rl
      · simp only [hc, ↓reduceIte]
        rw [show resolve (brecWithWs C l ws') pid = resolve C pid from rfl]
        cases hres : resolve C pid with
        | none => rfl
        | some l0 =>
          simp only
          rw [brecWithWs_ns]
          cases C.ns !! l0 with
          | none => rfl
          | some r0 => by_cases hl0 : l0 = l <;> simp [hl0]
      · simp only [hc, ↓reduceIte]
  have hext : ∀ c, (X.withWs X.rl l ws').extents c = X.extents c := by
    intro c; unfold WX.extents; rw [hpos]; congr 1; funext pid; exact hpe c pid
  refine ⟨flView_congr X _ fl hvv (lCovers_congrB X _ hvv hroot hbkt hbs (fun c _ => hext c)) h.1,
    covU_congrB X _ hvv hroot hbkt hbs (fun c _ => hpos c) (fun c pid _ => hpe c pid) h.2.1,
    h.2.2.1, h.2.2.2⟩

end put

/-- **`setNode` and `withWs` agree on what `flViewU` reads** (the record keeps its page id and
leaf flag; the second half of U7i's `flViewU_setNode`, for any bucket). -/
theorem flViewU_setNode_of_withWs (X : WX) (fl : FLPg) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (hlf' : r'.nv.isLeaf' = r.nv.isLeaf') (hpg : r'.nv.pgid' = r.nv.pgid')
    (hY : flViewU (X.withWs bl l r'.ws) fl) : flViewU (X.setNode bl l r') fl := by
  let Y := X.withWs bl l r'.ws
  let Z := X.setNode bl l r'
  have hZ : Z.t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l r' } := by
    show (X.setNode bl l r').t.bs = _
    unfold WX.setNode WX.setBkt; rw [hB]
  have hYb : Y.t.bs = X.t.bs.insert bl { B with ns := B.ns.insert l { r with ws := r'.ws } } := by
    show (X.withWs bl l r'.ws).t.bs = _
    unfold WX.withWs; rw [hB]; simp only [hr]
  have hv : Z.v = Y.v := by
    show (X.setNode bl l r').v = (X.withWs bl l r'.ws).v
    unfold WX.setNode WX.setBkt; rw [hB]; rfl
  have hrl : Z.rl = Y.rl := by
    show (X.setNode bl l r').rl = (X.withWs bl l r'.ws).rl
    unfold WX.setNode WX.setBkt; rw [hB]; rfl
  have hlt : ltree Z = ltree Y := ltree_setNode_eq X bl l B r r' hB hr hlf'
  have hfuel : Z.fuel = Y.fuel := by
    unfold WX.fuel; rw [hZ, hYb, GMap.map_size_insert_Some _ _ _ _ hB,
      GMap.map_size_insert_Some _ _ _ _ hB, hv]
  have hbsc : ∀ c, (Z.t.bs !! c).map (fun C => (C.ib, C.bv, C.nm, C.bm)) =
      (Y.t.bs !! c).map (fun C => (C.ib, C.bv, C.nm, C.bm)) := by
    intro c; rw [hZ, hYb]
    by_cases hc : c = bl
    · subst hc; simp
    · simp [Ne.symm hc]
  have hrp : ∀ c, Z.rootPid c = Y.rootPid c := by
    intro c; unfold WX.rootPid
    have := congrArg (Option.map fun x : InBucket × _ × _ × _ => x.1.root') (hbsc c)
    simp only [Option.map_map, Function.comp_def] at this
    exact congrArg (fun o => Option.getD o 0) this
  have hbkt : ∀ n, bktLoc Z n = bktLoc Y n := by
    intro n; unfold bktLoc; rw [hrl]
    have := congrArg (Option.map fun x : InBucket × _ × _ × GMap GoString Loc => x.2.2.2) (hbsc Y.rl)
    simp only [Option.map_map, Function.comp_def] at this
    cases e1 : Z.t.bs !! Y.rl <;> cases e2 : Y.t.bs !! Y.rl <;> simp_all
  have hleaves : ∀ c, Z.leaves c = Y.leaves c := by
    intro c; unfold WX.leaves; rw [hlt, hfuel, hrp]
  have hroots : rootEnts Z = rootEnts Y := by unfold rootEnts; rw [hrl, hleaves]
  have hsome : ∀ c, (Z.t.bs !! c).isSome = (Y.t.bs !! c).isSome := by
    intro c; have := congrArg Option.isSome (hbsc c); simpa using this
  have hpos : ∀ c, Z.positions c = Y.positions c := by
    intro c; unfold WX.positions; rw [hlt, hfuel, hrp]
  have hpe : ∀ c pid, Z.posExtent c pid = Y.posExtent c pid := by
    intro c pid
    apply posExtent_eq Y Z c pid hv
    rw [hZ, hYb]
    by_cases hc : c = bl
    · subst hc
      simp only [GMap.lookup_insert, Option.map_some, Option.some.injEq]
      unfold posIdOf
      show (match resolve B pid with
          | some l0 => ((B.ns.insert l r' !! l0).map fun r0 : NRec => r0.nv.pgid').getD 0
          | none => pid) =
        (match resolve B pid with
          | some l0 => ((B.ns.insert l { r with ws := r'.ws } !! l0).map fun r0 : NRec => r0.nv.pgid').getD 0
          | none => pid)
      cases resolve B pid with
      | none => rfl
      | some l0 =>
        by_cases hl0 : l0 = l
        · subst hl0; simp [hpg]
        · simp [Ne.symm hl0]
    · simp [Ne.symm hc]
  have hext : ∀ c, Z.extents c = Y.extents c := by
    intro c; unfold WX.extents; rw [hpos]; congr 1; funext pid; exact hpe c pid
  refine ⟨flView_congr Y Z fl hv (lCovers_congr Y Z hv hroots hbkt hsome (fun c _ => hext c)) hY.1,
    covU_congr Y Z hv hroots hbkt hsome (fun c _ => hpos c) (fun c pid _ => hpe c pid) hY.2.1,
    ?_, hY.2.2.2⟩
  rw [hv]; exact hY.2.2.1

end createbktfl

end Write

end bbolt
end EtcdGrove
end Perennial
