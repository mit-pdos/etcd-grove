/-
The bridge from the writer's logical stacks to its cursor stacks (U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): a stack `lPath` built (by `seek_w`, over the logical tree) is a
`boltCurDef` writer stack over the base view (`sPathR` from the bucket's root, the registry
`X.nloc`), its leaf page, if a page, holds its bounds' entries (`sLeafOK`), and its leaf's entries
are all plain and are `entsIn (wEs X n) (pathBnd …)`. The branch keys along the path are the base
pages' (F3, `nodePg`), so the walk's bounds are `pathBnd`; the leaf's entries are the bucket's
within them (as `ltree_leaf_of_T'`, at the walk's own bounds).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur
public import Proof.go_etcd_io.bbolt.Read.LeafOfT
public import Proof.go_etcd_io.bbolt.Read.PubWGet
public import Proof.go_etcd_io.bbolt.Write.Fuel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WBridge

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write Ents LeafT

section bridge
variable [GooseExts]

/-! ## A logical stack is a leaf of the walk -/

theorem lPathFrom_tail (X : WX) (bl : Loc) (p : w64) (e e' : elemRef) (es : List elemRef)
    (ps : List w64) (h : lPathFrom X bl p (e :: e' :: es) ps) :
    ∃ ws w ps', ps = p :: ps' ∧ refAt X bl p e ∧ ltree X bl p = some (false, ws) ∧
      ws[e.index'.toNat]? = some w ∧ lPathFrom X bl w.pgid (e' :: es) ps' := by
  obtain ⟨-, hlen, hhd, hall⟩ := h
  cases ps with
  | nil => simp at hlen
  | cons p0 ps' =>
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    obtain ⟨hr, lf, ws, hL, hnext, -⟩ := hall 0 e p0 rfl rfl
    obtain ⟨rfl, w, hw, hpn⟩ := hnext (by simp)
    refine ⟨ws, w, ps', rfl, hr, hL, hw, by simp, by simpa using hlen, ?_, ?_⟩
    · rw [List.head?_eq_getElem?]; simpa using hpn
    · intro j e2 p2 he hp
      obtain ⟨h1, lf2, ws2, h2, h3, h4⟩ := hall (j + 1) e2 p2 (by simpa using he) (by simpa using hp)
      exact ⟨h1, lf2, ws2, h2, fun hj => h3 (by simp at hj ⊢; omega),
        fun hj => h4 (by simp at hj ⊢; omega)⟩

theorem lPathFrom_one (X : WX) (bl : Loc) (p : w64) (e : elemRef) (ps : List w64)
    (h : lPathFrom X bl p [e] ps) :
    ps = [p] ∧ refAt X bl p e ∧ ∃ ws, ltree X bl p = some (true, ws) := by
  obtain ⟨-, hlen, hhd, hall⟩ := h
  cases ps with
  | nil => simp at hlen
  | cons p0 ps' =>
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    have : ps' = [] := by simpa using hlen
    subst this
    obtain ⟨hr, lf, ws, hL, -, hlast⟩ := hall 0 e p0 rfl rfl
    have := hlast rfl
    subst this
    exact ⟨rfl, hr, ws, hL⟩

/-- **A logical stack's leaf is a leaf of the walk, at the bounds `pathBndFrom`** (given that the
logical branches' keys are the base pages'). -/
theorem lPathFrom_lleavesB (X : WX) (bl : Loc)
    (hkeys : ∀ p ws, ltree X bl p = some (false, ws) → ws.map WEntry.key = pidKeys X.v p.toNat) :
    ∀ (els : List elemRef) (ps : List w64) (p : w64) (b : Bnd) (F : Nat),
    lPathFrom X bl p els ps → els.length ≤ F →
    ∃ pl ws, ps.getLast? = some pl ∧ ltree X bl pl = some (true, ws) ∧
      (pl, pathBndFrom X.v b (ps.map (·.toNat)) els, ws) ∈ lleavesB (ltree X) bl F p b
  | [], _, _, _, _, h, _ => absurd rfl h.1
  | [e], ps, p, b, F, h, hF => by
    obtain ⟨rfl, -, ws, hL⟩ := lPathFrom_one X bl p e ps h
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    refine ⟨p, ws, rfl, hL, ?_⟩
    simp only [lleavesB, hL, List.map_cons, List.map_nil]
    simp [pathBndFrom]
  | e :: e' :: es, ps, p, b, F, h, hF => by
    obtain ⟨ws, w, ps', rfl, -, hL, hw, ht⟩ := lPathFrom_tail X bl p e e' es ps h
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    obtain ⟨pl, ws', hlast, hL', hmem⟩ :=
      lPathFrom_lleavesB X bl hkeys (e' :: es) ps' w.pgid (wEntryBnd b ws e.index'.toNat) F' ht
        (by simp at hF ⊢; omega)
    have hne : ps' ≠ [] := by
      intro h0; subst h0; obtain ⟨-, hlen, -⟩ := ht; simp at hlen
    obtain ⟨p', ps'', rfl⟩ : ∃ p' ps'', ps' = p' :: ps'' := by
      cases ps' with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, t, rfl⟩
    refine ⟨pl, ws', ?_, hL', ?_⟩
    · rw [List.getLast?_cons_cons]; exact hlast
    · have hb : wEntryBnd b ws e.index'.toNat = entryBnd b (pidKeys X.v p.toNat) e.index'.toNat := by
        unfold wEntryBnd; rw [hkeys p ws hL]
      rw [hb] at hmem
      simp only [List.map_cons, pathBndFrom]
      simp only [lleavesB, hL]
      have hi : e.index'.toNat < ws.length := (List.getElem?_eq_some_iff.1 hw).1
      have hgd : ws.getD e.index'.toNat default = w := by
        rw [List.getD_eq_getElem?_getD, hw]; rfl
      refine List.mem_flatMap.2 ⟨e.index'.toNat, List.mem_range.2 hi, ?_⟩
      rw [hgd, wEntryBnd, hkeys p ws hL]
      simpa using hmem

/-! ## The walk at more fuel -/

/-- The view's tree measure decreases along the logical branches (`Write.wOK_leaves_fuel'`'s step). -/
theorem ltree_dec (X : WX) (bl : Loc) (hok : wOK X) :
    ∀ pid ws, ltree X bl pid = some (false, ws) → ∀ w ∈ ws,
      treeMeasure X.v.pages w.pgid < treeMeasure X.v.pages pid := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  intro pid ws hL w hw
  unfold ltree at hL
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hL; cases hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    have hc := wOK_bktClean X hok bl B hB
    cases hr : resolve B pid with
    | some l =>
      rw [hr] at hL
      simp only at hL
      cases hrl : B.ns !! l with
      | none => rw [hrl] at hL; cases hL
      | some r =>
        rw [hrl] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
        obtain ⟨hleaf, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have := hc.2.2.2.2.2.2.1 hin l r hrl; rw [hleaf] at this; cases this
        · have hnm : B.nm !! pid = some l := by unfold resolve at hr; rwa [if_neg hin] at hr
          obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 pid l hnm
          rw [hrl] at hr'; cases hr'
          obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := ((hok.2.2.1 bl B hB l r hrl).2 hleaf)
          rw [hpid] at hpg
          obtain ⟨i, hi, he⟩ := List.getElem_of_mem hw
          have hwi : r.ws[i]? = some w := by rw [List.getElem?_eq_getElem hi]; exact congrArg _ he
          rw [hws i w hwi]
          exact treeMeasure_child X.v hv pid pg hpg hbr i (by rw [← hlen]; exact hi)
    | none =>
      rw [hr] at hL
      simp only at hL
      cases hp : wpageAt X.v B pid with
      | none => rw [hp] at hL; cases hL
      | some x =>
        obtain ⟨pa, pg⟩ := x
        rw [hp] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
        obtain ⟨hnl, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hr; rw [if_pos hin] at hr; split at hr
            · assumption
            · cases hr
          have := wOK_inlineLeaf X bl pid hok B pa pg hB hin hrn hp
          exact absurd this hnl
        · have hpg : X.v.pages !! pid.toNat = some pg := by
            unfold wpageAt at hp; rw [if_neg hin] at hp
            cases h : X.v.pages !! pid.toNat with
            | none => rw [h] at hp; cases hp
            | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                            Prod.mk.injEq] at hp; rw [hp.2]
          have hbr : pageFlags pg = branchPageFlag := by
            rcases (Read.viewWF_page X.v hv _ pg hpg).2.2.2 with h | h
            · exact h
            · exact absurd h hnl
          unfold pageWs at hw
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
            unfold pageW; simp [hnl]
          rw [this]
          exact treeMeasure_child X.v hv pid pg hpg hbr i hi

/-- **More fuel walks the same leaves, with their bounds.** -/
theorem lleavesB_fuel_stable (L : LTree) (bl : Loc) (μ : w64 → Nat)
    (hdec : ∀ pid ws, L bl pid = some (false, ws) → ∀ w ∈ ws, μ w.pgid < μ pid) :
    ∀ n k pid b, μ pid < n → lleavesB L bl (n + k) pid b = lleavesB L bl n pid b
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, pid, b, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [lleavesB]
    cases hL : L bl pid with
    | none => rfl
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true => rfl
      | false =>
        simp only
        apply flatMap_congr'
        intro i hi
        have hi' : i < ws.length := List.mem_range.1 hi
        exact lleavesB_fuel_stable L bl μ hdec n k _ _
          (by have := hdec pid ws hL _ (getD_mem ws i hi'); omega)

/-- **A logical stack of a `wOK` writer's bucket ends at a leaf of its walk** (at `X.fuel`, from
its root, with the bounds `pathBnd`). -/
theorem lPath_lleavesB (X : WX) (bl : Loc) (hok : wOK X)
    (hkeys : ∀ p ws, ltree X bl p = some (false, ws) → ws.map WEntry.key = pidKeys X.v p.toNat)
    (els : List elemRef) (ps : List w64) (h : lPath X bl els ps) :
    ∃ pl ws, ps.getLast? = some pl ∧ ltree X bl pl = some (true, ws) ∧
      (pl, pathBnd X.v (ps.map (·.toNat)) els, ws) ∈
        lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none) := by
  obtain ⟨pl, ws, h1, h2, h3⟩ := lPathFrom_lleavesB X bl hkeys els ps (X.rootPid bl) (none, none)
    (X.fuel + els.length) h (by omega)
  refine ⟨pl, ws, h1, h2, ?_⟩
  rw [lleavesB_fuel_stable (ltree X) bl (treeMeasure X.v.pages) (ltree_dec X bl hok) X.fuel
    els.length _ _ (by have := treeMeasure_le X.v.pages (X.rootPid bl); unfold WX.fuel; omega)] at h3
  exact h3

open Classical in
/-- **A leaf of the walk holds the bucket's entries within its bounds** (`ltree_leaf_of_T'`, at the
walk's own bounds). -/
theorem walk_leaf_ents (X : WX) (n : GoString) (bl : Loc) (hok : wOK X) (hb : bktLoc X n = some bl)
    (x : w64 × Bnd × List WEntry)
    (hx : x ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none)) :
    x.2.2.filterMap plainOf =
      (bktEnts (((wtxData X) !! n).getD ∅)).filter fun e => decide (keyIn x.2.1.1 x.2.1.2 e.1) := by
  -- the bucket's record
  have hB : ∃ B, X.t.bs !! bl = some B := by
    unfold bktLoc at hb
    cases hR : X.t.bs !! X.rl with
    | none => rw [hR] at hb; cases hb
    | some R =>
      rw [hR] at hb
      simp only [Option.bind_some] at hb
      exact Option.isSome_iff_exists.1 ((hok.1.2.2.2.2.2 X.rl R hR).2 n bl hb)
  obtain ⟨B, hB⟩ := hB
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  obtain ⟨hP1, -, hP2⟩ := bInv_walk X bl B bnd hok hB hbk X.fuel _ _
    (bInv_root X bl B bnd hok hB hbk)
  -- the bucket's data
  have hdata : ((wtxData X) !! n).getD ∅ = GMap.ofList (lbktEnts X bl) := by
    rw [wtxData_lookup]
    unfold bktData
    obtain ⟨v0, hv0⟩ := bktLoc_rootEnt X hok n bl hb
    cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 hf (n, v0) hv0
      simp at this
    | some e =>
      simp only [Option.map_some, Option.getD_some]
      rw [bktDataOf_eq, hb]
  rw [hdata]
  have hE := lbktEnts_blocks X bl
  have hsortB : ∀ y ∈ lleavesB (ltree X) bl X.fuel (X.rootPid bl) (none, none), wsPw y.2.2 :=
    fun y hy => leaf_pw X hok bl B hB y.1 y.2.2 (lleavesB_leaf _ _ _ _ _ y hy)
  have hnd : (lbktEnts X bl).Pairwise (fun a b => a.1 ≠ b.1) := by
    rw [hE, List.pairwise_flatMap]
    refine ⟨fun y hy => ?_, ?_⟩
    · apply (plain_pw _ (hsortB y hy)).imp
      intro a b hab e
      rw [e] at hab
      exact go.goStringLt_irrefl _ hab
    · apply List.Pairwise.imp_of_mem _ hP2
      intro y z hy hz hR e he e' he' heq
      obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 he
      obtain ⟨w', hw', hwe'⟩ := List.mem_filterMap.1 he'
      have h1 := hP1 y hy w hw
      have h2 := hP1 z hz w' hw'
      rw [← plainOf_key w e hwe, heq, plainOf_key w' e' hwe'] at h1
      exact hR _ h1 h2
  show x.2.2.filterMap plainOf = _
  apply sorted_ext
  · exact plain_pw _ (hsortB x hx)
  · exact (bktEnts_sorted _).filter _
  · intro e
    rw [List.mem_filter, mem_bktEnts, ofList_lookup_iff _ hnd, decide_eq_true_iff]
    constructor
    · intro he
      obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 he
      refine ⟨?_, ?_⟩
      · rw [hE]; exact List.mem_flatMap.2 ⟨x, hx, he⟩
      · rw [plainOf_key w e hwe]; exact hP1 x hx w hw
    · rintro ⟨hm, hk⟩
      rw [hE] at hm
      obtain ⟨y, hy, hey⟩ := List.mem_flatMap.1 hm
      have hyx : y = x := by
        apply Classical.byContradiction
        intro hne
        obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.1 hey
        have h1 := hP1 y hy w hw
        rw [← plainOf_key w e hwe] at h1
        exact pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hP2 y hy x hx hne _ h1 hk
      rw [← hyx]; exact hey

/-! ## A logical position over the base view -/

theorem pageWs_map_key (pg : List w8) :
    (pageWs pg).map WEntry.key = (List.range (pageCount pg)).map (pageKey pg) := by
  unfold pageWs pageKey
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, pageW]
  unfold leafPageFlag
  split <;> rfl

/-- **The logical branch keys are the base pages'** (F3: a branch node's keys are its page's). -/
theorem ltree_branch_keys (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) :
    ∀ p ws, ltree X bl p = some (false, ws) → ws.map WEntry.key = pidKeys X.v p.toNat := by
  intro p ws hL
  have hc := wOK_bktClean X hok bl B hB
  unfold ltree at hL
  rw [hB] at hL
  simp only at hL
  cases hres : resolve B p with
  | some l =>
    rw [hres] at hL
    simp only at hL
    cases hrl : B.ns !! l with
    | none => rw [hrl] at hL; cases hL
    | some r =>
      rw [hrl] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨hleaf, rfl⟩ := hL
      by_cases hin : B.ib.root' = W64 0
      · have := hc.2.2.2.2.2.2.1 hin l r hrl; rw [hleaf] at this; cases this
      · have hnm : B.nm !! p = some l := by rw [← resolve_tree B p hin]; exact hres
        obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 p l hnm
        rw [hrl] at hr'; cases hr'
        obtain ⟨⟨-, hF3⟩, pg, hpg, -⟩ := (hok.2.2.1 bl B hB l r hrl).2 hleaf
        rw [hpid] at hpg
        unfold pidKeys; rw [hpg]; simp only
        exact hF3 pg (by rw [hpid]; exact hpg)
  | none =>
    rw [hres] at hL
    simp only at hL
    cases hp : wpageAt X.v B p with
    | none => rw [hp] at hL; cases hL
    | some x =>
      obtain ⟨pa, pg⟩ := x
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
      obtain ⟨hnl, rfl⟩ := hL
      by_cases hin : B.ib.root' = W64 0
      · have hrn : B.bv.rootNode' = null := by
          unfold resolve at hres; rw [if_pos hin] at hres; split at hres
          · assumption
          · cases hres
        exact absurd (wOK_inlineLeaf X bl p hok B pa pg hB hin hrn hp) hnl
      · have hpg : X.v.pages !! p.toNat = some pg := by
          unfold wpageAt at hp; rw [if_neg hin] at hp
          cases h : X.v.pages !! p.toNat with
          | none => rw [h] at hp; cases hp
          | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                          Prod.mk.injEq] at hp; rw [hp.2]
        unfold pidKeys; rw [hpg]; simp only
        exact pageWs_map_key pg

/-- An inline bucket's logical positions are leaves. -/
theorem ltree_inline_leaf (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hin : B.ib.root' = W64 0) (p : w64) (lf : Bool)
    (ws : List WEntry) (hL : ltree X bl p = some (lf, ws)) : lf = true := by
  have hc := wOK_bktClean X hok bl B hB
  unfold ltree at hL
  rw [hB] at hL
  simp only at hL
  cases hres : resolve B p with
  | some l =>
    rw [hres] at hL
    simp only at hL
    cases hrl : B.ns !! l with
    | none => rw [hrl] at hL; cases hL
    | some r =>
      rw [hrl] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      rw [← hL.1]; exact hc.2.2.2.2.2.2.1 hin l r hrl
  | none =>
    rw [hres] at hL
    simp only at hL
    cases hp : wpageAt X.v B p with
    | none => rw [hp] at hL; cases hL
    | some x =>
      obtain ⟨pa, pg⟩ := x
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      have hrn : B.bv.rootNode' = null := by
        unfold resolve at hres; rw [if_pos hin] at hres; split at hres
        · assumption
        · cases hres
      rw [← hL.1]
      simp only [decide_eq_true_eq]
      exact wOK_inlineLeaf X bl p hok B pa pg hB hin hrn hp

/-- An inline bucket's logical stack is at position `0`. -/
theorem lPath_inline_zero (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hin : B.ib.root' = W64 0) (els : List elemRef) (ps : List w64)
    (hp : lPath X bl els ps) : ∀ (j : Nat) (p : w64), ps[j]? = some p → p = W64 0 := by
  obtain ⟨-, hlen, hhd, hall⟩ := hp
  intro j p hj
  cases j with
  | zero =>
    rw [List.head?_eq_getElem?] at hhd
    rw [hhd] at hj; cases hj
    unfold WX.rootPid; rw [hB]; exact hin
  | succ j =>
    have hj1 : j + 1 < ps.length := (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨-, lf, ws, hL, hnext, -⟩ := hall j els[j] ps[j]
      (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega))
    have := (hnext (by omega)).1
    rw [ltree_inline_leaf X bl B hok hB hin _ lf ws hL] at this
    cases this

/-- **A logical position's facts over the base view**: a node reference is registered at its
position, a page reference is its view page (or the inline page), a branch is its base page with
its children's ids, a leaf is a base leaf page (or the inline root), and a leaf page reference's
entries are its page's (`leafPgAt`). -/
theorem pos_facts (X : WX) (bl : Loc) (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B)
    (hnl : nlocCur X) (hbase : 0 < X.v.base.addr) (p : w64) (e : elemRef) (lf : Bool)
    (ws : List WEntry) (hr : refAt X bl p e) (hL : ltree X bl p = some (lf, ws))
    (hin0 : B.ib.root' = W64 0 → p = W64 0) :
    (e.node' ≠ null → X.nloc !! e.node' = some (bl, p.toNat)) ∧
    (e.node' = null → e.page' ≠ null ∧ (p.toNat ≠ 0 → e.page' = pageLoc X.v p.toNat)) ∧
    (lf = false → ∃ pg, X.v.pages !! p.toNat = some pg ∧ pageFlags pg = branchPageFlag ∧
      ws.length = pageCount pg ∧ ∀ i w, ws[i]? = some w → w.pgid = W64 (branchPgid pg i : Int)) ∧
    (lf = true → p.toNat = 0 ∨ ∃ pg, X.v.pages !! p.toNat = some pg ∧
      pageFlags pg = leafPageFlag) ∧
    (e.node' = null → ∃ pg, leafPgAt X.v B.ipg p.toNat = some pg ∧ ws = pageWs pg ∧
      (p.toNat = 0 → inlineGood pg)) := by
  have hc := wOK_bktClean X hok bl B hB
  have hlive : bl ∈ X.liveB := hok.2.2.2.2.2.1.2.2.1 bl B hB
  obtain ⟨B', hB', hm⟩ := hr
  rw [hB] at hB'; cases hB'
  cases hres : resolve B p with
  | some l =>
    simp only [hres] at hm
    have hnm : B.nm !! p = some l := by
      by_cases hin : B.ib.root' = W64 0
      · have hp0 := hin0 hin
        unfold resolve at hres; rw [if_pos hin] at hres
        by_cases hrn : B.bv.rootNode' = null
        · rw [if_pos hrn] at hres; cases hres
        · rw [if_neg hrn] at hres; cases hres
          have := hc.2.2.2.1 hrn; rw [hin, ← hp0] at this; exact this
      · rw [← resolve_tree B p hin]; exact hres
    obtain ⟨hlnn, r, hrl, hpid⟩ := hc.2.2.2.2.1 p l hnm
    rw [ltree_node X bl B p l r hB hres hrl] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    have hnp := hok.2.2.1 bl B hB l r hrl
    refine ⟨fun _ => by rw [hm]; exact hnl.2 bl B p l hB hlive hnm,
      fun h => absurd (hm ▸ h) hlnn, fun hleaf => ?_, fun hleaf => ?_,
      fun h => absurd (hm ▸ h) hlnn⟩
    · obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := hnp.2 hleaf
      rw [hpid] at hpg
      exact ⟨pg, hpg, hbr, hlen, hws⟩
    · by_cases hin : B.ib.root' = W64 0
      · left; rw [hin0 hin]; rfl
      · obtain ⟨pg, hpg, hf⟩ := (hnp.1 hleaf).2 hin
        rw [hpid] at hpg
        exact Or.inr ⟨pg, hpg, hf⟩
  | none =>
    simp only [hres] at hm
    obtain ⟨hnn, pg, hwp⟩ := hm
    rw [ltree_page X bl B p _ pg hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    by_cases hin : B.ib.root' = W64 0
    · have hrn : B.bv.rootNode' = null := by
        unfold resolve at hres; rw [if_pos hin] at hres; split at hres
        · assumption
        · cases hres
      have hp0 := hin0 hin
      subst hp0
      unfold wpageAt at hwp; rw [if_pos hin, if_pos rfl] at hwp
      simp only [Option.some.injEq, Prod.mk.injEq] at hwp
      obtain ⟨he, rfl⟩ := hwp
      obtain ⟨hpnn, -, hg, -⟩ := hc.1 hin hrn
      have h0 : (W64 0).toNat = 0 := rfl
      refine ⟨fun h => absurd hnn h, fun _ => ⟨by rw [← he]; exact hpnn, fun h => absurd h0 h⟩,
        fun hf => ?_, fun _ => Or.inl h0, fun _ => ⟨B.ipg, by rw [h0]; rfl, rfl, fun _ => hg⟩⟩
      simp only [decide_eq_false_iff_not] at hf
      exact absurd hg.2.1 hf
    · have hpg : ∃ pg', X.v.pages !! p.toNat = some pg' ∧ e.page' = pageLoc X.v p.toNat ∧
          pg' = pg := by
        unfold wpageAt at hwp; rw [if_neg hin] at hwp
        cases h : X.v.pages !! p.toNat with
        | none => rw [h] at hwp; cases hwp
        | some pg' =>
          rw [h] at hwp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwp
          exact ⟨pg', rfl, hwp.1.symm, hwp.2⟩
      obtain ⟨pg', hpg, hpl, hpp⟩ := hpg
      rw [hpp] at hpg
      obtain ⟨h2, -, -, hfl⟩ := Read.viewWF_page X.v hok.2.2.2.2.2.2.2 _ _ hpg
      have hne0 : p.toNat ≠ 0 := by omega
      refine ⟨fun h => absurd hnn h, fun _ => ⟨?_, fun _ => hpl⟩, fun hf => ?_, fun hf => ?_,
        fun _ => ⟨pg, by unfold leafPgAt; rw [if_neg hne0]; exact hpg, rfl, fun h => absurd h hne0⟩⟩
      · rw [hpl]; unfold pageLoc; intro h
        have := congrArg Loc.addr h
        simp [Loc.add, null] at this; omega
      · simp only [decide_eq_false_iff_not] at hf
        have hbr : pageFlags pg = branchPageFlag := by
          rcases hfl with h | h
          · exact h
          · exact absurd h hf
        refine ⟨pg, hpg, hbr, pageWs_len pg, fun i w hw => ?_⟩
        have hi : i < pageCount pg := by
          have := (List.getElem?_eq_some_iff.1 hw).1; rw [pageWs_len] at this; exact this
        rw [pageWs_get pg i hi] at hw; cases hw
        exact (Write.pageW_branch pg i hf).2
      · simp only [decide_eq_true_eq] at hf
        exact Or.inr ⟨pg, hpg, hf⟩

/-! ## The bridge -/

theorem filterMap_plain_all (ws : List WEntry) (h : ∀ w ∈ ws, ¬ isBktFlag w.flags) :
    ws.filterMap plainOf = ws.map fun w => (w.key, w.value) := by
  induction ws with
  | nil => rfl
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    have hp : plainOf a = some (a.key, a.value) := by unfold plainOf; simp [ha]
    rw [List.filterMap_cons, hp, List.map_cons]
    simp only
    rw [ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

/-- A logical leaf of the opened bucket `bl ≠ X.rl` has plain entries (`leafShape`, `posShape`,
an inline page's `inlineGood`). -/
theorem leaf_plain (X : WX) (bl : Loc) (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B)
    (hbr : bl ≠ X.rl) (p : w64) (hI : WOpen.posI X B p) (ws : List WEntry)
    (hL : ltree X bl p = some (true, ws)) : ∀ w ∈ ws, ¬ isBktFlag w.flags := by
  have hc := wOK_bktClean X hok bl B hB
  intro w hw hf
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn, rfl⟩ | ⟨hi, ht, hnm, ⟨c, hpr, hown⟩, -⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hleaf, rfl⟩ := hL
    exact hbr ((hok.1.2.1.2.2.1 bl B hB l rn hrn hleaf w hw).1 hf)
  · have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    obtain ⟨-, -, hg, -⟩ := hc.1 h0 hrn
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    rw [WOpen.pageW_leaf' _ _ hlf] at hf
    have := WOpen.isBktFlag_mod _ hf
    have := (hg.2.2.2.2 i hi).2
    omega
  · have hres : resolve B p = none := by
      rw [resolve_tree B p hi]
      have := hnm p.toNat (by obtain ⟨pg, hpg, -⟩ := WOpen.treeWF_page ht; exact treeHas.root _ pg hpg)
      rwa [LR.w64_toNat_eq] at this
    obtain ⟨-, pg, hpg, hwp, -⟩ := posOK_tree_page X B p hi ht hnm
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    unfold pageWs at hw
    obtain ⟨i, hi', rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi'
    rw [WOpen.pageW_leaf' _ _ hlf] at hf
    have h1 := WOpen.isBktFlag_mod _ hf
    have h2 := (hok.1.2.1.2.2.2.1 bl B hB c p.toNat pg hpr hown hpg hlf i hi').1
    unfold bucketLeafFlag at h2
    exact hbr (h2.1 h1)

/-- **The bridge** (U6aa): a logical stack `lPath` of the opened bucket `n` (at `bl ≠ X.rl`) of a
`wOK` writer whose registry is current is a `boltCurDef` writer stack from the bucket's root over
the registry `X.nloc` (`sPathR`), its leaf page, if a page, holds its bounds' entries (`sLeafOK`,
with the bucket's inline page `B.ipg`), and its leaf's entries are plain and are the bucket's
within the path's bounds. -/
theorem lPath_wStk (X : WX) (n : GoString) (bl : Loc) (B : BRec) (hok : wOK X)
    (hb : bktLoc X n = some bl) (hbr : bl ≠ X.rl) (hnl : nlocCur X) (hB : X.t.bs !! bl = some B)
    (hbase : 0 < X.v.base.addr) (els : List elemRef) (ps : List w64) (hp : lPath X bl els ps) :
    sPathR (fun l => X.nloc !! l) X.v bl (X.rootPid bl).toNat els (ps.map (·.toNat)) ∧
    sLeafOK X.v B.ipg (wEs X n) (ps.map (·.toNat)) els ∧
    (lLeaf X bl ps).map (fun w => (w.key, w.value)) =
      entsIn (wEs X n) (pathBnd X.v (ps.map (·.toNat)) els) ∧
    ∀ w ∈ lLeaf X bl ps, ¬ isBktFlag w.flags := by
  have hloc := PubW.bktLocalOK_of_wOK X hok bl B hB
  have hin0 : ∀ (j : Nat) (p : w64), ps[j]? = some p → B.ib.root' = W64 0 → p = W64 0 :=
    fun j p hj hin => lPath_inline_zero X bl B hok hB hin els ps hp j p hj
  have hfacts : ∀ (j : Nat) (e : elemRef) (p : w64), els[j]? = some e → ps[j]? = some p →
      ∃ lf ws, refAt X bl p e ∧ ltree X bl p = some (lf, ws) ∧
        (j + 1 < els.length → lf = false ∧ ∃ w, ws[e.index'.toNat]? = some w ∧
          ps[j + 1]? = some w.pgid) ∧ (j + 1 = els.length → lf = true) := by
    intro j e p he hpj
    obtain ⟨hr, lf, ws, hL, h1, h2⟩ := hp.2.2.2 j e p he hpj
    exact ⟨lf, ws, hr, hL, h1, h2⟩
  -- the leaf
  obtain ⟨pl, ws, hlast, hL, hmem⟩ :=
    lPath_lleavesB X bl hok (ltree_branch_keys X bl B hok hB) els ps hp
  have hlen := hp.2.1
  have hne := hp.1
  have hpos : 0 < ps.length := by
    rw [hlen]; cases els with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hlj : ps[ps.length - 1]? = some pl := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hll : lLeaf X bl ps = ws := by
    unfold lLeaf; rw [hlast]; simp only [hL]
  have hplain : ∀ w ∈ ws, ¬ isBktFlag w.flags :=
    leaf_plain X bl B hok hB hbr pl (WOpen.lPath_posI X bl B hB hloc els ps hp _ pl hlj) ws hL
  have hents : ws.map (fun w => (w.key, w.value)) =
      entsIn (wEs X n) (pathBnd X.v (ps.map (·.toNat)) els) := by
    rw [← filterMap_plain_all ws hplain]
    exact walk_leaf_ents X n bl hok hb _ hmem
  refine ⟨⟨hne, by simp [hlen], ?_, ?_⟩, ?_, by rw [hll]; exact hents, by rw [hll]; exact hplain⟩
  · obtain ⟨-, -, hhd, -⟩ := hp
    rw [List.head?_map, hhd]; rfl
  · intro j e pid he hpj
    rw [List.getElem?_map] at hpj
    cases hpj' : ps[j]? with
    | none => rw [hpj'] at hpj; cases hpj
    | some p =>
      rw [hpj'] at hpj
      simp only [Option.map_some, Option.some.injEq] at hpj
      subst hpj
      obtain ⟨lf, ws', hr, hL', hbrn, hlf⟩ := hfacts j e p he hpj'
      obtain ⟨f1, f2, f3, f4, -⟩ := pos_facts X bl B hok hB hnl hbase p e lf ws' hr hL'
        (hin0 j p hpj')
      refine ⟨f1, f2, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨rfl, w, hw, hpn⟩ := hbrn hj
        obtain ⟨pg, hpg, hfl, hcnt, hws⟩ := f3 rfl
        refine ⟨pg, hpg, hfl, ?_, ?_⟩
        · have := (List.getElem?_eq_some_iff.1 hw).1; omega
        · rw [List.getElem?_map, hpn, hws _ w hw]
          simp only [Option.map_some]
          rw [LR.branchPgid_toNat]
      · exact f4 (hlf hj)
  · intro e pid he hpid hnull
    rw [List.getLast?_map, hlast] at hpid
    simp only [Option.map_some, Option.some.injEq] at hpid
    subst hpid
    have hj : els.length - 1 < els.length := by omega
    have he' : els[els.length - 1]? = some e := by rw [← List.getLast?_eq_getElem?]; exact he
    obtain ⟨lf, ws', hr, hL', -, hlf⟩ := hfacts (els.length - 1) e pl he' (by rw [← hlen]; exact hlj)
    have hlf' := hlf (by omega)
    subst hlf'
    rw [hL] at hL'; cases hL'
    obtain ⟨-, -, -, -, f5⟩ := pos_facts X bl B hok hB hnl hbase pl e true ws hr hL
      (hin0 _ pl hlj)
    obtain ⟨pg, hpg, rfl, hig⟩ := f5 hnull
    refine ⟨pg, hpg, hplain, ?_, hig⟩
    unfold pgEnts; exact hents

/-! ## A routing stack's position (`Model/Cursor`'s private `stackPos_seek`, copied) -/

private theorem len_filter_sum (es : List BoltEnt) (f g h : BoltEnt → Bool)
    (hpt : ∀ e ∈ es, (if f e then 1 else 0) + (if g e then 1 else 0) = (if h e then 1 else 0)) :
    (es.filter f).length + (es.filter g).length = (es.filter h).length := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    have ha := hpt a (List.mem_cons_self ..)
    have ht := ih (fun e he => hpt e (List.mem_cons_of_mem _ he))
    simp only [List.filter_cons]
    split <;> split <;> split <;> simp_all <;> omega

private theorem takeWhile_lt_sorted (es : List BoltEnt) (k : List w8) (hs : esSorted es) :
    es.takeWhile (fun e => decide (go.GoStringLt e.1 k)) =
      es.filter (fun e => decide (go.GoStringLt e.1 k)) := by
  induction es with
  | nil => rfl
  | cons a t ih =>
    unfold esSorted at hs
    rw [List.pairwise_cons] at hs
    simp only [List.takeWhile_cons, List.filter_cons]
    by_cases ha : go.GoStringLt a.1 k
    · simp only [ha, decide_true, ↓reduceIte, ih hs.2]
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_nil_iff]
      intro x hx hxk
      simp only [decide_eq_true_eq] at hxk
      exact ha (go.goStringLt_trans (hs.1 x hx) hxk)

private theorem keyGe_lt {lo : Option (List w8)} {e k : List w8} (hk : keyGe lo k)
    (he : ¬ keyGe lo e) : go.GoStringLt e k := by
  cases lo with
  | none => exact absurd (fun _ h => nomatch h) he
  | some l =>
  have hel : go.GoStringLt e l := Classical.byContradiction fun h => he (fun l' hl => by
    cases hl; exact h)
  have := hk l rfl
  rcases Classical.em (go.GoStringLt l k) with h | h
  · exact go.goStringLt_trans hel h
  · rw [go.goStringLt_eq_of_not_lt this h]; exact hel

private theorem keyLt_lt {hi : Option (List w8)} {e k : List w8} (hk : keyLt k hi)
    (he : go.GoStringLt e k) : keyLt e hi :=
  fun h hh => go.goStringLt_trans he (hk h hh)

open Classical in
/-- The position of a search's leaf index under the bounds `bnd` routing `k`. -/
private theorem seek_count (es : List BoltEnt) (k : List w8) (bnd : Option (List w8) × Option (List w8))
    (hs : esSorted es) (hk : keyIn bnd.1 bnd.2 k) :
    (es.filter fun e => decide (¬ keyGe bnd.1 e.1)).length +
      ((entsIn es bnd).takeWhile fun e => decide (go.GoStringLt e.1 k)).length =
      seekIdx es k := by
  unfold seekIdx entsIn
  rw [takeWhile_lt_sorted es k hs, takeWhile_lt_sorted _ k (List.Pairwise.filter _ hs)]
  rw [List.filter_filter]
  apply len_filter_sum
  intro e _
  by_cases hg : keyGe bnd.1 e.1
  · by_cases hl : go.GoStringLt e.1 k
    · have := keyLt_lt hk.2 hl
      simp [hg, hl, keyIn, this]
    · simp [hg, hl]
  · have hl := keyGe_lt hk.1 hg
    simp [hg, hl, keyIn]

/-- A routed path's leaf bounds contain `k`. -/
private theorem pathBndFrom_route (v : View) (k : List w8) :
    ∀ (els : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    pids.length = els.length → keyIn b.1 b.2 k →
    (∀ j pid e, pids[j]? = some pid → els[j]? = some e → j + 1 < els.length →
      let ks := pidKeys v pid
      e.index'.toNat < ks.length ∧
      (e.index'.toNat = 0 ∨ ∃ ki, ks[e.index'.toNat]? = some ki ∧ ¬ go.GoStringLt k ki) ∧
      ∀ kn, ks[e.index'.toNat + 1]? = some kn → go.GoStringLt k kn) →
    keyIn (pathBndFrom v b pids els).1 (pathBndFrom v b pids els).2 k
  | [], _, b, _, hb, _ => by cases ‹List Nat› <;> simpa [pathBndFrom] using hb
  | [_], pids, b, hl, hb, _ => by
    match pids, hl with
    | [_], _ => simpa [pathBndFrom] using hb
  | e :: e' :: es, pids, b, hl, hb, hr => by
    match pids, hl with
    | pid :: pid' :: ps, hl =>
      simp only [pathBndFrom]
      apply pathBndFrom_route v k (e' :: es) (pid' :: ps)
      · simpa using hl
      · obtain ⟨_, h0, h1⟩ := hr 0 pid e rfl rfl (by simp)
        refine ⟨?_, ?_⟩
        · simp only [entryBnd, childLo]
          split
          · exact hb.1
          · rcases h0 with h0 | ⟨ki, hki, hnk⟩
            · contradiction
            · intro l hlk
              simp only [Option.some.injEq] at hlk
              subst hlk
              rw [List.getD_eq_getElem?_getD, hki]; exact hnk
        · simp only [entryBnd, childHi]
          split
          · intro h hh
            simp only [Option.some.injEq] at hh
            subst hh
            rw [List.getD_eq_getElem?_getD]
            obtain ⟨kn, hkn⟩ : ∃ kn, (pidKeys v pid)[e.index'.toNat + 1]? = some kn :=
              Option.isSome_iff_exists.mp (by simp [*])
            rw [hkn]; exact h1 kn hkn
          · exact hb.2
      · intro j p x hp hx hj
        exact hr (j + 1) p x (by simpa using hp) (by simpa using hx) (by simp at hj ⊢; omega)


theorem stackPos_seek' (v : View) (es : List BoltEnt) (pids : List Nat)
    (els : List elemRef) (k : List w8) (hs : esSorted es) (hl : pids.length = els.length)
    (hr : sRoutes v es pids els k) : stackPos v es pids els = seekIdx es k := by
  unfold stackPos
  rw [hr.2]
  exact seek_count es k _ hs (pathBndFrom_route v k els pids (none, none) hl
    (show keyIn (none : Option (List w8)) none k by
      unfold keyIn keyGe keyLt; simp)
    hr.1)

/-- **A routing logical stack is at `seekIdx`** (`lRoutes`): its position over the bucket's entries
is the search index of `k`, its leaf index the leaf's. -/
theorem lPath_seek (X : WX) (n : GoString) (bl : Loc) (B : BRec) (hok : wOK X)
    (hb : bktLoc X n = some bl) (hbr : bl ≠ X.rl) (hnl : nlocCur X) (hB : X.t.bs !! bl = some B)
    (hbase : 0 < X.v.base.addr) (els : List elemRef) (ps : List w64) (k : List w8)
    (hp : lPath X bl els ps) (hr : lRoutes X bl els ps k) :
    stackPos X.v (wEs X n) (ps.map (·.toNat)) els = seekIdx (wEs X n) k ∧
    leafIdx els = wsIdx (lLeaf X bl ps) k := by
  obtain ⟨-, -, hents, -⟩ := lPath_wStk X n bl B hok hb hbr hnl hB hbase els ps hp
  have hlen := hp.2.1
  have hne := hp.1
  obtain ⟨pl, ws, ⟨jl, hjl⟩, hL, hll⟩ := WOpen.lPath_leaf X bl B hB
    (PubW.bktLocalOK_of_wOK X hok bl B hB) els ps hp
  -- the leaf index
  have hleaf : leafIdx els = wsIdx (lLeaf X bl ps) k := by
    have hpos : 0 < els.length := by
      cases els with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    obtain ⟨e0, he⟩ : ∃ e0, els[els.length - 1]? = some e0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨p0, hpl⟩ : ∃ p0, ps[els.length - 1]? = some p0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, lf, ws', hL', -, hlast⟩ := hp.2.2.2 _ _ _ he hpl
    have := hlast (by omega)
    subst this
    have hpl' : ps.getLast? = some p0 := by
      rw [List.getLast?_eq_getElem?, show ps.length - 1 = els.length - 1 by omega]; exact hpl
    have hll' : lLeaf X bl ps = ws' := by unfold lLeaf; rw [hpl']; simp only [hL']
    rw [hll']
    have := (hr _ _ _ true ws' he hpl hL').2 rfl
    unfold leafIdx
    rw [List.getLast?_eq_getElem?, he]
    exact this
  refine ⟨?_, hleaf⟩
  apply stackPos_seek' _ _ _ _ k (bktEnts_sorted _) (by simp [hlen])
  refine ⟨fun j pid e hpj hej hj => ?_, ?_⟩
  · rw [List.getElem?_map] at hpj
    cases hpj' : ps[j]? with
    | none => rw [hpj'] at hpj; cases hpj
    | some p =>
      rw [hpj'] at hpj
      simp only [Option.map_some, Option.some.injEq] at hpj
      subst hpj
      obtain ⟨-, lf, ws', hL', hnext, -⟩ := hp.2.2.2 j e p hej hpj'
      obtain ⟨rfl, -⟩ := hnext hj
      obtain ⟨h1, h2, h3⟩ := (hr j e p false ws' hej hpj' hL').1 rfl
      have hk := ltree_branch_keys X bl B hok hB p ws' hL'
      simp only
      rw [← hk]
      refine ⟨by simpa using h1, ?_, ?_⟩
      · rcases h2 with h2 | ⟨w, hw, hnk⟩
        · exact Or.inl h2
        · exact Or.inr ⟨w.key, by simp [hw], hnk⟩
      · intro kn hkn
        rw [List.getElem?_map] at hkn
        cases hw : ws'[e.index'.toNat + 1]? with
        | none => rw [hw] at hkn; cases hkn
        | some w =>
          rw [hw] at hkn; simp only [Option.map_some, Option.some.injEq] at hkn
          subst hkn; exact h3 w hw
  · unfold wEs at hents
    rw [hleaf, ← hents]
    unfold wsIdx
    rw [List.takeWhile_map, List.length_map]
    rfl

end bridge

end WBridge

end bbolt
end EtcdGrove
end Perennial
