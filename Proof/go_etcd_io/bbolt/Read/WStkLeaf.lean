/-
A writer cursor's stack over the current logical tree (U6aa, `notes/bbolt-proof-plan.md`, "Writer
reads at a fraction"): a `boltCurDef` writer stack (`sPathR` over the base view from the bucket's
root) may hold stale references (a page since materialized), but its positions are a logical stack:
the same indices over the current references (`curRef`) are an `lPath`, so the bridge
(`Read/WBridge`) gives its leaf's entries; a node reference the registry names is current
(`nodeRef_current`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WBridge

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write Ents LeafT

section stkLeaf
variable [GooseExts]

/-- The current reference of position `pid` of bucket `B`, with `e`'s index: its materialized
node, else its page (`refAt`'s). -/
def curRef (X : WX) (B : BRec) (pid : w64) (e : elemRef) : elemRef :=
  match resolve B pid with
  | some l => { e with node' := l }
  | none => { e with node' := null, page' := ((wpageAt X.v B pid).map Prod.fst).getD null }

/-- A stack's elements with their current references. -/
def curRefs (X : WX) (B : BRec) (pids : List Nat) (els : List elemRef) : List elemRef :=
  List.zipWith (fun (p : Nat) e => curRef X B (W64 (p : Int)) e) pids els

theorem curRef_index (X : WX) (B : BRec) (p : w64) (e : elemRef) :
    (curRef X B p e).index' = e.index' := by
  unfold curRef; split <;> rfl

theorem curRefs_map_index (X : WX) (B : BRec) :
    ∀ (pids : List Nat) (els : List elemRef), pids.length = els.length →
    (curRefs X B pids els).map (·.index') = els.map (·.index')
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, e :: es, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := curRefs_map_index X B ps es h
    simp only [curRefs, List.zipWith_cons_cons, List.map_cons] at ih ⊢
    rw [ih, curRef_index]

theorem pathBndFrom_index (v : View) :
    ∀ (els els' : List elemRef) (pids : List Nat) (b : Option (List w8) × Option (List w8)),
    els.map (·.index') = els'.map (·.index') → pathBndFrom v b pids els = pathBndFrom v b pids els'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | e :: es, e' :: es', pids, b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    match pids with
    | [] => simp [pathBndFrom]
    | [_] => simp [pathBndFrom]
    | p :: p' :: ps =>
      simp only [pathBndFrom]
      rw [h.1]
      exact pathBndFrom_index v es es' (p' :: ps) _ h.2

/-- **A node reference the registry names is current**: a registered node of the opened bucket at
`(bl, pid)` is what the bucket resolves `pid` to. -/
theorem nodeRef_current (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (l : Loc) (pid : Nat)
    (hl : l ≠ null) (hnl : X.nloc !! l = some (bl, pid)) :
    resolve B (W64 (pid : Int)) = some l := by
  obtain ⟨hok, -, hnc, -, -⟩ := hc
  have hlive : bl ∈ X.liveB := hok.2.2.2.2.2.1.2.2.1 bl B hB
  obtain ⟨B', hB', hnm⟩ := hnc.1 l bl pid hnl hlive
  rw [hB] at hB'; cases hB'
  have hcl := wOK_bktClean X hok bl B hB
  by_cases hin : B.ib.root' = W64 0
  · unfold resolve; simp only [hin, ite_true]
    have hrn : B.bv.rootNode' ≠ null := by
      intro h0
      have := (hcl.2.2.1 h0).2
      rw [this] at hnm; simp at hnm
    simp only [hrn, ite_false]
    obtain ⟨-, r, hr, hpg⟩ := hcl.2.2.2.2.1 _ l hnm
    have hncl := hcl.2.2.2.2.2.2.2.1 l r hr
    have h0 : r.nv.pgid' = W64 0 := hncl.2.2.2.2.2.2.2.2.1 hin
    have h4 := hcl.2.2.2.1 hrn
    rw [hin, ← h0, hpg, hnm] at h4
    cases h4; rfl
  · rw [resolve_tree B _ hin]; exact hnm

theorem w64_cast_toNat (x : w64) : W64 ((x.toNat : Nat) : Int) = x := by simp [W64]

theorem W64_toNat_lt (p : Nat) (h : p < 2 ^ 64) : (W64 (p : Int)).toNat = p := by
  simp [W64]; omega

theorem branchPgid_lt (pg : List w8) (i : Nat) : branchPgid pg i < 2 ^ 64 := by
  unfold branchPgid; exact BitVec.isLt _

/-- A child of a view branch page is a view page. -/
theorem viewWF_child (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) : ∃ pg', v.pages !! branchPgid pg i = some pg' := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg ⊢
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf _ _ => rw [hb] at hf; exact absurd hf (by decide)
    | branch _ _ _ _ hch =>
      cases hch i hi with
      | page _ pg'' _ _ hp _ _ _ => exact ⟨pg'', hp⟩

theorem curRef_refAt (X : WX) (bl : Loc) (B : BRec) (pid : w64) (e : elemRef)
    (x : Bool × List WEntry) (hB : X.t.bs !! bl = some B) (hL : ltree X bl pid = some x) :
    refAt X bl pid (curRef X B pid e) := by
  refine ⟨B, hB, ?_⟩
  unfold curRef
  cases hr : resolve B pid with
  | some l => simp
  | none =>
    unfold ltree at hL; rw [hB] at hL; simp only [hr] at hL
    cases hw : wpageAt X.v B pid with
    | none => rw [hw] at hL; cases hL
    | some lp => exact ⟨rfl, lp.2, by simp⟩

theorem curRefs_get (X : WX) (B : BRec) : ∀ (pids : List Nat) (els : List elemRef) (j : Nat)
    (e' : elemRef), (curRefs X B pids els)[j]? = some e' →
    ∃ p e, pids[j]? = some p ∧ els[j]? = some e ∧ e' = curRef X B (W64 (p : Int)) e
  | [], _, _, _, h => by simp [curRefs] at h
  | _ :: _, [], _, _, h => by simp [curRefs] at h
  | p :: ps, e :: es, 0, e', h => by
    simp only [curRefs, List.zipWith_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨p, e, rfl, rfl, h.symm⟩
  | p :: ps, e :: es, j + 1, e', h => by
    simp only [curRefs, List.zipWith_cons_cons, List.getElem?_cons_succ] at h
    exact curRefs_get X B ps es j e' h

/-- One position of a writer stack, over the current logical tree. -/
theorem sPathR_pos (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl X.v bl rt els pids) (j : Nat) (e : elemRef) (p : Nat)
    (he : els[j]? = some e) (hpj : pids[j]? = some p) :
    p < 2 ^ 64 ∧ ∃ lf ws, ltree X bl (W64 (p : Int)) = some (lf, ws) ∧
      (j + 1 < els.length → lf = false ∧ ∃ w p', ws[e.index'.toNat]? = some w ∧
        pids[j + 1]? = some p' ∧ w.pgid = W64 (p' : Int)) ∧
      (j + 1 = els.length → lf = true) := by
  obtain ⟨hok, -, -, hrt, -⟩ := hc
  obtain ⟨hne, hlen, hhd, hall⟩ := hp
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hcl := wOK_bktClean X hok bl B hB
  have htp : ∀ l r, B.ns !! l = some r → nodePg X.v B.ib.root' r := hok.2.2.1 bl B hB
  have hroot : X.rootPid bl = B.ib.root' := by simp [WX.rootPid, hB]
  rw [hroot] at hrt
  have hj_lt : j < els.length := (List.getElem?_eq_some_iff.1 he).1
  have hpos : ∀ j p, pids[j]? = some p → (j = 0 ∧ p = rt) ∨
      ((∃ pg, X.v.pages !! p = some pg) ∧ p < 2 ^ 64) := by
    intro j p hj
    cases j with
    | zero =>
      left; refine ⟨rfl, ?_⟩
      rw [List.head?_eq_getElem?] at hhd; rw [hhd] at hj; cases hj; rfl
    | succ j =>
      right
      have hjl : j + 1 < els.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
      obtain ⟨e0, he0⟩ : ∃ e0, els[j]? = some e0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨p0, hp0⟩ : ∃ p0, pids[j]? = some p0 :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlen]; omega)⟩
      obtain ⟨pg, hpg, hf, hi, hnx⟩ := (hall j e0 p0 he0 hp0).2.2.1 hjl
      rw [hnx] at hj; cases hj
      exact ⟨viewWF_child _ hv _ _ hpg hf _ hi, branchPgid_lt _ _⟩
  have hbnd : p < 2 ^ 64 := by
    rcases hpos j p hpj with ⟨-, rfl⟩ | ⟨-, h⟩
    · rw [← hrt]; exact BitVec.isLt _
    · exact h
  have hP : (W64 (p : Int)).toNat = p := W64_toNat_lt p hbnd
  refine ⟨hbnd, ?_⟩
  obtain ⟨-, -, hbr, hlf⟩ := hall j e p he hpj
  by_cases hin : B.ib.root' = W64 0
  · have hrt0 : rt = 0 := by rw [← hrt, hin]; rfl
    have hhd0 : pids[0]? = some 0 := by rw [← List.head?_eq_getElem?, hhd, hrt0]
    have hlen1 : els.length = 1 := by
      have hpos' : 0 < els.length := List.length_pos_iff.2 hne
      rcases Nat.lt_or_ge 1 els.length with h1 | h1
      · exfalso
        obtain ⟨e0, he0⟩ : ∃ e0, els[0]? = some e0 := ⟨_, List.getElem?_eq_getElem hpos'⟩
        obtain ⟨pg, hpg, -⟩ := (hall 0 e0 0 he0 hhd0).2.2.1 (by omega)
        have := (Read.viewWF_page _ hv _ _ hpg).1; omega
      · omega
    have hj0 : j = 0 := by omega
    subst hj0
    have hp0 : p = 0 := by rw [hhd0] at hpj; cases hpj; rfl
    subst hp0
    obtain ⟨x, hx⟩ : ∃ x, ltree X bl (W64 ((0 : Nat) : Int)) = some x := by
      unfold ltree; rw [hB]; unfold resolve; simp only [hin, ite_true]
      by_cases hrn : B.bv.rootNode' = null
      · simp [hrn, wpageAt, hin]
      · obtain ⟨-, r, hr, -⟩ := hcl.2.2.2.2.1 _ _ (hcl.2.2.2.1 hrn)
        simp [hrn, hr]
    obtain ⟨lf, ws⟩ := x
    exact ⟨lf, ws, hx, fun h => by omega, fun _ => ltree_inline_leaf X bl B hok hB hin _ lf ws hx⟩
  · have hres : resolve B (W64 (p : Int)) = B.nm !! W64 (p : Int) := resolve_tree B _ hin
    by_cases hj : j + 1 < els.length
    · obtain ⟨pg, hpg, hf, hi, hnx⟩ := hbr hj
      cases hm : B.nm !! W64 (p : Int) with
      | some l =>
        obtain ⟨-, r, hr, hpgid⟩ := hcl.2.2.2.2.1 _ l hm
        have hnp := htp l r hr
        cases hlr : r.nv.isLeaf' with
        | true =>
          exfalso
          obtain ⟨pg', hpg', hf'⟩ := (hnp.1 hlr).2 hin
          rw [hpgid, hP, hpg] at hpg'; cases hpg'
          rw [hf] at hf'; exact absurd hf' (by decide)
        | false =>
          obtain ⟨pg', hpg', -, hwl, hwp⟩ := (hnp.2 hlr).2
          rw [hpgid, hP, hpg] at hpg'; cases hpg'
          have hlt : e.index'.toNat < r.ws.length := by rw [hwl]; exact hi
          have hL := ltree_node X bl B _ l r hB (by rw [hres, hm]) hr
          rw [hlr] at hL
          exact ⟨false, r.ws, hL, fun _ => ⟨rfl, r.ws[e.index'.toNat], branchPgid pg e.index'.toNat,
            List.getElem?_eq_getElem hlt, hnx, hwp _ _ (List.getElem?_eq_getElem hlt)⟩,
            fun h => by omega⟩
      | none =>
        have hw : wpageAt X.v B (W64 (p : Int)) = some (pageLoc X.v p, pg) := by
          unfold wpageAt; simp only [hin, ite_false, hP, hpg]; rfl
        have hL := ltree_page X bl B _ _ pg hB (by rw [hres, hm]) hw
        have hd : decide (pageFlags pg = leafPageFlag) = false := by rw [hf]; decide
        rw [hd] at hL
        exact ⟨false, pageWs pg, hL, fun _ => ⟨rfl, pageW pg e.index'.toNat, _,
          pageWs_get pg _ hi, hnx, (pageW_branch pg _ hf).2⟩, fun h => by omega⟩
    · have hjl : j + 1 = els.length := by omega
      obtain ⟨pg, hpg, hf⟩ : ∃ pg, X.v.pages !! p = some pg ∧ pageFlags pg = leafPageFlag := by
        rcases hlf hjl with h0 | h
        · exfalso
          subst h0
          rcases hpos j 0 hpj with ⟨-, h⟩ | ⟨⟨pg, hpg⟩, -⟩
          · apply hin; apply BitVec.eq_of_toNat_eq; rw [hrt, ← h]; rfl
          · have := (Read.viewWF_page _ hv _ _ hpg).1; omega
        · exact h
      cases hm : B.nm !! W64 (p : Int) with
      | some l =>
        obtain ⟨-, r, hr, hpgid⟩ := hcl.2.2.2.2.1 _ l hm
        have hnp := htp l r hr
        cases hlr : r.nv.isLeaf' with
        | false =>
          exfalso
          obtain ⟨pg', hpg', hf', -⟩ := (hnp.2 hlr).2
          rw [hpgid, hP, hpg] at hpg'; cases hpg'
          rw [hf] at hf'; exact absurd hf' (by decide)
        | true =>
          have hL := ltree_node X bl B _ l r hB (by rw [hres, hm]) hr
          rw [hlr] at hL
          exact ⟨true, r.ws, hL, fun h => by omega, fun _ => rfl⟩
      | none =>
        have hw : wpageAt X.v B (W64 (p : Int)) = some (pageLoc X.v p, pg) := by
          unfold wpageAt; simp only [hin, ite_false, hP, hpg]; rfl
        have hL := ltree_page X bl B _ _ pg hB (by rw [hres, hm]) hw
        have hd : decide (pageFlags pg = leafPageFlag) = true := decide_eq_true hf
        rw [hd] at hL
        exact ⟨true, pageWs pg, hL, fun h => by omega, fun _ => rfl⟩

/-- **A cursor stack's positions are a logical stack**: over the current references, a writer
stack (`sPathR` from the bucket's root `rt`) is an `lPath` at the same positions (each below
`2 ^ 64`). -/
theorem sPathR_lPath (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl X.v bl rt els pids) :
    lPath X bl (curRefs X B pids els) (pids.map fun (p : Nat) => W64 (p : Int)) ∧
    ∀ p ∈ pids, p < 2 ^ 64 := by
  have hpp := hp
  obtain ⟨hne, hlen, hhd, -⟩ := hp
  have hcl_len : (curRefs X B pids els).length = els.length := by
    simp [curRefs, List.length_zipWith, hlen]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h
    have := congrArg List.length h
    rw [hcl_len] at this
    exact hne (List.length_eq_zero_iff.1 this)
  · simp [hcl_len, hlen]
  · rw [List.head?_map, hhd]; simp only [Option.map_some]; rw [← hc.2.2.2.1]
    exact congrArg some (w64_cast_toNat _)
  · intro j e' p' he' hp'
    obtain ⟨p, e, hpj, he, rfl⟩ := curRefs_get X B pids els j e' he'
    rw [List.getElem?_map, hpj] at hp'
    simp only [Option.map_some, Option.some.injEq] at hp'
    subst hp'
    obtain ⟨-, lf, ws, hL, hbr, hlf⟩ := sPathR_pos X n bl rt B hc hB nl els pids hpp j e p he hpj
    refine ⟨curRef_refAt X bl B _ e _ hB hL, lf, ws, hL, ?_, ?_⟩
    · intro hj
      rw [hcl_len] at hj
      obtain ⟨h1, w, p2, hw, hp2, hwp⟩ := hbr hj
      refine ⟨h1, w, ?_, ?_⟩
      · rw [curRef_index]; exact hw
      · rw [List.getElem?_map, hp2, hwp]; rfl
    · intro hj; rw [hcl_len] at hj; exact hlf hj
  · intro p hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < els.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    exact (sPathR_pos X n bl rt B hc hB nl els pids hpp j _ p
      (List.getElem?_eq_getElem hjl) hj).1

/-- The current references keep the indices, so the bounds, the leaf index and the position. -/
theorem curRefs_index (X : WX) (B : BRec) (pids : List Nat) (els : List elemRef)
    (hl : pids.length = els.length) :
    (curRefs X B pids els).map (·.index') = els.map (·.index') ∧
    (curRefs X B pids els).length = els.length ∧
    pathBnd X.v pids (curRefs X B pids els) = pathBnd X.v pids els ∧
    leafIdx (curRefs X B pids els) = leafIdx els := by
  have hm := curRefs_map_index X B pids els hl
  have hlen : (curRefs X B pids els).length = els.length := by
    simp [curRefs, List.length_zipWith, hl]
  refine ⟨hm, hlen, pathBndFrom_index _ _ _ _ _ hm, ?_⟩
  have h2 := congrArg List.getLast? hm
  rw [List.getLast?_map, List.getLast?_map] at h2
  unfold leafIdx
  have h3 := congrArg (Option.map fun i : w64 => i.toNat) h2
  simp only [Option.map_map] at h3
  exact congrArg (fun o => Option.getD o 0) h3

end stkLeaf

end WBridge

end bbolt
end EtcdGrove
end Perennial
