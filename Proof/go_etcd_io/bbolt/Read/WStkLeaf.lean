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
  · unfold resolve; rw [if_pos hin]
    have hrn : B.bv.rootNode' ≠ null := by
      intro h0
      have := (hcl.2.2.1 h0).2
      rw [this] at hnm; simp at hnm
    rw [if_neg hrn]
    obtain ⟨-, r, hr, hpg⟩ := hcl.2.2.2.2.1 _ l hnm
    have hncl := hcl.2.2.2.2.2.2.2.1 l r hr
    have h0 : r.nv.pgid' = W64 0 := hncl.2.2.2.2.2.2.2.2.1 hin
    have h4 := hcl.2.2.2.1 hrn
    rw [hin, ← h0, hpg, hnm] at h4
    cases h4; rfl
  · rw [resolve_tree B _ hin]; exact hnm

/-- **A cursor stack's positions are a logical stack**: over the current references, a writer
stack (`sPathR` from the bucket's root `rt`) is an `lPath` at the same positions (each below
`2 ^ 64`). -/
theorem sPathR_lPath (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl X.v bl rt els pids) :
    lPath X bl (curRefs X B pids els) (pids.map fun (p : Nat) => W64 (p : Int)) ∧
    ∀ p ∈ pids, p < 2 ^ 64 := by
  sorry

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
