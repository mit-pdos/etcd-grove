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

/-- **A node reference the registry names is current**: a registered node of the opened bucket at
`(bl, pid)` is what the bucket resolves `pid` to. -/
theorem nodeRef_current (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (l : Loc) (pid : Nat)
    (hl : l ≠ null) (hnl : X.nloc !! l = some (bl, pid)) :
    resolve B (W64 (pid : Int)) = some l := by
  sorry

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
  sorry

end stkLeaf

end WBridge

end bbolt
end EtcdGrove
end Perennial
