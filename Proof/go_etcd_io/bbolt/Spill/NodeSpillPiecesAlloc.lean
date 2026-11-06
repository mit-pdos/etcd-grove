/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`; pure): **what a
successful `allocate` leaves** (`allocRes`): every node's record modulo sources (`allocRes_node`,
through `dereference`'s step and the remap's `unview`), liveness, and the allocated buffer
(`allocRes_buf`: in the page cache at `p`, a zeroed page with its header).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section alloc
variable [GooseExts]

theorem nodeStep_nodeSim {r r' : NRec} (h : nodeStep r r') : nodeSim r r' := by
  rcases h with h | ⟨h1, h2, h3, -, h5, h6, h7, h8, -⟩
  · subst h; exact nodeSim_refl _
  · exact ⟨h1, h2, h3, h5, h6, h7, h8⟩

theorem unview_nodeSim (r : NRec) :
    nodeSim r { r with ws := r.ws.map fun w => { w with ks := w.ks.unview, vs := w.vs.unview },
                       ksrc := r.ksrc.unview } := by
  refine ⟨rfl, Iff.rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.map_map]
  rfl

theorem derefStep_node {X X' : WX} (h : derefStep X X') {bl l : Loc} {r : NRec}
    (hn : X.node bl l = some r) : ∃ r', X'.node bl l = some r' ∧ nodeSim r r' := by
  have hb := h.2.2.2.2.2.2.2.2.2.2.2.2 bl
  unfold WX.node at hn ⊢
  cases e : X.t.bs !! bl with
  | none => rw [e] at hn; cases hn
  | some B =>
    rw [e] at hn hb
    simp only [Option.bind_some] at hn
    cases e' : X'.t.bs !! bl with
    | none => rw [e'] at hb; exact absurd hb (by simp [optRel])
    | some B' =>
      rw [e'] at hb
      have hl := hb.2 l
      rw [hn] at hl
      cases e'' : B'.ns !! l with
      | none => rw [e''] at hl; exact absurd hl (by simp [optRel])
      | some r' =>
        rw [e''] at hl
        exact ⟨r', by simp [e''], nodeStep_nodeSim hl⟩

theorem rebase_node {X : WX} (b : Loc) {bl l : Loc} {r : NRec} (hn : X.node bl l = some r) :
    ∃ r', (X.rebase b).node bl l = some r' ∧ nodeSim r r' := by
  unfold WX.node at hn ⊢
  cases e : X.t.bs !! bl with
  | none => rw [e] at hn; cases hn
  | some B =>
    rw [e] at hn
    simp only [Option.bind_some] at hn
    refine ⟨_, ?_, unview_nodeSim r⟩
    simp only [WX.rebase, GMap.lookup_fmap, e, Option.map_some, Option.bind_some, BRec.unview, hn]

theorem addPage_node (X : WX) (id : w64) (p : Loc) (count : Nat) (hwm : w64) (bl l : Loc) :
    (X.addPage id p count hwm).node bl l = X.node bl l := rfl

/-- **A successful `allocate` keeps every node's record modulo sources**, and its liveness. -/
theorem allocRes_node {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc} {id : w64}
    (h : allocRes X X' fl fl' txid count p id) {bl l : Loc} {r : NRec}
    (hn : X.node bl l = some r) :
    (∃ r', X'.node bl l = some r' ∧ nodeSim r r') ∧ (l ∈ X'.live ↔ l ∈ X.live) := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hR : (∃ r', Xr.node bl l = some r' ∧ nodeSim r r') ∧ (l ∈ Xr.live ↔ l ∈ X.live) := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · exact ⟨⟨r, hn, nodeSim_refl r⟩, Iff.rfl⟩
    · obtain ⟨r1, h1, s1⟩ := derefStep_node hdr.2.2.2.2.2.2.2.2.2.2.2.2.2 hn
      obtain ⟨r2, h2, s2⟩ := rebase_node b h1
      refine ⟨⟨r2, h2, nodeSim_trans s1 s2⟩, ?_⟩
      show l ∈ Xd.live ↔ l ∈ X.live
      rw [hdr.2.2.1]
  rcases hX' with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> exact hR

/-- **The buffer a successful `allocate` adds**: at `p` in the page cache, a zeroed page of
`count` slots with its header. -/
theorem allocRes_buf {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc} {id : w64}
    (h : allocRes X X' fl fl' txid count p id) :
    X'.t.pm !! id = some p ∧ X'.t.bufs !! id = some
      (encode (⟨id, W16 0, W16 0, W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (count * 4096 - 16) (W8 0)) := by
  obtain ⟨-, -, Xr, -, hX'⟩ := h
  rcases hX' with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
    exact ⟨GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩

end alloc

end Spill

end bbolt
end EtcdGrove
end Perennial
