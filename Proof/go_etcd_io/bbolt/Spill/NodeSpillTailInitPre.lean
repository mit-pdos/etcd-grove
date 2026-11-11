/-
`node.spill` after its children's loop (U9w, `notes/bbolt-proof-plan.md`; pure): **helpers of
`pcInv_pre`**: the spill's global state across a piece's free (`spG_pcFreed`), an entry's page in
its slots (`fTree_root_slot`), and an allocation never returning an owned slot
(`allocRes_not_owned`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureG
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureAlloc
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pre
variable [GooseExts] [GoGlobalContext]

/-- `spG` reads only the freelist's free ids. -/
theorem spG_fl {X : WX} {txid : w64} {ml : Nat} {fl fl' : FLPg} (hf : fl'.free = fl.free)
    (h : spG X txid ml fl) : spG X txid ml fl' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun id hid => by rw [hf]; exact a8 id hid, a9.1, a9.2.1,
    by rw [hf]; exact a9.2.2⟩

theorem freePages_free (fl : FLPg) (txid id : w64) (n : Nat) :
    (fl.freePages txid id n).free = fl.free := rfl

/-- **The spill's global state across a piece's free** (`pieceOne_wp`'s `hG`). -/
theorem spG_pcFreed {X : WX} {w : WDb} {bl l : Loc} {r : NRec} (hn : X.node bl l = some r)
    (hl : l ∈ X.live) (hG : spG X w.wtxid (mapLen w.ms) w.fl) :
    ∀ X1 w1 st, pcFreed X w bl l r X1 w1 st → spG X1 w.wtxid (mapLen w1.ms) w1.fl := by
  intro X1 w1 st hf
  rcases hf with ⟨-, rfl, rfl, -⟩ | ⟨pg, -, -, rfl, rfl, -⟩
  · exact hG
  · obtain ⟨B, hB, hr⟩ := node_bsQ hn
    have hd := (hG.2.2.1.1 bl B l r hB hr hl)
    have hf := hG.2.2.2.1 bl B l r hB hr hl
    refine spG_fl (freePages_free _ _ _ _) ?_
    exact spG_setNode (r' := { r with nv := { r.nv with pgid' := W64 0 } }) hn ⟨rfl, rfl⟩ rfl hd.2.1 hd.2.2.1 hf.1 hf.2 hG

/-- A page is among its slots. -/
theorem mem_pgSlots_self_ {P : Pages} {S : List Nat} {x : Nat} (hx : x ∈ S) :
    x ∈ pgSlots P S := by
  unfold pgSlots
  refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
  cases P !! x with
  | none => simp
  | some pg => simp; omega

/-- **A finished subtree's root page is among its slots.** -/
theorem fTree_root_slot {P : Pages} {hwm id : Nat} {k : List w8} {hi : Option (List w8)}
    {h : Nat} {S : List Nat} {E : List El} (hf : fTree P hwm id k hi h S E) :
    id ∈ pgSlots P S := by
  obtain ⟨hs, ⟨pg, hpg, -⟩, -⟩ := hf
  exact mem_pgSlots_self_ ((hs.has id).1 (treeHas.root _ pg hpg))

/-- **An allocation never returns an owned slot** (`slotInv`: owned slots are below the mark and
no free id). -/
theorem allocRes_not_owned {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} {L : List Nat} (h : allocRes X X' fl fl' txid count p id)
    (hs : slotInv fl X.t.mv.pgid'.toNat L) {s : Nat} (hsL : s ∈ L) : id.toNat ≠ s := by
  obtain ⟨hc, -, Xr, -, hX'⟩ := h
  obtain ⟨hlt, h62, hnot⟩ := hs.2.1 s hsL
  rcases hX' with ⟨⟨-, hrun⟩, -, -⟩ | ⟨rfl, -, -, -⟩
  · intro e
    have hm := hrun id ⟨Nat.le_refl _, by omega⟩
    apply hnot
    have : W64 (s : Int) = id := by
      apply BitVec.eq_of_toNat_eq; rw [← e]; simp <;> omega
    rw [this]; exact List.mem_append_left _ hm
  · omega

end pre

end Spill

end bbolt
end EtcdGrove
end Perennial
