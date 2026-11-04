/-
`Commit`'s publish facts (U10k of `notes/bbolt-proof-plan.md`): what the tail (`write`,
`writeMeta`, the publish) needs of the records `X` and the writer side `w` where the freelist's
branches join (`cmPubPre`: the dirty pages, the meta, the new tree `Pg` and its committed state
`pubC w.C X.t.mv Pg`), and the tail's pure steps from it.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailMeta
public import Proof.go_etcd_io.bbolt.Commit.TailWrite
public import Proof.go_etcd_io.bbolt.Inv.Publish

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The publish's facts at the join** (see the file header), for the transaction's data `D`:
the dirty pages (`tx.pages`' buffers: whole pages in `[2, pgid)`, pairwise disjoint, outside the
committed tree, the pending ids and the free ids), the meta (`writeMeta`'s bounds, valid), and the
new tree's pages `Pg`: its committed state `pubC w.C X.t.mv Pg` well-formed, holding `D`, its
dropped slots pending, its pages the committed ones or buffers, its new synced freelist page a
buffer that reloads the freelist `w.fl`. -/
def cmPubPre (D : Data) (X : WX) (w : WDb) : Prop :=
  (∀ id, (X.t.pm !! id).isSome = (X.t.bufs !! id).isSome) ∧
  (∀ id pg, X.t.bufs !! id = some pg → pageId pg = id.toNat ∧
    pg.length = 4096 * (1 + pageOverflow pg) ∧ 2 ≤ id.toNat ∧
    id.toNat + (1 + pageOverflow pg) ≤ X.t.mv.pgid'.toNat) ∧
  (bufSlots X.t.bufs).Nodup ∧
  (∀ s ∈ bufSlots X.t.bufs, s ∉ treeSlots w.C ∧ s ∉ pendSlots w.fl ∧ W64 (s : Int) ∉ w.fl.free) ∧
  uint.Z X.t.mv.root'.root' < uint.Z X.t.mv.pgid' ∧
  (uint.Z X.t.mv.freelist' < uint.Z X.t.mv.pgid' ∨ X.t.mv.freelist'.toNat = pgidNoFreelist) ∧
  2 ≤ w.C.hwm ∧ metaValid (metaSummed X.t.mv) ∧ (metaSummed X.t.mv).pageSize'.toNat = 4096 ∧
  ∃ Pg : Pages,
    treeData (pubC w.C X.t.mv Pg) = D ∧ treeOK (pubC w.C X.t.mv Pg) ∧
    (pubC w.C X.t.mv Pg).hwm ≤ 2 ^ 62 ∧
    (∀ s ∈ treeSlots w.C, s ∉ treeSlots (pubC w.C X.t.mv Pg) → s ∈ pendSlots w.fl) ∧
    (∀ s ∈ treeSlots (pubC w.C X.t.mv Pg), s ∉ pendSlots w.fl) ∧
    flBelow w.fl (pubC w.C X.t.mv Pg) (some (w.C.txid + 1)) ∧
    (∀ id pg, Pg !! id = some pg → w.C.pages !! id = some pg ∨ X.t.bufs !! W64 (id : Int) = some pg) ∧
    (∀ s ∈ treeSlots (pubC w.C X.t.mv Pg), s ∈ slotsOf w.C w.fl ∨ s ∈ bufSlots X.t.bufs) ∧
    (∀ f, (pubC w.C X.t.mv Pg).flpg = some f → ∃ pg, X.t.bufs !! W64 (f : Int) = some pg ∧
      flCurOK w.fl (pubC w.C X.t.mv Pg) pg)

/-- `cmPubPre` reads the writer side's committed state and freelist only. -/
theorem cmPubPre_congr (D : Data) (X : WX) (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (h : cmPubPre D X w) : cmPubPre D X w' := by
  unfold cmPubPre; rw [hC, hfl]; exact h

omit [GooseExts] in
/-- The slots `SB` (inside `W`, no duplicates) and the rest of `W` are `W`. -/
theorem mem_SB_wMinus (W SB : List Nat) (hsub : ∀ s ∈ SB, s ∈ W) (s : Nat) :
    s ∈ SB ++ wMinus W SB ↔ s ∈ W := by
  simp only [List.mem_append, wMinus, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact hsub s h
    · exact h
  · intro h
    by_cases hs : s ∈ SB
    · exact Or.inl hs
    · exact Or.inr ⟨h, hs⟩

/-- **The writer side after a write of the slots `SB`** (all of them, or after an error): `wdbOK`
with `SB` back among the `W` slots, holding the write's bytes. -/
theorem wdbOK_written (w : WDb) (m : OsMeta) (SB : List Nat) (wb' : Nat → List w8) (hok : wdbOK w)
    (hsub : ∀ s ∈ SB, s ∈ w.W) (hsz : m.size = w.m.size) (hmaps : m.maps = w.m.maps)
    (hlen : ∀ s ∈ SB, (wb' s).length = 4096) (hfl : w.C.flpg = none) :
    wdbOK (w.reslot m (SB ++ wMinus w.W SB) (wbUpd SB wb' w.wb)) := by
  apply wdbOK_reslot w m _ _ hok (mem_SB_wMinus w.W SB hsub) hsz hmaps
  · intro s hs hz
    unfold wbUpd
    split
    · exact hlen s (by assumption)
    · exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s hs hz
  · intro f hf; rw [hfl] at hf; cases hf

end pure

end bbolt
end EtcdGrove
end Perennial
