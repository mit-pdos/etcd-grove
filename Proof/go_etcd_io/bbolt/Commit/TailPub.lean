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

/-- **The new tree's facts** (`cmPubPre`'s last part): its pages `Pg`, its committed state
`pubC w.C X.t.mv Pg` well-formed, holding the data `D`, its dropped slots pending, its pages the
committed ones or buffers, its slots store slots or the buffers', its new synced freelist page a
buffer that reloads the freelist `w.fl`. -/
def cmPubPg (D : Data) (X : WX) (w : WDb) (Pg : Pages) : Prop :=
  treeData (pubC w.C X.t.mv Pg) = D ∧ treeOK (pubC w.C X.t.mv Pg) ∧
  (pubC w.C X.t.mv Pg).hwm ≤ 2 ^ 62 ∧
  (∀ s ∈ treeSlots w.C, s ∉ treeSlots (pubC w.C X.t.mv Pg) → s ∈ pendSlots w.fl) ∧
  (∀ s ∈ treeSlots (pubC w.C X.t.mv Pg), s ∉ pendSlots w.fl) ∧
  flBelow w.fl (pubC w.C X.t.mv Pg) (some (w.C.txid + 1)) ∧
  (∀ id pg, Pg !! id = some pg → w.C.pages !! id = some pg ∨ X.t.bufs !! W64 (id : Int) = some pg) ∧
  (∀ s ∈ treeSlots (pubC w.C X.t.mv Pg), s ∈ slotsOf w.C w.fl ∨ s ∈ bufSlots X.t.bufs) ∧
  (∀ f, (pubC w.C X.t.mv Pg).flpg = some f → ∃ pg, X.t.bufs !! W64 (f : Int) = some pg ∧
    flCurOK w.fl (pubC w.C X.t.mv Pg) pg)

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
  ∃ Pg : Pages, cmPubPg D X w Pg

/-- `cmPubPre` reads the writer side's committed state and freelist only. -/
theorem cmPubPre_congr (D : Data) (X : WX) (w w' : WDb) (hC : w'.C = w.C) (hfl : w'.fl = w.fl)
    (h : cmPubPre D X w) : cmPubPre D X w' := by
  unfold cmPubPre cmPubPg at *; rw [hC, hfl]; exact h

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

/-- The `W` slots outside the written slots `SB ++ cmTail` lie inside the file. -/
theorem cm_rest (w : WDb) (SB : List Nat) (l : Nat)
    (hinW : ∀ s ∈ w.W, l / 4096 ≤ s → 4096 * (s + 1) ≤ w.m.size) :
    ∀ s ∈ w.W, s ∉ SB ++ cmTail w SB l → 4096 * (s + 1) ≤ w.m.size := by
  intro s hsW hsn
  by_cases hlt : s < l / 4096
  · apply Nat.le_of_not_lt
    intro hgt
    apply hsn
    by_cases hSB : s ∈ SB
    · exact List.mem_append_left _ hSB
    · exact List.mem_append_right _ ((mem_cmTail _ _ _ s).2 ⟨hlt, hsW, hgt, hSB⟩)
  · exact hinW s hsW (by omega)

/-- **The writer side after a write of the slots `SBT`** (`W` slots; after an error): `wdbOK`
with `SBT` back among the `W` slots, holding the write's bytes, the file grown at most to the
mapping's end. -/
theorem wdbOK_written (w : WDb) (m : OsMeta) (SBT : List Nat) (wb' : Nat → List w8)
    (hok : wdbOK w) (hsub : ∀ s ∈ SBT, s ∈ w.W) (hsz1 : w.m.size ≤ m.size)
    (hsz2 : m.size ≤ max w.m.size (mapLen w.ms)) (hsz63 : m.size < 2 ^ 63)
    (hmaps : m.maps = w.m.maps)
    (hlen : ∀ s ∈ SBT, 4096 * (s + 1) ≤ m.size → (wb' s).length = 4096)
    (hold : ∀ s ∈ w.W, s ∉ SBT → 4096 * (s + 1) ≤ w.m.size) (hfl : w.C.flpg = none) :
    wdbOK (w.reslot m (SBT ++ wMinus w.W SBT) (wbUpd SBT wb' w.wb)) := by
  apply wdbOK_reslot w m _ _ hok (mem_SB_wMinus w.W SBT hsub) hsz1 hsz2 hsz63 hmaps
  · intro s hs hz
    unfold wbUpd
    split
    · exact hlen s (by assumption) hz
    · exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s hs (hold s hs (by assumption))
  · intro f hf; rw [hfl] at hf; cases hf

@[simp] theorem WDb.reslot_reslot (w : WDb) (m m' : OsMeta) (W W' : List Nat)
    (wb wb' : Nat → List w8) : (w.reslot m W wb).reslot m' W' wb' = w.reslot m' W' wb' := rfl

/-- **The slots the commit publishes**: a dirty page's slot in the new tree that was no store
slot. -/
def pubP (w : WDb) (X : WX) (Pg : Pages) (s : Nat) : Bool :=
  decide (s ∈ treeSlots (pubC w.C X.t.mv Pg) ∧ s ∉ slotsOf w.C w.fl)

/-- **The write's premises** (`cm_write_step`) for the writer side `w` mapped at `(b, l)`, from
`cmPubPre`: the dirty pages below the high-water mark `X.t.mv.pgid'`, which lies inside the
mapping; the mapping's slots past the file's end and the `W` slots past the mapping. -/
theorem cm_write_pre (D : Data) (X : WX) (w : WDb) (b : Loc) (l : Nat) (hpre : cmPubPre D X w)
    (hok : wdbOK w) (hms : w.ms = some (b, l)) (hmapl : X.t.mv.pgid'.toNat * 4096 ≤ l) :
    bufsOK X.t.bufs (l / 4096) ∧ (∀ s ∈ bufSlots X.t.bufs, s ∈ w.W) ∧
      (∀ s, s < l / 4096 → w.m.size < 4096 * (s + 1) → s ∈ w.W) ∧
      (∀ s ∈ w.W, 4096 * (s + 1) ≤ w.m.size → (w.wb s).length = 4096) ∧
      (∀ s ∈ w.W, l / 4096 ≤ s → 4096 * (s + 1) ≤ w.m.size) := by
  obtain ⟨-, hb, -, hsl, -, -, h2, -⟩ := hpre
  have h3 := hok.2.2.1
  have h11 := hok.2.2.2.2.2.2.2.2.2.2.1
  have hlim : X.t.mv.pgid'.toNat ≤ l / 4096 :=
    (Nat.le_div_iff_mul_le (by decide)).2 hmapl
  have hml : mapLen w.ms = l := by rw [hms]; rfl
  refine ⟨fun id pg hp => ?_, fun s hs => ?_, fun s hs hgt => ?_, fun s hs hz =>
    hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2 s hs hz, fun s hs hle => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hb id pg hp
    exact ⟨h1, h2, h3, by omega⟩
  · obtain ⟨id, pg, hp, h1, h2⟩ := (mem_bufSlots X.t.bufs s).1 hs
    have := hb id pg hp
    obtain ⟨h3, h4, -⟩ := hsl s hs
    refine (hok.2.2.2.1 s).2 ⟨by omega, ?_, h3, h4⟩
    rw [hml]
    have : s < l / 4096 := by omega
    exact Nat.lt_of_lt_of_le this (Nat.div_le_div_right (Nat.le_max_left _ _))
  · refine (hok.2.2.2.1 s).2 ⟨?_, ?_, fun ht => ?_, fun hp => ?_⟩
    · omega
    · rw [hml]; exact Nat.lt_of_lt_of_le hs (Nat.div_le_div_right (Nat.le_max_left _ _))
    · have := h11 s (Or.inl ht); omega
    · have := h11 s (Or.inr hp); omega
  · have h4 := ((hok.2.2.2.1 s).1 hs).2.1
    rw [hml] at h4
    have h5 : s < max l w.m.size / 4096 := h4
    have : 4096 * (s + 1) ≤ max l w.m.size := by
      have := (Nat.lt_div_iff_mul_lt (by decide)).1 h5; omega
    have : l < 4096 * (s + 1) := by
      have := (Nat.div_le_iff_le_mul_add_pred (by decide)).1 hle; omega
    omega

end pure

end bbolt
end EtcdGrove
end Perennial
