/-
The pure facts of `Open`'s core phase (U11c): the page store's invariant `storeOK` of the opened
state (`Open/Core.openSigma`) from `fileHolds`' facts: the tree's pages are the file's slots'
bytes, each slot a page's 4096 bytes, at least 2 (a tree page is a `treeWF` root).
-/
module

public import Proof.go_etcd_io.bbolt.Open.Core
public import Proof.go_etcd_io.bbolt.Inv.FileHolds
public import Proof.go_etcd_io.bbolt.Read.TreeFacts
public import Proof.go_etcd_io.bbolt.Spill.STree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Spill Read

section facts
variable [GooseExts]

/-- A page's header is in its first 16 bytes. -/
theorem pageOverflow_take (pg : List w8) (n : Nat) (h : 16 ≤ n) :
    pageOverflow (pg.take n) = pageOverflow pg := by
  unfold pageOverflow pageHdr bytesAt
  simp only [List.drop_zero, List.take_take, Nat.min_eq_left h]

/-- A page of the file: its overflow is its first slot's. -/
theorem filePage_overflow (xs : List w8) (id : Nat) :
    pageOverflow (filePage xs id) = pageOverflow (bytesAt xs (4096 * id) 4096) := by
  unfold filePage bytesAt
  rw [pageOverflow_take _ _ (by
      have := Nat.mul_le_mul_right 4096 (Nat.succ_le_succ (Nat.zero_le
        (pageOverflow ((xs.drop (4096 * id)).take 4096)))); omega),
    pageOverflow_take _ _ (by omega)]

omit [GooseExts] in
/-- `k` slots of the file from slot `id`, inside it, are its bytes there. -/
theorem bytesAt_slots (xs : List w8) :
    ∀ (k id : Nat), bytesAt xs (4096 * id) (k * 4096) =
      (List.range' id k).flatMap (fun s => bytesAt xs (4096 * s) 4096)
  | 0, id => by simp [bytesAt]
  | k + 1, id => by
    rw [List.range'_succ, List.flatMap_cons, ← bytesAt_slots xs k (id + 1)]
    unfold bytesAt
    rw [show (k + 1) * 4096 = 4096 + k * 4096 by omega, List.take_add, List.drop_drop,
      show 4096 * id + 4096 = 4096 * (id + 1) by omega]

/-- A tree page of a well-formed committed state roots a well-formed tree, so its id is at least
2. -/
theorem tree_page_ge2 (C : CommitSt) (h : treeOK C) (id : Nat) (pg : List w8)
    (hp : C.pages !! id = some pg) : 2 ≤ id := by
  obtain ⟨⟨hwf, -⟩, htp, -⟩ := h
  have hhas : treeHas C.pages C.root id := by
    rw [← htp] at hp
    rw [treePages_lookup] at hp
    split at hp
    · assumption
    · cases hp
  cases treeHas_treeWF C.pages C.hwm hhas hwf with
  | page _ _ h2 _ _ _ _ _ => exact h2

omit [GooseExts] in
/-- A lookup in a map built from a list of keys. -/
theorem ofList_map_lookup {V : Type} (f : Nat → V) :
    ∀ (l : List Nat) (id : Nat) (v : V),
      (GMap.ofList (l.map fun i => (i, f i))) !! id = some v → v = f id ∧ id ∈ l
  | [], id, v, h => by cases h
  | a :: l, id, v, h => by
    simp only [List.map_cons, GMap.ofList] at h
    by_cases ha : a = id
    · subst ha
      rw [GMap.lookup_insert] at h
      cases h; exact ⟨rfl, List.mem_cons_self⟩
    · rw [GMap.lookup_insert_ne _ _ ha] at h
      obtain ⟨h1, h2⟩ := ofList_map_lookup f l id v h
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- A tree page of a file image is the file's page there. -/
theorem image_page (xs : List w8) (C : CommitSt) (himg : fileImage xs C) (id : Nat)
    (pg : List w8) (hp : C.pages !! id = some pg) : pg = filePage xs id := by
  obtain ⟨-, -, hpg⟩ := himg
  rw [hpg] at hp
  have := treePages_le _ _ id pg hp
  exact (ofList_map_lookup (filePage xs) _ id pg this).1

/-- No pending page in the empty freelist. -/
theorem pendSlots_empty' : pendSlots FLPg.empty = [] := by
  unfold pendSlots FLPg.pendingIds FLPg.empty
  simp

/-- The tree's slots: covered by a tree page. -/
theorem open_slot (xs : List w8) (C : CommitSt) (htree : treeOK C)
    (hhwm : C.hwm * 4096 ≤ xs.length) (s : Nat) (hs : s ∈ slotsOf C FLPg.empty) :
    2 ≤ s ∧ s < C.hwm ∧ (bytesAt xs (4096 * s) 4096).length = 4096 := by
  rw [mem_slotsOf, pendSlots_empty'] at hs
  simp only [List.not_mem_nil, or_false] at hs
  unfold treeSlots at hs
  rw [mem_pagesSlots_iff] at hs
  obtain ⟨id, pg, hp, h1, h2⟩ := hs
  have hge := tree_page_ge2 C htree id pg hp
  have hlt := htree.2.2.2.1 id pg hp
  refine ⟨by omega, by omega, ?_⟩
  unfold bytesAt
  simp only [List.length_take, List.length_drop]
  omega

/-- **The page store's invariant of the opened state** (`Open/Core.openSigma`), from
`fileHolds`' facts: the file `xs` mapped at `b` for `L` bytes, at least the file. -/
theorem storeOK_open (xs : List w8) (C : CommitSt) (b : Loc) (L : Nat)
    (himg : fileImage xs C) (hmeta : C.metaOk) (htree : treeOK C)
    (hhwm : C.hwm * 4096 ≤ xs.length) (hL : xs.length ≤ L) (hsz : xs.length < 2 ^ 63)
    (htx : C.txid < 2 ^ 62) :
    storeOK (openSigma b L C (fun s => bytesAt xs (4096 * s) 4096)) := by
  have hslot := open_slot xs C htree hhwm
  have hcov : ∀ s, coversSlot C.pages s → 2 ≤ s := by
    intro s ⟨id, pg, hp, h1, _⟩
    have := tree_page_ge2 C htree id pg hp; omega
  unfold storeOK
  simp only [openSigma]
  refine ⟨hmeta, htree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [FLPg.empty, FLPg.pendingIds] <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [FLPg.empty, FLPg.allIds, FLPg.pendingIds, PgidsIncr]
  · intro w h; cases h
  · intro _; first | rfl | trivial
  · intro k r h; cases h
  · intro v h; cases h
  · intro id pg hp
    rw [image_page xs C himg id pg hp, filePage_overflow]
    have hlt := htree.2.2.2.1 id pg hp
    rw [image_page xs C himg id pg hp, filePage_overflow] at hlt
    unfold filePage
    exact bytesAt_slots xs _ id
  · intro k r h; cases h
  · intro v h; cases h
  · intro s hs; exact ⟨(hslot s hs).1, (hslot s hs).2.2⟩
  · intro b' l h s hs
    cases h
    have := (hslot s hs).2.1
    omega
  · intro h; cases h
  · intro _; first | rfl | trivial
  · intro _; first | rfl | trivial
  · intro s _; left; rw [pendSlots_empty']; simp
  · intro b'
    unfold mvccView
    refine ⟨fun id pg _ a h => (by cases h), fun s hs => ⟨hcov s hs, (by simp [FLPg.empty]),
      fun t pd i h => (by cases h)⟩⟩
  · intro x a h; cases h
  · intro _ s hs; rw [pendSlots_empty'] at hs; cases hs
  · omega

/-- **The writer side's invariant once the freelist is loaded** (`Open/Core.open_writer`'s
`wdbOK`): `openW` with the loaded freelist `fl` (no pending page; free ids below the mark, not
tree slots; the synced page reloadable) and its interface `fli`, the mapping `(b, L)` at least the
file `xs` (`m`'s bytes), registered in `m`. -/
theorem wdbOK_open (xs : List w8) (C : CommitSt) (b : Loc) (L : Nat) (m : OsMeta) (f : Loc)
    (fd : w64) (fl : FLPg) (fli : GoInterface)
    (htree : treeOK C) (hhwm : C.hwm * 4096 ≤ xs.length) (hxs : xs.length = m.size)
    (hL : m.size ≤ L) (hsz : m.size < 2 ^ 63) (htx : C.txid < 2 ^ 62)
    (hmaps : m.maps = GMap.singleton b L)
    (hpend : fl.pending = ∅)
    (hfree : ∀ x ∈ fl.free, x.toNat < C.hwm ∧ x.toNat ∉ treeSlots C)
    (hcur : ∀ g, C.flpg = some g →
      flCurOK fl C (extentBytes (fun s => bytesAt xs (4096 * s) 4096) g))
    (hfd : 0 ≤ fd.toInt) :
    wdbOK { openW C b L m (fun s => bytesAt xs (4096 * s) 4096) f fd with fl := fl, fli := fli } := by
  have hps : pendSlots fl = [] := by
    unfold pendSlots FLPg.pendingIds; rw [hpend]; simp
  have hlt : ∀ s, s ∈ treeSlots C → s < C.hwm := by
    intro s hs
    unfold treeSlots at hs
    rw [mem_pagesSlots_iff] at hs
    obtain ⟨id, pg, hp, h1, h2⟩ := hs
    have := htree.2.2.2.1 id pg hp; omega
  unfold wdbOK
  simp only [openW, mapLen]
  refine ⟨?_, ?_, by omega, ?_, fun x hx => (hfree x hx).2, hcur, by omega, by omega, ?_, ?_, ?_,
    fun x hx => (hfree x hx).1, by omega, ?_, ?_, ?_, ?_⟩
  · intro b' l h; cases h; exact hmaps
  · intro h; cases h
  · intro s
    rw [mem_wSlots, mem_slotsOf, hps, Nat.max_eq_left hL, pendSlots_empty']
    simp
  · intro b' l h; cases h; omega
  · intro b' l h _; cases h; exact hL
  · intro s hs
    rw [hps] at hs
    simp only [List.not_mem_nil, or_false] at hs
    exact hlt s hs
  · intro b' l h; cases h; left; exact hL
  · intro s _ hs
    unfold bytesAt
    simp only [List.length_take, List.length_drop]
    omega
  · intro s _ _
    unfold bytesAt
    simp only [List.length_take, List.length_drop]
    omega
  · exact hfd

end facts

end bbolt
end EtcdGrove
end Perennial
