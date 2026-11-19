/-
**The file a closed database leaves** (session bbolt-inv, `DB.Close_own.spec`; pure): the bytes of
a database file whose writer side is idle, read slot by slot, the metas from `metaR`'s committed
state, a store slot from the store's bytes, any other slot from the writer side's `W` slots, are
an image of the committed state (`fileOK`): its tree's pages are the store's (`pagesFromBytes`),
its synced freelist page the writer's (`flCurOK`, `wdbOK`'s clause).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.FileImg
public import Proof.go_etcd_io.bbolt.Inv.Store
public import Proof.go_etcd_io.bbolt.Spill.STree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Spill

section img
variable [GooseExts]

/-- Slot `s` of the closed file: the metas, the store's bytes `bs` for a store slot, the writer
side's `wb` for the rest. -/
def closeSlot (C : CommitSt) (fl : FLPg) (bs wb : Nat → List w8) (s : Nat) : List w8 :=
  if s = 0 then C.m0 else if s = 1 then C.m1 else if s ∈ slotsOf C fl then bs s else wb s

/-- The closed file's bytes, `n` slots. -/
def closeBytes (C : CommitSt) (fl : FLPg) (bs wb : Nat → List w8) (n : Nat) : List w8 :=
  (List.range' 0 n).flatMap (closeSlot C fl bs wb)

/-- A page of a tree is a page of the map (`Spill/STreeMono.treeHas_page`'s, not imported here). -/
theorem treeHas_page_ci {P : Pages} {r y : Nat} (h : treeHas P r y) : ∃ pg, P !! y = some pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_2 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_3 := fun _ y _ => ∃ pg, P !! y = some pg)
    (fun _ pg hpg => ⟨pg, hpg⟩) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

/-- Runs of equal-length chunks: their length. -/
theorem flatMap_range'_length (g : Nat → List w8) (c a k : Nat)
    (h : ∀ s, a ≤ s → s < a + k → (g s).length = c) :
    ((List.range' a k).flatMap g).length = c * k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.flatMap_cons, List.length_append, h a (Nat.le_refl _) (by omega),
      ih (a + 1) (fun s h1 h2 => h s (by omega) (by omega)), Nat.mul_succ]
    omega

/-- A run of chunks from a run of `n` chunks of `4096` bytes. -/
theorem chunks_bytesAt (g : Nat → List w8) (n a k : Nat)
    (hg : ∀ s, s < n → (g s).length = 4096) (hak : a + k ≤ n) :
    bytesAt ((List.range' 0 n).flatMap g) (4096 * a) (4096 * k) = (List.range' a k).flatMap g := by
  have e1 : List.range' a k ++ List.range' (a + k) (n - (a + k)) = List.range' a (n - a) := by
    rw [List.range'_append_1]; congr 1; omega
  have e2 : List.range' 0 a ++ List.range' (0 + a) (n - a) = List.range' 0 (a + (n - a)) :=
    List.range'_append_1
  have e : List.range' 0 n =
      List.range' 0 a ++ (List.range' a k ++ List.range' (a + k) (n - (a + k))) := by
    rw [e1]; rw [Nat.zero_add] at e2; rw [e2]; congr 1; omega
  have hA : ((List.range' 0 a).flatMap g).length = 4096 * a :=
    flatMap_range'_length g 4096 0 a (fun s _ h2 => hg s (by omega))
  have hB : ((List.range' a k).flatMap g).length = 4096 * k :=
    flatMap_range'_length g 4096 a k (fun s _ h2 => hg s (by omega))
  unfold bytesAt
  rw [e, List.flatMap_append, List.flatMap_append, List.drop_left' hA, List.take_left' hB]

/-- `flatMap` over a list, by its members. -/
theorem flatMap_congr_mem_ci {l : List Nat} {f g : Nat → List w8} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A page's header is its first slot's. -/
theorem pageHdr_append (a b : List w8) (h : 16 ≤ a.length) : pageHdr (a ++ b) = pageHdr a := by
  unfold pageHdr bytesAt
  simp only [List.drop_zero]
  rw [List.take_append_of_le_length h]

theorem ofList_map_lookup_mem' {V : Type} (f : Nat → V) :
    ∀ (l : List Nat) (id : Nat), id ∈ l →
      (GMap.ofList (l.map fun i => (i, f i))) !! id = some (f id)
  | [], id, h => by cases h
  | a :: l, id, h => by
    simp only [List.map_cons, GMap.ofList]
    by_cases ha : a = id
    · subst ha; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ ha]
      exact ofList_map_lookup_mem' f l id (by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ha
        · exact h)

private theorem mem_pendSlots_iff' (fl : FLPg) (s : Nat) :
    s ∈ pendSlots fl ↔ ∃ t pd x, fl.pending !! t = some pd ∧ x ∈ pd.ids ∧ x.toNat = s := by
  simp only [pendSlots, FLPg.pendingIds, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨⟨t, pd⟩, hkv, hx⟩, rfl⟩
    exact ⟨t, pd, x, (GMap.mem_toList _ _ _).1 hkv, hx, rfl⟩
  · rintro ⟨t, pd, x, hp, hx, rfl⟩
    exact ⟨x, ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩, rfl⟩

/-- **The closed file is an image of its committed state** (see the file header): `n` slots of
`4096` bytes, the high-water mark inside, every slot of the tree a store slot (`slotsOf`), the
store's pages its bytes, the synced freelist page the writer side's `W` slots' and reloadable
(`flCurOK`), the idle store's tree slots not pending and its pending slots below the mark. -/
theorem closeBytes_fileOK (C : CommitSt) (fl : FLPg) (bs wb : Nat → List w8) (n : Nat)
    (hmeta : C.metaOk) (htree : treeOK C) (htx1 : 1 ≤ C.txid) (htx2 : C.txid < 2 ^ 62)
    (hn : C.hwm ≤ n) (hpb : pagesFromBytes bs C.pages)
    (hbs : ∀ s ∈ slotsOf C fl, 2 ≤ s ∧ (bs s).length = 4096)
    (hwb : ∀ s, 2 ≤ s → s < n → s ∉ slotsOf C fl → (wb s).length = 4096)
    (hnp : ∀ s ∈ treeSlots C, s ∉ pendSlots fl)
    (hpend : ∀ s ∈ pendSlots fl, s < C.hwm)
    (hfl : ∀ f, C.flpg = some f → flCurOK fl C (extentBytes wb f)) :
    fileOK (closeBytes C fl bs wb n) (4096 * n) (treeData C) ∧
      (closeBytes C fl bs wb n).length = 4096 * n ∧ fileImage (closeBytes C fl bs wb n) C := by
  have hm0 := hmeta.1
  have hm1 := hmeta.2.1
  have hslot : ∀ s, s < n → (closeSlot C fl bs wb s).length = 4096 := by
    intro s hs
    unfold closeSlot
    by_cases h0 : s = 0
    · rw [if_pos h0]; exact hm0
    rw [if_neg h0]
    by_cases h1 : s = 1
    · rw [if_pos h1]; exact hm1
    rw [if_neg h1]
    by_cases h2 : s ∈ slotsOf C fl
    · rw [if_pos h2]; exact (hbs s h2).2
    · rw [if_neg h2]; exact hwb s (by omega) hs h2
  have hlen : (closeBytes C fl bs wb n).length = 4096 * n := by
    unfold closeBytes
    rw [flatMap_range'_length _ 4096 0 n (fun s _ h => hslot s (by omega)), Nat.mul_comm]
  have hchunk : ∀ a k, a + k ≤ n →
      bytesAt (closeBytes C fl bs wb n) (4096 * a) (4096 * k) =
        (List.range' a k).flatMap (closeSlot C fl bs wb) := fun a k hak =>
    chunks_bytesAt _ n a k hslot hak
  have htree0 := htree
  obtain ⟨⟨hwf, -⟩, htp, -, hext, -, -⟩ := htree
  have hroot2 : 2 ≤ C.root ∧ C.root < C.hwm := by
    cases hwf with
    | page _ _ h2 hlt _ _ _ _ => exact ⟨h2, hlt⟩
  have h2n : 2 ≤ n := by omega
  -- a tree slot is a store slot
  have htreeS : ∀ id pg, C.pages !! id = some pg → ∀ s, id ≤ s → s < id + (1 + pageOverflow pg) →
      s ∈ slotsOf C fl := by
    intro id pg hpg s h1 h2
    unfold slotsOf
    rw [Perennial.mem_list_dedup, List.mem_append]
    left
    unfold treeSlots
    exact (mem_pagesSlots_iff _ _).2 ⟨id, pg, hpg, h1, h2⟩
  -- the file's pages hold the tree's
  have hpage : ∀ id pg, C.pages !! id = some pg → filePage (closeBytes C fl bs wb n) id = pg := by
    intro id pg hpg
    have hid := hext id pg hpg
    have hrun : ∀ s ∈ List.range' id (1 + pageOverflow pg), closeSlot C fl bs wb s = bs s := by
      intro s hs
      rw [List.mem_range'_1] at hs
      have hS := htreeS id pg hpg s hs.1 hs.2
      have h2 := (hbs s hS).1
      unfold closeSlot
      rw [if_neg (by omega), if_neg (by omega), if_pos hS]
    have hpg' := hpb id pg hpg
    have hfirst : bytesAt (closeBytes C fl bs wb n) (4096 * id) 4096 = bs id := by
      have := hchunk id 1 (by omega)
      rw [Nat.mul_one] at this
      rw [this, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hrun id (List.mem_range'_1.2 ⟨Nat.le_refl _, by omega⟩)
    have hov : pageOverflow (bs id) = pageOverflow pg := by
      have hl : 16 ≤ (bs id).length := by
        have := (hbs id (htreeS id pg hpg id (Nat.le_refl _) (by omega))).2; omega
      conv => rhs; rw [hpg']
      rw [show 1 + pageOverflow pg = (1 + pageOverflow pg - 1) + 1 by omega,
        List.range'_succ, List.flatMap_cons]
      unfold pageOverflow
      rw [pageHdr_append _ _ hl]
    unfold filePage
    rw [hfirst, hov, show (1 + pageOverflow pg) * 4096 = 4096 * (1 + pageOverflow pg) by omega,
      hchunk id (1 + pageOverflow pg) (by omega), flatMap_congr_mem_ci hrun, ← hpg']
  have hle : pagesLe C.pages (filePages (closeBytes C fl bs wb n) C.hwm) := by
    intro id pg hpg
    have hid := hext id pg hpg
    unfold filePages
    rw [ofList_map_lookup_mem' (filePage _) _ id (List.mem_range.2 (by omega)), hpage id pg hpg]
  have htp' : treePages (filePages (closeBytes C fl bs wb n) C.hwm) C.root = C.pages := by
    apply GMap.ext
    intro id
    show treePages _ C.root !! id = C.pages !! id
    rw [treePages_lookup]
    by_cases h : treeHas (filePages (closeBytes C fl bs wb n) C.hwm) C.root id
    · rw [if_pos h]
      have h' := treeHas_of_le hle C.hwm h hwf
      obtain ⟨pg, hpg⟩ := treeHas_page_ci h'
      rw [hpg]; exact hle id pg hpg
    · rw [if_neg h]
      rcases hc : C.pages !! id with _ | pg
      · rfl
      · exfalso; apply h
        have h1 : treePages C.pages C.root !! id = some pg := by rw [htp]; exact hc
        rw [treePages_lookup] at h1
        split at h1
        · rename_i ht; exact treeHas_le hle ht
        · cases h1
  -- the synced freelist page: the writer side's slots
  have hflF : flFileOK (closeBytes C fl bs wb n) C := by
    intro f hf
    obtain ⟨hf2, hfh, -, hflag, hcnt, hnd, hx2, hxout, hsl, -, -, hxs, -, hid⟩ := hfl f hf f hf
    have hnotS : ∀ s, f ≤ s → s < f + (1 + pageOverflow (extentBytes wb f)) → s ∉ slotsOf C fl := by
      intro s h1 h2 hS
      obtain ⟨hcov, hall⟩ := hsl s h1 h2
      unfold slotsOf at hS
      rw [Perennial.mem_list_dedup, List.mem_append] at hS
      rcases hS with hS | hS
      · unfold treeSlots at hS; exact hcov ((mem_pagesSlots_iff _ _).1 hS)
      · obtain ⟨t, pd, x, hp, hx, rfl⟩ := (mem_pendSlots_iff' _ _).1 hS
        apply hall
        have hxe : W64 ((x.toNat : Nat) : Int) = x := by
          apply BitVec.eq_of_toNat_eq; rw [toNat_W64_of_lt _ x.isLt]
        rw [hxe]
        simp only [FLPg.allIds, FLPg.pendingIds, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(t, pd), (GMap.mem_toList _ _ _).2 hp, hx⟩
    have hW : ∀ s, f ≤ s → s < f + (1 + pageOverflow (extentBytes wb f)) →
        closeSlot C fl bs wb s = wb s := by
      intro s h1 h2
      unfold closeSlot
      rw [if_neg (by omega), if_neg (by omega), if_neg (hnotS s h1 h2)]
    have hwf16 : 16 ≤ (wb f).length := by
      have := hwb f hf2 (by omega) (hnotS f (Nat.le_refl _) (by omega)); omega
    have hovE : pageOverflow (extentBytes wb f) = pageOverflow (wb f) := by
      unfold extentBytes
      rw [show 1 + pageOverflow (wb f) = pageOverflow (wb f) + 1 by omega, List.range'_succ,
        List.flatMap_cons]
      unfold pageOverflow
      rw [pageHdr_append _ _ hwf16]
    have hfirst : bytesAt (closeBytes C fl bs wb n) (4096 * f) 4096 = wb f := by
      have := hchunk f 1 (by omega)
      rw [Nat.mul_one] at this
      rw [this, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hW f (Nat.le_refl _) (by omega)
    have hfp : filePage (closeBytes C fl bs wb n) f = extentBytes wb f := by
      unfold filePage
      rw [hfirst, ← hovE,
        show (1 + pageOverflow (extentBytes wb f)) * 4096 = 4096 * (1 + pageOverflow (extentBytes wb f))
          by omega, hchunk f _ (by omega)]
      have e2 : extentBytes wb f =
          (List.range' f (1 + pageOverflow (extentBytes wb f))).flatMap wb := by
        conv => lhs; unfold extentBytes
        rw [hovE]
      conv => rhs; rw [e2]
      apply flatMap_congr_mem_ci
      intro s hs
      rw [List.mem_range'_1] at hs
      exact hW s hs.1 hs.2
    have hcp : ∀ x, committedPending fl C x → x.toNat ∈ pendSlots fl := by
      rintro x ⟨t, pd, hp, hx, -⟩
      exact (mem_pendSlots_iff' _ _).2 ⟨t, pd, x, hp, hx, rfl⟩
    simp only
    rw [hfp]
    refine ⟨hf2, hfh, hflag, hcnt, hnd, fun x hx => ⟨hx2 x hx, ?_⟩, fun x hx => ⟨hxout x hx, ?_⟩,
      fun s h1 h2 => (hsl s h1 h2).1, hid⟩
    · rcases hxs x hx with h | h
      · exact hpend _ (hcp x h)
      · exact h.1
    · rcases hxs x hx with h | h
      · intro hcov
        exact hnp _ (by unfold treeSlots; exact (mem_pagesSlots_iff _ _).2 hcov) (hcp x h)
      · exact h.2.2
  have hm0' : bytesAt (closeBytes C fl bs wb n) 0 4096 = C.m0 := by
    have := hchunk 0 1 (by omega)
    simp only [Nat.mul_zero, Nat.mul_one] at this
    rw [this, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold closeSlot; simp
  have hm1' : bytesAt (closeBytes C fl bs wb n) 4096 4096 = C.m1 := by
    have := hchunk 1 1 (by omega)
    simp only [Nat.mul_one] at this
    rw [this, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold closeSlot; simp
  refine ⟨Or.inr ⟨C, ⟨hm0'.symm, hm1'.symm, htp'.symm⟩, hmeta, htree0, hflF, by omega, htx1, htx2,
    rfl⟩, hlen, ⟨hm0'.symm, hm1'.symm, htp'.symm⟩⟩

end img

end bbolt
end EtcdGrove
end Perennial
