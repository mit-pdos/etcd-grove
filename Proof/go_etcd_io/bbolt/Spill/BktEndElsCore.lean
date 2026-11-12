/-
`Bucket.spill`'s root loop's end (U9x10, `notes/bbolt-proof-plan.md`): **`endEls` from facts per
element** (`endEls_of`), pure. A tree `P'` written with the root's elements `E` (an `sTree`) reads,
at each bucket element, the value's tree: when the value is a `bvalS` over a page map `Q` that
`P'` agrees with on its pages, holding the entries `L` plain (`bvalData`), `P'`'s tree pages read
the same entries (`val_end`: the nested pages are the tree's, `treeEls_bucketHas`). With each
element a bucket entry within the bounds, its name the writer's, its data the writer's
(`elVal`), this gives `endEls`'s three clauses (`rootShape_of_els` for the shape).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndShape
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureSpilled
public import Proof.go_etcd_io.bbolt.Spill.STreeAgree
public import Proof.go_etcd_io.bbolt.Spill.BktValKey
public import Proof.go_etcd_io.bbolt.Spill.BktEndPost
public import Proof.go_etcd_io.bbolt.Spill.BktEndPieces

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section core
variable [GooseExts]

/-- An element of a written tree is an entry of one of its own leaf pages. -/
theorem treeEls_src {P : Pages} {hwm root : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm root lo hi h S) {e : El} (he : e ∈ treeEls P root) :
    ∃ id pg i, ownHas P root id ∧ P !! id = some pg ∧ pageFlags pg = leafPageFlag ∧
      i < pageCount pg ∧ e = (leafFlags pg i, leafKey pg i, leafValue pg i) := by
  unfold treeEls at he
  obtain ⟨pg, hpg, hm⟩ := List.mem_flatMap.1 he
  obtain ⟨i, hix, rfl⟩ := List.mem_map.1 hm
  obtain ⟨id, -, -, hown, hp, hfl, -, -⟩ := leavesF_page P hwm _ root lo hi hs.wf hs.keys pg hpg
  exact ⟨id, pg, i, hown, hp, hfl, List.mem_range.1 hix, rfl⟩

/-- `treeEls_src` with the leaf's membership and its entry's key and value lengths. -/
theorem treeEls_srcWF {P : Pages} {hwm root : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm root lo hi h S) {e : El} (he : e ∈ treeEls P root) :
    ∃ id pg i, pg ∈ treeLeaves P root ∧ ownHas P root id ∧ P !! id = some pg ∧
      pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
      e = (leafFlags pg i, leafKey pg i, leafValue pg i) ∧
      (leafKey pg i).length = leafKsize pg i ∧ (leafValue pg i).length = leafVsize pg i := by
  unfold treeEls at he
  obtain ⟨pg, hpg, hm⟩ := List.mem_flatMap.1 he
  obtain ⟨i, hix, rfl⟩ := List.mem_map.1 hm
  rw [List.mem_range] at hix
  obtain ⟨id, -, -, hown, hp, hfl, hpt, -⟩ := leavesF_page P hwm _ root lo hi hs.wf hs.keys pg hpg
  refine ⟨id, pg, i, hpg, hown, hp, hfl, hix, rfl, ?_⟩
  cases hpt with
  | branch _ _ hb _ _ => rw [hfl] at hb; cases hb
  | leaf _ _ _ hwf _ =>
    have hb := (hwf.2.2.1 i hix).1
    constructor
    · unfold leafKey bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega
    · unfold leafValue bytesAt; simp only [List.length_take, List.length_drop]; have := hwf.1; omega

/-- A page of a `bvalS` is a page of the map. -/
theorem bvalS_page {P : Pages} {hwm : Nat} {v : List w8} {S : List Nat} (hb : bvalS P hwm v S)
    {x : Nat} (hx : x ∈ S) : ∃ pg, P !! x = some pg := by
  rcases hb.2 with ⟨-, rfl, -⟩ | ⟨-, h, hs⟩
  · cases hx
  · exact Option.isSome_iff_exists.1 (sTree_isSome hs x hx)

/-- The keys of a list of bucket entries, through `rootEnts`' filter. -/
theorem filterMap_bkt_keys : ∀ (ws : List WEntry), (∀ w ∈ ws, isBktFlag w.flags) →
    (ws.filterMap fun w => if decide (isBktFlag w.flags) then some (w.key, w.value) else none).map
      Prod.fst = ws.map WEntry.key
  | [], _ => rfl
  | a :: t, h => by
    have ha : isBktFlag a.flags := h a (by simp)
    have ih := filterMap_bkt_keys t (fun w hw => h w (by simp [hw]))
    simp only [List.filterMap_cons, ha, decide_true, ↓reduceIte, List.map_cons, ih]

/-- A bucket element's nested pages are pages of the tree. -/
theorem treeEls_bucketHas {P : Pages} {hwm root : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm root lo hi h S) {e : El} (he : e ∈ treeEls P root)
    (hb : e.1 % 2 = bucketLeafFlag) : ∀ d, bucketHas P e.2.2 d → treeHas P root d := by
  obtain ⟨id, pg, i, hown, hp, hfl, hi, rfl⟩ := treeEls_src hs he
  intro d hd
  exact treeHas_trans (treeHas_of_ownHas hown) (treeHas_bucket hp hfl hi hb hd)

/-- **A bucket element's value read in the written tree's pages** (see the module doc). -/
theorem val_end {P' Q : Pages} {hwm root hwmv h : Nat} {S Sv : List Nat} {e : El}
    {L : List BoltEnt} (hs : sTree P' hwm root none none h S) (he : e ∈ treeEls P' root)
    (hb : e.1 % 2 = bucketLeafFlag) (hv : bvalS Q hwmv e.2.2 Sv)
    (hag : ∀ x ∈ Sv, P' !! x = Q !! x) (hd : bvalData Q e.2.2 L) :
    bktOfPage (treePages P' root) e.2.2 = GMap.ofList L ∧
    ∀ bpg, bktLeafPg (treePages P' root) e.2.2 bpg → ∀ j < pageCount bpg,
      leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
        leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax := by
  have hd' := bvalData_agree hv hag hd
  have htr := treeEls_bucketHas hs he hb
  rcases hv.2 with ⟨hr0, -, -⟩ | ⟨hr0, hv', hsv⟩
  · obtain ⟨d1, d2⟩ := hd'.1 hr0
    refine ⟨?_, ?_⟩
    · unfold bktOfPage bktEntries bktLeaves
      rw [if_pos hr0, List.flatMap_singleton, d1]
    · intro bpg hbpg
      rcases hbpg with ⟨-, rfl⟩ | ⟨hne, -⟩
      · exact d2
      · exact absurd hr0 hne
  · obtain ⟨d1, d2⟩ := hd'.2 hr0
    have hsv' := sTree_agree hag (Nat.le_refl _) hsv
    have hagT : ∀ x ∈ Sv, treePages P' root !! x = P' !! x := fun x hx =>
      treePages_agree P' root x (htr x (bucketHas.file _ x hr0 ((hsv'.has x).2 hx)))
    have hL : treeLeaves (treePages P' root) (inBucketRoot e.2.2) =
        treeLeaves P' (inBucketRoot e.2.2) := treeLeaves_sTree_agree hsv' hagT
    refine ⟨?_, ?_⟩
    · unfold bktOfPage bktEntries bktLeaves
      rw [if_neg hr0, hL]
      unfold treeEntries at d1; rw [d1]
    · intro bpg hbpg
      rcases hbpg with ⟨h0, -⟩ | ⟨-, id, hown, hpg, hfl⟩
      · exact absurd h0 hr0
      · have hm := ownLeaf_mem_treeLeaves hsv' (ownHas_le (treePages_le P' root) hown)
          (treePages_le P' root _ _ hpg) hfl
        exact d2 bpg hm

/-- **What an element of the root at the end needs** for `endEls`: its value a `bvalS` over `Q`
on owned pages, holding the entries `L` plain, the writer's data of its name at the start. -/
def elVal (X0 : WX) (Q : Pages) (D : List Nat) (e : El) : Prop :=
  ∃ hwmv Sv L, bvalS Q hwmv e.2.2 Sv ∧ (∀ x ∈ Sv, x ∈ D) ∧ bvalData Q e.2.2 L ∧
    bktData X0 e.2.1 = some (GMap.ofList L)

/-- **`endEls` from facts per element** (see the module doc). -/
theorem endEls_of {X0 : WX} {Q : Pages} {D : List Nat} {E : List El}
    (hel : ∀ e ∈ E, e.1 % 2 = bucketLeafFlag ∧ (0 < e.2.1.length ∧ e.2.1.length ≤ maxKeySize) ∧
      e.2.1.length + e.2.2.length ≤ bboltEntryMax)
    (hval : ∀ e ∈ E, elVal X0 Q D e)
    (hnames : E.map (fun e => e.2.1) = (rootEnts X0).map Prod.fst) :
    endEls X0 Q D E := by
  intro P' root hwm h S hs hE hag
  have hTP : treeEntries (treePages P' root) root = E.map (fun e => (e.2.1, e.2.2)) := by
    unfold treeEntries
    rw [treeLeaves_sTree_agree hs (fun x hx => treePages_agree P' root x ((hs.has x).2 hx))]
    rw [← hE, treeEls_entries]; rfl
  have hv : ∀ e ∈ E, bktOfPage (treePages P' root) e.2.2 = (bktData X0 e.2.1).getD ∅ ∧
      ∀ bpg, bktLeafPg (treePages P' root) e.2.2 bpg → ∀ j < pageCount bpg,
        leafFlags bpg j % 2 = 0 ∧ 0 < leafKsize bpg j ∧
          leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax := by
    intro e he
    obtain ⟨hwmv, Sv, L, hSv, hSD, hd, hbd⟩ := hval e he
    have := val_end hs (hE ▸ he) (hel e he).1 hSv (fun x hx => hag x (hSD x hx)) hd
    rw [hbd]; exact this
  refine ⟨rootShape_of_els hs hE hel fun e he => (hv e he).2, ?_, ?_⟩
  · rw [hTP, List.map_map]; exact hnames
  · intro n v hm
    rw [hTP] at hm
    obtain ⟨e, he, hev⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨hwmv, Sv, L, -, -, -, hbd⟩ := hval e he
    rw [(hv e he).1, hbd]; rfl

end core

end Spill

end bbolt
end EtcdGrove
end Perennial
