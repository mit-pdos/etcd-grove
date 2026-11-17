/-
**A read transaction's buckets are small** (S1a of `notes/bbolt-integration-plan.md`, D-I3): the
`…Def` law of `Api.lean`'s `boltTx_size`. Every entry of a bucket of a reader's view is an element
of a leaf page (or of its inline page): at most `2 ^ 16` per page (the header's `count` is a
`uint16`), and the leaves a bucket's walk reaches are distinct pages of the view (`viewUnique`), each
inside the mapping (`rtxFrac`: `(id + 1) · 4096 ≤ l`, `mapFields`: `l ≤ maxMapSize < 2 ^ 48`), so
fewer than `2 ^ 36` of them: a bucket has at most `2 ^ 52` entries.

The pure half (`View.data_bkt_size`) is over a well-formed view whose page ids are below `2 ^ 36`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Proof.go_etcd_io.bbolt.Inv.MatReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace TxSize

section pure
variable [GooseExts]

/-- The page ids of `leavesF`'s leaves (the same walk, recording the ids). -/
def leafIdsF : Nat → Pages → Nat → List Nat
  | 0, _, _ => []
  | n + 1, P, id =>
    match P !! id with
    | none => []
    | some pg =>
      if pageFlags pg = leafPageFlag then [id]
      else (List.range (pageCount pg)).flatMap fun i => leafIdsF n P (branchPgid pg i)

theorem leavesF_eq_map (P : Pages) :
    ∀ n id, leavesF n P id = (leafIdsF n P id).map fun j => (P !! j).getD []
  | 0, _ => by simp [leavesF, leafIdsF]
  | n + 1, id => by
    simp only [leavesF, leafIdsF]
    cases hp : P !! id with
    | none => simp
    | some pg =>
      simp only
      split
      · simp [hp]
      · rw [List.map_flatMap]
        exact congrArg (fun g => List.flatMap g (List.range (pageCount pg)))
          (funext fun i => leavesF_eq_map P n (branchPgid pg i))

theorem leafIdsF_has (P : Pages)
    (hk : ∀ id pg, P !! id = some pg → pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) :
    ∀ n id j, j ∈ leafIdsF n P id → treeHas P id j ∧ (P !! j).isSome
  | 0, _, _, h => by simp [leafIdsF] at h
  | n + 1, id, j, h => by
    simp only [leafIdsF] at h
    cases hp : P !! id with
    | none => rw [hp] at h; simp at h
    | some pg =>
      rw [hp] at h
      simp only at h
      by_cases hl : pageFlags pg = leafPageFlag
      · rw [if_pos hl, List.mem_singleton] at h
        subst h
        exact ⟨treeHas.root _ _ hp, by simp [hp]⟩
      · rw [if_neg hl] at h
        obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 h
        rw [List.mem_range] at hi
        obtain ⟨ht, hs⟩ := leafIdsF_has P hk n _ j hm
        have hb : pageFlags pg = branchPageFlag := by
          rcases hk id pg hp with e | e
          · exact absurd e hl
          · exact e
        exact ⟨treeHas.sub id pg j hp (pageHas.child pg i j hb hi ht), hs⟩

/-- A flat map of duplicate-free lists, pairwise disjoint over a duplicate-free list. -/
theorem nodup_flatMap_of {α β : Type} (f : α → List β) :
    ∀ l : List α, l.Nodup → (∀ x ∈ l, (f x).Nodup) →
      (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ d, d ∈ f x → d ∉ f y) → (l.flatMap f).Nodup
  | [], _, _, _ => by simp
  | x :: l, hl, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.nodup_cons] at hl
    refine ⟨h1 x List.mem_cons_self,
      nodup_flatMap_of f l hl.2 (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
        (fun a ha b hb => h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)), ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨y, hy, hby⟩ := List.mem_flatMap.1 hb
    have hxy : x ≠ y := fun e => hl.1 (e ▸ hy)
    exact h2 x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hxy a ha hby

theorem leafIdsF_nodup (P : Pages)
    (hk : ∀ id pg, P !! id = some pg → pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag)
    (hu : viewUnique P) : ∀ n id, (leafIdsF n P id).Nodup
  | 0, _ => by simp [leafIdsF]
  | n + 1, id => by
    simp only [leafIdsF]
    cases hp : P !! id with
    | none => simp
    | some pg =>
      simp only
      by_cases hl : pageFlags pg = leafPageFlag
      · rw [if_pos hl]; simp
      · rw [if_neg hl]
        have hb : pageFlags pg = branchPageFlag := by
          rcases hk id pg hp with e | e
          · exact absurd e hl
          · exact e
        apply nodup_flatMap_of _ _ List.nodup_range (fun i _ => leafIdsF_nodup P hk hu n _)
        intro i hi j hj hij
        rw [List.mem_range] at hi hj
        intro d hd1 hd2
        exact (hu.1 id pg hp hb).1 i j hi hj hij d (leafIdsF_has P hk n _ d hd1).1
          (leafIdsF_has P hk n _ d hd2).1

/-- A duplicate-free list of keys of a map is no longer than the map. -/
theorem length_le_size {V : Type} (P : GMap Nat V) (l : List Nat) (hn : l.Nodup)
    (hs : ∀ j ∈ l, (P !! j).isSome) : l.length ≤ P.size := by
  rw [GMap.size_eq_dom_list_length]
  apply List.Subperm.length_le
  apply List.subperm_of_subset hn
  intro j hj
  exact (GMap.mem_dom_list P j).2 (hs j hj)

/-- A map whose keys are below `N` has at most `N` bindings. -/
theorem size_le_of_bound {V : Type} (P : GMap Nat V) (N : Nat)
    (hb : ∀ j v, P !! j = some v → j < N) : P.size ≤ N := by
  rw [GMap.size_eq_dom_list_length]
  have : P.domList.length ≤ (List.range N).length := by
    apply List.Subperm.length_le
    apply List.subperm_of_subset (GMap.nodup_dom_list P)
    intro j hj
    have h := (GMap.mem_dom_list P j).1 hj
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    exact List.mem_range.2 (hb j v hv)
  simpa using this

theorem ofList_size_le {K V : Type} [DecidableEq K] :
    ∀ l : List (K × V), (GMap.ofList l).size ≤ l.length
  | [] => by
    show (∅ : GMap K V).size ≤ 0
    rw [GMap.map_size_empty]; exact Nat.le_refl 0
  | (k, v) :: l => by
    have ih := ofList_size_le l
    show (GMap.insert k v (GMap.ofList l)).size ≤ l.length + 1
    have := GMap.map_size_insert (GMap.ofList l) k v
    simp only [GMap.insert] at this ⊢
    split at this <;> omega

theorem ofList_lookup_mem {K V : Type} [DecidableEq K] :
    ∀ (l : List (K × V)) (k : K) (v : V), (GMap.ofList l).lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [GMap.ofList, GMap.empty] at h
  | (k', v') :: l, k, v, h => by
    simp only [GMap.ofList, GMap.insert] at h
    by_cases e : k' = k
    · rw [if_pos e] at h
      cases h; subst e; exact List.mem_cons_self
    · rw [if_neg e] at h
      exact List.mem_cons_of_mem _ (ofList_lookup_mem l k v h)

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (c : Nat)
    (h : ∀ x ∈ l, (f x).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem leafEnts_length (pg : List w8) : (leafEnts pg).length < 2 ^ 16 := by
  unfold leafEnts pageCount
  simp only [List.length_map, List.length_range]
  exact (pageHdr pg).count'.isLt

/-- **A bucket of a well-formed view with page ids below `2 ^ 36` has at most `2 ^ 52`
entries.** -/
theorem View.data_bkt_size (v : View) (hv : viewWF v)
    (hb : ∀ id pg, v.pages !! id = some pg → id < 2 ^ 36) :
    ∀ (n : GoString) (m : BktData), v.data.lookup n = some m → m.size < 2 ^ 61 := by
  intro n m hm
  unfold View.data at hm
  have hmem := ofList_lookup_mem _ _ _ hm
  obtain ⟨e, -, he⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  have hsz := ofList_size_le (bktEntries v.pages e.2)
  have hk : ∀ id pg, v.pages !! id = some pg →
      pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag :=
    fun id pg hp => (viewWF_page_ready v hv id pg hp).2.2.1
  have hu : viewUnique v.pages := by
    obtain ⟨C, hok, hvC⟩ := hv
    have hpv : v.pages = C.pages := by rw [← hvC]; rfl
    rw [hpv]; exact hok.1.2.1.2
  have hP : v.pages.size ≤ 2 ^ 36 := size_le_of_bound v.pages _ hb
  have hleaves : (bktLeaves v.pages e.2).length ≤ 2 ^ 36 := by
    unfold bktLeaves
    split
    · simp
    · unfold treeLeaves
      rw [leavesF_eq_map, List.length_map]
      have := length_le_size v.pages _
        (leafIdsF_nodup v.pages hk hu (v.pages.size + 1) (inBucketRoot e.2))
        (fun j hj => (leafIdsF_has v.pages hk _ _ j hj).2)
      omega
  have hents : (bktEntries v.pages e.2).length ≤ 2 ^ 36 * 2 ^ 16 := by
    unfold bktEntries
    have := length_flatMap_le (bktLeaves v.pages e.2) leafEnts (2 ^ 16)
      (fun x _ => Nat.le_of_lt (leafEnts_length x))
    exact Nat.le_trans this (Nat.mul_le_mul_right _ hleaves)
  unfold bktOfPage
  omega

end pure

end TxSize

section tx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Iris.ProofMode in
/-- **`boltTx_size`'s definition-level law**: every bucket of a read transaction's snapshot has
fewer than `2 ^ 61` entries (`TxSize.View.data_bkt_size`, with the view's pages inside its
mapping). -/
theorem boltTxDef_size_ro (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (D : Data) :
    boltTxDef (GF := GF) B N tx q (TxView.ro D) ⊢
      ⌜∀ (n : GoString) (m : BktData), D.lookup n = some m → m.size < 2 ^ 61⌝ := by
  unfold boltTxDef
  rw [ite_eq_right_iff.mpr (by simp [TxView.ro])]
  unfold rdTx rtxFrac
  iintro ⟨%db', ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, -, -, -, -, -,
    ⟨%t, -, -, -, -, -, -, -, -, -, -, -, ⟨%l, -, Hmf, %Hl⟩, -, %Hf⟩, -⟩, -⟩
  unfold mapFields
  icases Hmf with ⟨-, -, -, -, %Hlen⟩
  ipureintro
  have hT : TxView.ro D = TxView.ro v.data := Hf.1
  have hD : D = v.data := by
    have := congrArg TxView.cur hT; simpa [TxView.ro] using this
  rw [hD]
  apply TxSize.View.data_bkt_size v Hf.2.1
  intro id pg hp
  have := Hl id pg hp
  have := Hlen.1
  omega

end tx

end bbolt
end EtcdGrove
end Perennial
