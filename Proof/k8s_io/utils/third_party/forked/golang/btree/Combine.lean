/-
Combining readers' fractions of a tree: `ownBTree t dq1 s ∗ ownBTree t dq2 s` is
`ownBTree t (dq1 • dq2) s` (the converse of `ownBTree_split`), when the order's keys are
determined by the items (`o.item v k1 ∗ o.item v k2 ⊢ ⌜k1 = k2⌝`): the two fractions describe
the same memory, so their trees agree node by node (`ownNode_combine`), the keys through
`allItems`.

With it, `fun q => ownBTree t (DFrac.own q) s` is `Fractional`: a tree can be the resource of
a `sync.RWMutex` (`etcd`'s key index, `mvcc/InvIndex.lean`).
-/

module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Fractional

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

/-! ### Pure: a node's items and its children's elements are elements -/

theorem Tree.mem_elemsAux_of_mem_items {E : Type} :
    ∀ (is : List E) (cs : List (Tree E)) {e : E}, e ∈ is → e ∈ Tree.elemsAux is cs
  | is, [], e, h => by simpa using h
  | [], _ :: _, _, h => by simp at h
  | i :: is, c :: cs, e, h => by
    rw [Tree.elemsAux_cons_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _
        (List.mem_cons_of_mem _ (Tree.mem_elemsAux_of_mem_items is cs h))

theorem Tree.mem_elemsAux_of_mem_child {E : Type} :
    ∀ (is : List E) (cs : List (Tree E)) {c : Tree E}, c ∈ cs → ∀ {e : E}, e ∈ c.elems →
      e ∈ Tree.elemsAux is cs
  | _, [], _, hc, _, _ => by simp at hc
  | [], c' :: cs, c, hc, e, h => by
    rw [Tree.elemsAux_nil_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (Tree.mem_elemsAux_of_mem_child [] cs hc h)
  | i :: is, c' :: cs, c, hc, e, h => by
    rw [Tree.elemsAux_cons_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _
        (List.mem_cons_of_mem _ (Tree.mem_elemsAux_of_mem_child is cs hc h))

theorem Tree.items_subset_elems {E : Type} (is : List E) (cs : List (Tree E)) :
    ∀ e ∈ is, e ∈ (Tree.node is cs).elems := fun _ h =>
  Tree.elems_node is cs ▸ Tree.mem_elemsAux_of_mem_items is cs h

theorem Tree.child_elems_subset_elems {E : Type} (is : List E) (cs : List (Tree E)) {c : Tree E}
    (hc : c ∈ cs) : ∀ e ∈ c.elems, e ∈ (Tree.node is cs).elems := fun _ h =>
  Tree.elems_node is cs ▸ Tree.mem_elemsAux_of_mem_child is cs hc h

section combine
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

theorem tp_combine {A : Type} [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac) (l : Loc) (v : A) :
    typedPointsto (GF := GF) l v dq1 ∗ typedPointsto l v dq2 ⊢ typedPointsto l v (dq1 • dq2) :=
  (dfractional (Φ := fun dq => typedPointsto (GF := GF) l v dq) dq1 dq2).2

theorem slice_combine {A : Type} [ZeroVal A] [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac)
    (sl : GoSlice) (vs : List A) :
    (sl ↦*{dq1} vs ∗ sl ↦*{dq2} vs : IProp GF) ⊢ sl ↦*{dq1 • dq2} vs :=
  (dfractional (Φ := fun dq => (sl ↦*{dq} vs : IProp GF)) dq1 dq2).2

theorem cap_combine (A : Type) [ZeroVal A] [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac)
    (sl : GoSlice) :
    ownSliceCap (GF := GF) A sl dq1 ∗ ownSliceCap A sl dq2 ⊢ ownSliceCap A sl (dq1 • dq2) :=
  (dfractional (Φ := fun dq => ownSliceCap (GF := GF) A sl dq) dq1 dq2).2

/-- The keys of the order are determined by the items. -/
def KeysOfItems (o : ItemOrder GF V K) : Prop :=
  ∀ (v : V) (k1 k2 : K), ⊢ o.item v k1 -∗ o.item v k2 -∗ (⌜k1 = k2⌝ : IProp GF)

theorem allItems_elem' {l : List (V × K)} {e : V × K} (h : e ∈ l) :
    allItems o l ⊢ o.item e.1 e.2 := by
  unfold allItems
  iintro #H
  iapply H
  ipureintro; exact h

/-- Item lists with the same Go items, whose keys `allItems o S` determines, are equal. -/
theorem items_agree (hkey : KeysOfItems o) (S : List (V × K)) :
    ∀ (is1 is2 : List (V × K)), is1.map Prod.fst = is2.map Prod.fst →
      (∀ e ∈ is1, e ∈ S) → (∀ e ∈ is2, e ∈ S) → allItems o S ⊢ (⌜is1 = is2⌝ : IProp GF)
  | [], [], _, _, _ => by iintro _; ipureintro; rfl
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | (v, k) :: t1, (v', k') :: t2, h, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    iintro #H
    ihave #Hk := allItems_elem' o (h1 _ List.mem_cons_self) $$ H
    ihave #Hk' := allItems_elem' o (h2 _ List.mem_cons_self) $$ H
    ihave %hkk := hkey v k k' $$ Hk Hk'
    ihave %ht := items_agree hkey S t1 t2 h (fun e he => h1 e (List.mem_cons_of_mem _ he))
      (fun e he => h2 e (List.mem_cons_of_mem _ he)) $$ H
    ipureintro
    rw [hkk, ht]

theorem nodeFields_combine (dq1 dq2 : DFrac) (n : Loc) (is1 cs1 is2 cs2 : GoSlice)
    (cow1 cow2 : Loc) :
    ⊢ nodeFields (GF := GF) (V := V) n dq1 is1 cs1 cow1 -∗ nodeFields (V := V) n dq2 is2 cs2 cow2 -∗
      ⌜is1 = is2 ∧ cs1 = cs2 ∧ cow1 = cow2⌝ ∗ nodeFields (V := V) n (dq1 • dq2) is1 cs1 cow1 := by
  unfold nodeFields
  iintro ⟨%Hn, Hi1, Hc1, Hw1⟩ ⟨-, Hi2, Hc2, Hw2⟩
  icombine Hi1 Hi2 gives %Hi
  icombine Hc1 Hc2 gives %Hc
  icombine Hw1 Hw2 gives %Hw
  subst Hi Hc Hw
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitl []
  · ipureintro; exact Hn
  isplitl [Hi1 Hi2]
  · iapply tp_combine dq1 dq2 _ _; iframe
  isplitl [Hc1 Hc2]
  · iapply tp_combine dq1 dq2 _ _; iframe
  iapply tp_combine dq1 dq2 _ _; iframe

theorem nodeShallow_combine (hkey : KeysOfItems o) (S : List (V × K)) (dq1 dq2 : DFrac) (n : Loc)
    (is1 is2 : List (V × K)) (ps1 ps2 : List Loc) (h1 : ∀ e ∈ is1, e ∈ S) (h2 : ∀ e ∈ is2, e ∈ S) :
    ⊢ allItems o S -∗ nodeShallow (GF := GF) (V := V) c dq1 n is1 ps1 -∗
      nodeShallow (V := V) c dq2 n is2 ps2 -∗
      ⌜is1 = is2 ∧ ps1 = ps2⌝ ∗ nodeShallow (V := V) c (dq1 • dq2) n is1 ps1 := by
  unfold nodeShallow
  iintro #H ⟨%isl1, %csl1, Hf1, Hi1, Hic1, Hc1, Hcc1⟩ ⟨%isl2, %csl2, Hf2, Hi2, Hic2, Hc2, Hcc2⟩
  icases nodeFields_combine dq1 dq2 n isl1 csl1 isl2 csl2 c c $$ Hf1 Hf2 with ⟨%Hp, Hf⟩
  obtain ⟨Hisl, Hcsl, -⟩ := Hp
  subst Hisl Hcsl
  ihave %Hmap := ownSlice_agree isl1 dq1 dq2 _ _ $$ Hi1 Hi2
  ihave %His := items_agree o hkey S is1 is2 Hmap h1 h2 $$ H
  ihave %Hps := ownSlice_agree csl1 dq1 dq2 _ _ $$ Hc1 Hc2
  subst His Hps
  isplitl []
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists isl1, csl1
  iframe Hf
  isplitl [Hi1 Hi2]
  · iapply slice_combine dq1 dq2 _ _; iframe
  isplitl [Hic1 Hic2]
  · iapply cap_combine V dq1 dq2 _; iframe
  isplitl [Hc1 Hc2]
  · iapply slice_combine dq1 dq2 _ _; iframe
  iapply cap_combine Loc dq1 dq2 _; iframe

/-- An owned node and a frozen one cannot be the same node: their `cow` fields differ. -/
theorem nodeFields_owned_frozen (dq : DFrac) (n : Loc) (is1 cs1 is2 cs2 : GoSlice) (cow : Loc)
    (hcow : cow ≠ c) :
    ⊢ nodeFields (GF := GF) (V := V) n dq is1 cs1 c -∗ nodeFields (V := V) n DFrac.discard is2 cs2 cow -∗
      False := by
  iintro H1 H2
  icases nodeFields_combine dq DFrac.discard n is1 cs1 is2 cs2 c cow $$ H1 H2 with ⟨%Hp, -⟩
  exact absurd Hp.2.2.symm hcow

@[simp] theorem frozenList_nil_cons (t : Tree (V × K)) (ts : List (Tree (V × K))) :
    frozenList o c f less [] (t :: ts) = iprop(False) := by rw [frozenList]
@[simp] theorem frozenList_cons_nil (p : Loc) (ps : List Loc) :
    frozenList o c f less (p :: ps) [] = iprop(False) := by rw [frozenList]
@[simp] theorem ownNodes_nil_cons (dq : DFrac) (t : Tree (V × K)) (ts : List (Tree (V × K))) :
    ownNodes o c f less dq [] (t :: ts) = iprop(False) := by rw [ownNodes]
@[simp] theorem ownNodes_cons_nil (dq : DFrac) (p : Loc) (ps : List Loc) :
    ownNodes o c f less dq (p :: ps) [] = iprop(False) := by rw [ownNodes]

mutual
theorem frozen_agree (hkey : KeysOfItems o) (S : List (V × K)) :
    ∀ (n : Loc) (t1 t2 : Tree (V × K)), (∀ e ∈ t1.elems, e ∈ S) → (∀ e ∈ t2.elems, e ∈ S) →
      ⊢ allItems o S -∗ frozen o c f less n t1 -∗ frozen o c f less n t2 -∗ (⌜t1 = t2⌝ : IProp GF)
  | n, .node is1 cs1, .node is2 cs2, h1, h2 => by
    rw [frozen_node, frozen_node]
    iintro #H ⟨%isl1, %csl1, %cow1, %ps1, #Hf1, -, -, #Hi1, #Hc1, #Hl1⟩
      ⟨%isl2, %csl2, %cow2, %ps2, #Hf2, -, -, #Hi2, #Hc2, #Hl2⟩
    icases nodeFields_combine DFrac.discard DFrac.discard n isl1 csl1 isl2 csl2 cow1 cow2
      $$ Hf1 Hf2 with ⟨%Hp, -⟩
    obtain ⟨Hisl, Hcsl, -⟩ := Hp
    subst Hisl Hcsl
    ihave %Hmap := ownSlice_agree isl1 DFrac.discard DFrac.discard _ _ $$ Hi1 Hi2
    ihave %His := items_agree o hkey S is1 is2 Hmap
      (fun e he => h1 e (Tree.items_subset_elems is1 cs1 e he))
      (fun e he => h2 e (Tree.items_subset_elems is2 cs2 e he)) $$ H
    ihave %Hps := ownSlice_agree csl1 DFrac.discard DFrac.discard _ _ $$ Hc1 Hc2
    subst His Hps
    ihave %Hcs := frozenList_agree hkey S ps1 cs1 cs2
      (fun c hc e he => h1 e (Tree.child_elems_subset_elems is1 cs1 hc e he))
      (fun c hc e he => h2 e (Tree.child_elems_subset_elems is1 cs2 hc e he)) $$ H Hl1 Hl2
    ipureintro
    rw [Hcs]

theorem frozenList_agree (hkey : KeysOfItems o) (S : List (V × K)) :
    ∀ (ps : List Loc) (ts1 ts2 : List (Tree (V × K))),
      (∀ t ∈ ts1, ∀ e ∈ t.elems, e ∈ S) → (∀ t ∈ ts2, ∀ e ∈ t.elems, e ∈ S) →
      ⊢ allItems o S -∗ frozenList o c f less ps ts1 -∗ frozenList o c f less ps ts2 -∗
        (⌜ts1 = ts2⌝ : IProp GF)
  | [], [], [], _, _ => by iintro _ _ _; ipureintro; rfl
  | p :: ps, t1 :: ts1, t2 :: ts2, h1, h2 => by
    simp only [frozenList_cons]
    iintro #H ⟨#H1, #Hs1⟩ ⟨#H2, #Hs2⟩
    ihave %Ht := frozen_agree hkey S p t1 t2 (h1 t1 List.mem_cons_self)
      (h2 t2 List.mem_cons_self) $$ H H1 H2
    ihave %Hts := frozenList_agree hkey S ps ts1 ts2
      (fun t ht => h1 t (List.mem_cons_of_mem _ ht)) (fun t ht => h2 t (List.mem_cons_of_mem _ ht))
      $$ H Hs1 Hs2
    ipureintro
    rw [Ht, Hts]
  | [], _ :: _, _, _, _ => by simp only [frozenList_nil_cons]; iintro - %h -; exact h.elim
  | [], [], _ :: _, _, _ => by simp only [frozenList_nil_cons]; iintro - - %h; exact h.elim
  | _ :: _, [], _, _, _ => by simp only [frozenList_cons_nil]; iintro - %h -; exact h.elim
  | _ :: _, _ :: _, [], _, _ => by simp only [frozenList_cons_nil]; iintro - - %h; exact h.elim
end

mutual
/-- Two fractions of a node describe the same subtree, and combine. -/
theorem ownNode_combine (hkey : KeysOfItems o) (S : List (V × K)) (dq1 dq2 : DFrac) :
    ∀ (n : Loc) (t1 t2 : Tree (V × K)), (∀ e ∈ t1.elems, e ∈ S) → (∀ e ∈ t2.elems, e ∈ S) →
      ⊢ allItems o S -∗ ownNode o c f less dq1 n t1 -∗ ownNode o c f less dq2 n t2 -∗
        ⌜t1 = t2⌝ ∗ ownNode o c f less (dq1 • dq2) n t1
  | n, .node is1 cs1, .node is2 cs2, h1, h2 => by
    rw [ownNode_node, ownNode_node, ownNode_node]
    unfold ownedNode
    simp only [Tree.items_node, Tree.children_node]
    iintro #H (⟨%ps1, Hsh1, Hns1⟩ | #Hfr1) (⟨%ps2, Hsh2, Hns2⟩ | #Hfr2)
    · icases nodeShallow_combine o c hkey S dq1 dq2 n is1 is2 ps1 ps2
        (fun e he => h1 e (Tree.items_subset_elems is1 cs1 e he))
        (fun e he => h2 e (Tree.items_subset_elems is2 cs2 e he)) $$ H Hsh1 Hsh2
        with ⟨%Hp, Hsh⟩
      obtain ⟨His, Hps⟩ := Hp
      subst His Hps
      icases ownNodes_combine hkey S dq1 dq2 ps1 cs1 cs2
        (fun c hc e he => h1 e (Tree.child_elems_subset_elems is1 cs1 hc e he))
        (fun c hc e he => h2 e (Tree.child_elems_subset_elems is1 cs2 hc e he)) $$ H Hns1 Hns2
        with ⟨%Hcs, Hns⟩
      subst Hcs
      isplitl []
      · ipureintro; rfl
      ileft; iexists ps1; iframe
    · iexfalso
      unfold nodeShallow
      icases Hsh1 with ⟨%isl1, %csl1, Hf1, -, -, -, -⟩
      rw [frozen_node]
      icases Hfr2 with ⟨%isl2, %csl2, %cow2, %ps2, #Hf2, %Hcow, -, -, -, -⟩
      iapply nodeFields_owned_frozen c dq1 n isl1 csl1 isl2 csl2 cow2 Hcow $$ Hf1 Hf2
    · iexfalso
      unfold nodeShallow
      icases Hsh2 with ⟨%isl2, %csl2, Hf2, -, -, -, -⟩
      rw [frozen_node]
      icases Hfr1 with ⟨%isl1, %csl1, %cow1, %ps1, #Hf1, %Hcow, -, -, -, -⟩
      iapply nodeFields_owned_frozen c dq2 n isl2 csl2 isl1 csl1 cow1 Hcow $$ Hf2 Hf1
    · ihave %Ht := frozen_agree o c f less hkey S n (.node is1 cs1) (.node is2 cs2) h1 h2
        $$ H Hfr1 Hfr2
      isplitl []
      · ipureintro; exact Ht
      iright; iexact Hfr1

theorem ownNodes_combine (hkey : KeysOfItems o) (S : List (V × K)) (dq1 dq2 : DFrac) :
    ∀ (ps : List Loc) (ts1 ts2 : List (Tree (V × K))),
      (∀ t ∈ ts1, ∀ e ∈ t.elems, e ∈ S) → (∀ t ∈ ts2, ∀ e ∈ t.elems, e ∈ S) →
      ⊢ allItems o S -∗ ownNodes o c f less dq1 ps ts1 -∗ ownNodes o c f less dq2 ps ts2 -∗
        ⌜ts1 = ts2⌝ ∗ ownNodes o c f less (dq1 • dq2) ps ts1
  | [], [], [], _, _ => by
    simp only [ownNodes_nil]
    iintro _ _ _; isplitl [] <;> itrivial
  | p :: ps, t1 :: ts1, t2 :: ts2, h1, h2 => by
    simp only [ownNodes_cons]
    iintro #H ⟨H1, Hs1⟩ ⟨H2, Hs2⟩
    icases ownNode_combine hkey S dq1 dq2 p t1 t2 (h1 t1 List.mem_cons_self)
      (h2 t2 List.mem_cons_self) $$ H H1 H2 with ⟨%Ht, Hn⟩
    subst Ht
    icases ownNodes_combine hkey S dq1 dq2 ps ts1 ts2
      (fun t ht => h1 t (List.mem_cons_of_mem _ ht)) (fun t ht => h2 t (List.mem_cons_of_mem _ ht))
      $$ H Hs1 Hs2 with ⟨%Hts, Hns⟩
    subst Hts
    isplitl []
    · ipureintro; rfl
    iframe
  | [], _ :: _, _, _, _ => by simp only [ownNodes_nil_cons]; iintro - %h -; exact h.elim
  | [], [], _ :: _, _, _ => by simp only [ownNodes_nil_cons]; iintro - - %h; exact h.elim
  | _ :: _, [], _, _, _ => by simp only [ownNodes_cons_nil]; iintro - %h -; exact h.elim
  | _ :: _, _ :: _, [], _, _ => by simp only [ownNodes_cons_nil]; iintro - - %h; exact h.elim
end

theorem ownNode_null_absurd (dq : DFrac) (t : Tree (V × K)) :
    ownNode o c f less dq null t ⊢ (False : IProp GF) := by
  cases t with
  | node is cs =>
    rw [ownNode_node]
    unfold ownedNode nodeShallow nodeFields
    rw [frozen_node]
    unfold nodeFields
    iintro (⟨%ps, ⟨%isl, %csl, ⟨%Hn, -⟩, -⟩, -⟩ | ⟨%isl, %csl, %cow, %ps, ⟨%Hn, -⟩, -⟩)
    · exact absurd rfl Hn
    · exact absurd rfl Hn

theorem allItems_app (s1 s2 : List (V × K)) :
    allItems o s1 ∗ allItems o s2 ⊢ allItems o (s1 ++ s2) := by
  unfold allItems
  iintro ⟨#H1, #H2⟩
  imodintro
  iintro %e %he
  rcases List.mem_append.1 he with he | he
  · iapply H1; ipureintro; exact he
  · iapply H2; ipureintro; exact he

theorem ownRoot_combine (hkey : KeysOfItems o) (d : Nat) (dq1 dq2 : DFrac) (r : Loc)
    (s1 s2 : List (V × K)) :
    ⊢ allItems o s1 -∗ allItems o s2 -∗ ownRoot o c f less d dq1 r s1 -∗
      ownRoot o c f less d dq2 r s2 -∗ ⌜s1 = s2⌝ ∗ ownRoot o c f less d (dq1 • dq2) r s1 := by
  unfold ownRoot
  iintro #H1 #H2 (%Hnil1 | ⟨%h1, %tr1, %Htr1, H1⟩) (%Hnil2 | ⟨%h2, %tr2, %Htr2, H2⟩)
  · isplitl []
    · ipureintro; rw [Hnil1.2, Hnil2.2]
    ileft; ipureintro; exact Hnil1
  · iexfalso; rw [Hnil1.1]; iapply ownNode_null_absurd o c f less dq2 tr2 $$ H2
  · iexfalso; rw [Hnil2.1]; iapply ownNode_null_absurd o c f less dq1 tr1 $$ H1
  · ihave #H : allItems o (s1 ++ s2) $$ [H1 H2]
    · iapply allItems_app o s1 s2; iframe #
    icases ownNode_combine o c f less hkey (s1 ++ s2) dq1 dq2 r tr1 tr2
      (fun e he => List.mem_append_left _ (Htr1.2.2 ▸ he))
      (fun e he => List.mem_append_right _ (Htr2.2.2 ▸ he)) $$ H H1 H2 with ⟨%Ht, Hn⟩
    isplitl []
    · ipureintro; rw [← Htr1.2.2, ← Htr2.2.2, Ht]
    iright; iexists h1, tr1; iframe Hn; ipureintro; exact Htr1

theorem isCow_agree (c0 : Loc) (f1 f2 : Loc) (less1 less2 : GoFunc) :
    ⊢ isCow o c0 f1 less1 -∗ isCow o c0 f2 less2 -∗ (⌜f1 = f2 ∧ less1 = less2⌝ : IProp GF) := by
  unfold isCow
  iintro ⟨#Hc1, -, -⟩ ⟨#Hc2, -, -⟩
  icombine Hc1 Hc2 gives %Heq
  ipureintro
  exact ⟨congrArg copyOnWriteContext.freelist' Heq, congrArg copyOnWriteContext.less' Heq⟩

/-- **Combining readers' fractions of a tree** (the converse of `ownBTree_split`), when the
keys are determined by the items: the two describe the same entries. -/
theorem ownBTree_combine (hkey : KeysOfItems o) (t : Loc) (dq1 dq2 : DFrac) (s1 s2 : List (V × K)) :
    ownBTree o t dq1 s1 ∗ ownBTree o t dq2 s2 ⊢ ⌜s1 = s2⌝ ∗ ownBTree o t (dq1 • dq2) s1 := by
  unfold ownBTree
  iintro ⟨⟨%tv1, %f1, %less1, %d1, H1⟩, ⟨%tv2, %f2, %less2, %d2, H2⟩⟩
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine Ht1 Ht2 gives %Htv
  subst Htv
  ihave %Hcow := isCow_agree o tv1.cow' f1 f2 less1 less2 $$ Hcow1 Hcow2
  obtain ⟨rfl, rfl⟩ := Hcow
  have Hd : d1 = d2 := by omega
  subst Hd
  icases ownRoot_combine o tv1.cow' f1 less1 hkey d1 dq1 dq2 tv1.root' s1 s2
    $$ Hitems1 Hitems2 Hroot1 Hroot2 with ⟨%Hs, Hroot⟩
  subst Hs
  isplitl []
  · ipureintro; rfl
  iexists tv1, f1, less1, d1
  iframe Hcow1 Hitems1
  isplitl [Ht1 Ht2]
  · iapply tp_combine dq1 dq2 _ _; iframe
  simp only [named]
  isplitl []
  · ipureintro; exact Hdeg1
  isplitl []
  · ipureintro; exact Hlen1
  isplitl []
  · ipureintro; exact Hsorted1
  iexact Hroot

end combine

end btree
end EtcdGrove
end Perennial
