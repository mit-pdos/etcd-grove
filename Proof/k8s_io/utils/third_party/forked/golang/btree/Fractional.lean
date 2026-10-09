/-
Splitting a tree between readers: `ownBTree t (dq1 • dq2) s` is two `ownBTree`s at
`dq1` and `dq2` (every read-only method takes any fraction), e.g. a snapshot read by
several goroutines.
-/

module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.NodeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section frac
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

theorem tp_split {A : Type} [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac) (l : Loc) (v : A) :
    typedPointsto (GF := GF) l v (dq1 • dq2) ⊢ typedPointsto l v dq1 ∗ typedPointsto l v dq2 :=
  (dfractional (Φ := fun dq => typedPointsto (GF := GF) l v dq) dq1 dq2).1

theorem slice_split {A : Type} [ZeroVal A] [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac)
    (sl : GoSlice) (vs : List A) :
    sl ↦*{dq1 • dq2} vs ⊢ (sl ↦*{dq1} vs ∗ sl ↦*{dq2} vs : IProp GF) :=
  (dfractional (Φ := fun dq => (sl ↦*{dq} vs : IProp GF)) dq1 dq2).1

theorem cap_split (A : Type) [ZeroVal A] [TypedPointsto (GF := GF) A] (dq1 dq2 : DFrac)
    (sl : GoSlice) :
    ownSliceCap (GF := GF) A sl (dq1 • dq2) ⊢ ownSliceCap A sl dq1 ∗ ownSliceCap A sl dq2 :=
  (dfractional (Φ := fun dq => ownSliceCap (GF := GF) A sl dq) dq1 dq2).1

theorem nodeFields_split (dq1 dq2 : DFrac) (n : Loc) (is cs : GoSlice) (cow : Loc) :
    nodeFields (GF := GF) (V := V) n (dq1 • dq2) is cs cow ⊢
      nodeFields (V := V) n dq1 is cs cow ∗ nodeFields (V := V) n dq2 is cs cow := by
  unfold nodeFields
  iintro ⟨%Hn, Hi, Hc, Hw⟩
  icases tp_split dq1 dq2 _ _ $$ Hi with ⟨Hi1, Hi2⟩
  icases tp_split dq1 dq2 _ _ $$ Hc with ⟨Hc1, Hc2⟩
  icases tp_split dq1 dq2 _ _ $$ Hw with ⟨Hw1, Hw2⟩
  isplitl [Hi1 Hc1 Hw1]
  · iframe; ipureintro; exact Hn
  · iframe; ipureintro; exact Hn

theorem nodeShallow_split (dq1 dq2 : DFrac) (n : Loc) (is : List (V × K)) (ps : List Loc) :
    nodeShallow (GF := GF) (V := V) c (dq1 • dq2) n is ps ⊢
      nodeShallow (V := V) c dq1 n is ps ∗ nodeShallow (V := V) c dq2 n is ps := by
  unfold nodeShallow
  iintro ⟨%isl, %csl, Hf, Hi, Hic, Hc, Hcc⟩
  icases slice_split dq1 dq2 _ _ $$ Hi with ⟨Hi1, Hi2⟩
  icases cap_split V dq1 dq2 _ $$ Hic with ⟨Hic1, Hic2⟩
  icases slice_split dq1 dq2 _ _ $$ Hc with ⟨Hc1, Hc2⟩
  icases cap_split Loc dq1 dq2 _ $$ Hcc with ⟨Hcc1, Hcc2⟩
  icases nodeFields_split dq1 dq2 n isl csl c $$ Hf with ⟨Hf1, Hf2⟩
  isplitl [Hf1 Hi1 Hic1 Hc1 Hcc1]
  · iexists isl, csl; iframe
  · iexists isl, csl; iframe

mutual
theorem ownNode_split (dq1 dq2 : DFrac) : ∀ (n : Loc) (t : Tree (V × K)),
    ownNode o c f less (dq1 • dq2) n t ⊢
      ownNode o c f less dq1 n t ∗ ownNode o c f less dq2 n t
  | n, .node is cs => by
    rw [ownNode_node, ownNode_node, ownNode_node]
    unfold ownedNode
    simp only [Tree.items_node, Tree.children_node]
    iintro (⟨%ps, Hsh, Hns⟩ | #Hfr)
    · icases nodeShallow_split c dq1 dq2 n is ps $$ Hsh with ⟨H1, H2⟩
      icases ownNodes_split dq1 dq2 ps cs $$ Hns with ⟨N1, N2⟩
      isplitl [H1 N1]
      · ileft; iexists ps; iframe
      · ileft; iexists ps; iframe
    · isplitl []
      · iright; iexact Hfr
      · iright; iexact Hfr

theorem ownNodes_split (dq1 dq2 : DFrac) : ∀ (ps : List Loc) (ts : List (Tree (V × K))),
    ownNodes o c f less (dq1 • dq2) ps ts ⊢
      ownNodes o c f less dq1 ps ts ∗ ownNodes o c f less dq2 ps ts
  | [], [] => by simp only [ownNodes_nil]; iintro _; isplitl [] <;> itrivial
  | p :: ps, t :: ts => by
    simp only [ownNodes_cons]
    iintro ⟨H, Hs⟩
    icases ownNode_split dq1 dq2 p t $$ H with ⟨H1, H2⟩
    icases ownNodes_split dq1 dq2 ps ts $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [H1 Hs1] <;> iframe
  | [], _ :: _ => by rw [ownNodes]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [ownNodes]; iintro %h; exact h.elim
end

theorem ownRoot_split (d : Nat) (dq1 dq2 : DFrac) (r : Loc) (s : List (V × K)) :
    ownRoot o c f less d (dq1 • dq2) r s ⊢
      ownRoot o c f less d dq1 r s ∗ ownRoot o c f less d dq2 r s := by
  unfold ownRoot
  iintro (%Hnil | ⟨%h, %tr, %Htr, H⟩)
  · isplitl [] <;> (ileft; ipureintro; exact Hnil)
  · icases ownNode_split o c f less dq1 dq2 r tr $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iright; iexists h, tr; iframe; ipureintro; exact Htr
    · iright; iexists h, tr; iframe; ipureintro; exact Htr

/-- **Splitting a tree between readers.** -/
theorem ownBTree_split (t : Loc) (dq1 dq2 : DFrac) (s : List (V × K)) :
    ownBTree o t (dq1 • dq2) s ⊢ ownBTree o t dq1 s ∗ ownBTree o t dq2 s := by
  unfold ownBTree
  iintro H
  iNamed H
  icases tp_split dq1 dq2 _ _ $$ Ht with ⟨Ht1, Ht2⟩
  icases ownRoot_split o _ _ _ _ dq1 dq2 _ s $$ Hroot with ⟨Hr1, Hr2⟩
  isplitl [Ht1 Hr1]
  · iexists tv, f, less, d; iframe Ht1 Hr1 Hcow Hitems; ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩
  · iexists tv, f, less, d; iframe Ht2 Hr2 Hcow Hitems; ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩

/-! ### Read-only for good: `ownBTree … dq ==∗ ownBTree … discard` -/

theorem nodeShallow_persistent (n : Loc) (is : List (V × K)) (ps : List Loc) :
    Persistent (nodeShallow (GF := GF) (V := V) c DFrac.discard n is ps) := by
  unfold nodeShallow; infer_instance

mutual
theorem ownNode_persistent' : ∀ (n : Loc) (t : Tree (V × K)),
    Persistent (ownNode o c f less DFrac.discard n t)
  | n, .node is cs => by
    rw [ownNode_node]
    unfold ownedNode
    simp only [Tree.items_node, Tree.children_node]
    have : ∀ ps, Persistent (ownNodes o c f less DFrac.discard ps cs) :=
      fun ps => ownNodes_persistent' ps cs
    have := nodeShallow_persistent (GF := GF) (V := V) (K := K) c
    infer_instance

theorem ownNodes_persistent' : ∀ (ps : List Loc) (ts : List (Tree (V × K))),
    Persistent (ownNodes o c f less DFrac.discard ps ts)
  | [], [] => by rw [ownNodes]; infer_instance
  | p :: ps, t :: ts => by
    rw [ownNodes]
    have := ownNode_persistent' p t
    have := ownNodes_persistent' ps ts
    infer_instance
  | [], _ :: _ => by rw [ownNodes]; infer_instance
  | _ :: _, [] => by rw [ownNodes]; infer_instance
end

instance ownNode_persistent (n : Loc) (t : Tree (V × K)) :
    Persistent (ownNode o c f less DFrac.discard n t) :=
  ownNode_persistent' o c f less n t

instance ownNodes_persistent (ps : List Loc) (ts : List (Tree (V × K))) :
    Persistent (ownNodes o c f less DFrac.discard ps ts) :=
  ownNodes_persistent' o c f less ps ts

instance ownRoot_persistent (d : Nat) (r : Loc) (s : List (V × K)) :
    Persistent (ownRoot o c f less d DFrac.discard r s) := by
  unfold ownRoot; infer_instance

instance ownBTree_persistent (t : Loc) (s : List (V × K)) :
    Persistent (ownBTree o t DFrac.discard s) := by
  unfold ownBTree; infer_instance

theorem nodeFields_persist (dq : DFrac) (n : Loc) (is cs : GoSlice) (cow : Loc) :
    nodeFields (GF := GF) (V := V) n dq is cs cow ⊢ |==> nodeFields (V := V) n DFrac.discard is cs cow := by
  unfold nodeFields
  iintro ⟨%Hn, Hi, Hc, Hw⟩
  ipersist Hi
  ipersist Hc
  ipersist Hw
  imodintro
  iframe # ∗; ipureintro; exact Hn

theorem nodeShallow_persist (dq : DFrac) (n : Loc) (is : List (V × K)) (ps : List Loc) :
    nodeShallow (GF := GF) (V := V) c dq n is ps ⊢ |==> nodeShallow (V := V) c DFrac.discard n is ps := by
  unfold nodeShallow
  iintro ⟨%isl, %csl, Hf, Hi, Hic, Hc, Hcc⟩
  imod nodeFields_persist dq n isl csl c $$ Hf with Hf
  ipersist Hi
  ipersist Hic
  ipersist Hc
  ipersist Hcc
  imodintro
  iexists isl, csl; iframe # ∗

mutual
theorem ownNode_persist (dq : DFrac) : ∀ (n : Loc) (t : Tree (V × K)),
    ownNode o c f less dq n t ⊢ |==> ownNode o c f less DFrac.discard n t
  | n, .node is cs => by
    rw [ownNode_node, ownNode_node]
    unfold ownedNode
    simp only [Tree.items_node, Tree.children_node]
    iintro (⟨%ps, Hsh, Hns⟩ | #Hfr)
    · imod nodeShallow_persist c dq n is ps $$ Hsh with Hsh
      imod ownNodes_persist dq ps cs $$ Hns with Hns
      imodintro
      ileft; iexists ps; iframe
    · imodintro; iright; iexact Hfr

theorem ownNodes_persist (dq : DFrac) : ∀ (ps : List Loc) (ts : List (Tree (V × K))),
    ownNodes o c f less dq ps ts ⊢ |==> ownNodes o c f less DFrac.discard ps ts
  | [], [] => by simp only [ownNodes_nil]; iintro _; imodintro; itrivial
  | p :: ps, t :: ts => by
    simp only [ownNodes_cons]
    iintro ⟨H, Hs⟩
    imod ownNode_persist dq p t $$ H with H
    imod ownNodes_persist dq ps ts $$ Hs with Hs
    imodintro
    iframe
  | [], _ :: _ => by rw [ownNodes]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [ownNodes]; iintro %h; exact h.elim
end

theorem ownRoot_persist (d : Nat) (dq : DFrac) (r : Loc) (s : List (V × K)) :
    ownRoot o c f less d dq r s ⊢ |==> ownRoot o c f less d DFrac.discard r s := by
  unfold ownRoot
  iintro (%Hnil | ⟨%h, %tr, %Htr, H⟩)
  · imodintro; ileft; ipureintro; exact Hnil
  · imod ownNode_persist o c f less dq r tr $$ H with H
    imodintro
    iright; iexists h, tr; iframe; ipureintro; exact Htr

/-- **Making a tree read-only for good.** -/
theorem ownBTree_persist (t : Loc) (dq : DFrac) (s : List (V × K)) :
    ownBTree o t dq s ⊢ |==> ownBTree o t DFrac.discard s := by
  unfold ownBTree
  iintro H
  iNamed H
  ipersist Ht
  imod ownRoot_persist o _ _ _ _ dq _ s $$ Hroot with Hroot
  imodintro
  iexists tv, f, less, d; iframe Ht Hroot Hcow Hitems; ipureintro; exact ⟨Hdeg, Hlen, Hsorted⟩

end frac

end btree
end EtcdGrove
end Perennial
