/-
Lemmas for the structural node operations (`mutableFor`, `split`, `Clone`, ...).
-/
import EtcdGrove.Btree.NodeLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

/-- Frozen children are owned children (in their frozen disjunct). -/
theorem ownNodes_of_frozenList (dq : DFrac) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      frozenList o c f less ps ts ⊢ ownNodes o c f less dq ps ts
  | [], [] => by rw [frozenList_nil, ownNodes_nil]
  | p :: ps, t :: ts => by
    rw [frozenList_cons, ownNodes_cons]
    iintro ⟨H1, H2⟩
    isplitl [H1]
    · iapply ownNode_of_frozen; iexact H1
    · iapply ownNodes_of_frozenList dq ps ts $$ H2
  | [], _ :: _ => by rw [frozenList]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [frozenList]; iintro %h; exact h.elim

/-- Split a list of children at `k`. -/
theorem ownNodes_take_drop (dq : DFrac) (k : Nat) (ps : List Loc) (ts : List (Tree (V × K)))
    (hl : ps.length = ts.length) :
    ownNodes o c f less dq ps ts ⊢
      ownNodes o c f less dq (ps.take k) (ts.take k) ∗
        ownNodes o c f less dq (ps.drop k) (ts.drop k) := by
  have h := ownNodes_app o c f less dq (ps.take k) (ps.drop k) (ts.take k) (ts.drop k)
    (by simp [hl])
  rw [List.take_append_drop, List.take_append_drop] at h
  exact h.1

/-- Read access to a subtree's item field (its slice has as many elements as the root
has items), owned or frozen. -/
theorem ownNode_items_acc (dq : DFrac) (p : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    ownNode o c f less dq p (.node is cs) ⊢
      ∃ (isl : GoSlice) (dq' : DFrac),
        structFieldRef (node V) go!"items" p ↦{dq'} isl ∗ ⌜is.length = sint.nat isl.len⌝ ∗
        (structFieldRef (node V) go!"items" p ↦{dq'} isl -∗
          ownNode o c f less dq p (.node is cs)) := by
  rw [ownNode_node]
  unfold ownedNode nodeShallow nodeFields
  rw [frozen_node]
  unfold nodeFields
  simp only [Tree.items_node, Tree.children_node]
  iintro (⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, Hrest⟩, Hch⟩ |
    ⟨%isl, %csl, %cw, %ps, ⟨%Hnn, Hfi, Hfc, Hfw⟩, %Hne, #Hcw, #Hisl, #Hcsl, #Hch⟩)
  · ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, dq
    iframe Hfi
    isplitr
    · ipureintro; simpa using Hl.1
    iintro Hfi
    ileft
    iexists ps
    iframe Hch
    iexists isl, csl
    iframe
    ipureintro; exact Hnn
  · ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, DFrac.discard
    iframe Hfi
    isplitr
    · ipureintro; simpa using Hl.1
    iintro Hfi
    iright
    iexists isl, csl, cw, ps
    iframe Hfi Hfc Hfw Hcw Hisl Hcsl Hch
    ipureintro; exact ⟨Hnn, Hne⟩

/-- A child split in two: `ts[i]` (at `ps[i]`) is replaced by `t1` at `p1` and `t2` at
`p2`. -/
theorem ownNodes_split_child (dq : DFrac) (ps : List Loc) (ts : List (Tree (V × K))) (i : Nat)
    (hi : i < ps.length) (hl : ps.length = ts.length) (p1 p2 : Loc) (t1 t2 : Tree (V × K)) :
    ownNodes o c f less dq (ps.eraseIdx i) (ts.eraseIdx i) ∗
      ownNode o c f less dq p1 t1 ∗ ownNode o c f less dq p2 t2 ⊢
      ownNodes o c f less dq ((ps.set i p1).take (i + 1) ++ p2 :: (ps.set i p1).drop (i + 1))
        (ts.take i ++ t1 :: t2 :: ts.drop (i + 1)) := by
  have hps : (ps.set i p1).take (i + 1) ++ p2 :: (ps.set i p1).drop (i + 1) =
      ps.take i ++ p1 :: p2 :: ps.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    have h1 : (ps.take i).length = i := by simp; omega
    have ht : (ps.take i ++ p1 :: ps.drop (i + 1)).take (i + 1) = ps.take i ++ [p1] := by
      rw [List.take_append, h1, List.take_of_length_le (by omega),
        show i + 1 - i = 1 by omega]
      simp
    have hd : (ps.take i ++ p1 :: ps.drop (i + 1)).drop (i + 1) = ps.drop (i + 1) := by
      rw [List.drop_append, h1, List.drop_of_length_le (by omega),
        show i + 1 - i = 1 by omega]
      simp
    rw [ht, hd]
    simp
  rw [hps, List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
  have hl1 : (ps.take i).length = (ts.take i).length := by simp [hl]
  iintro ⟨H, H1, H2⟩
  icases (ownNodes_app o c f less dq _ _ _ _ hl1).1 $$ H with ⟨Ha, Hb⟩
  iapply (ownNodes_app o c f less dq _ _ _ _ hl1).2
  iframe Ha
  rw [ownNodes_cons, ownNodes_cons]
  iframe

/-! ### Clone: freezing a tree for two fresh contexts -/

/-- A fresh (fully owned) context is not a context some persistent points-to names. -/
theorem cow_ne (c1 cw : Loc) (v w : copyOnWriteContext V) :
    c1 ↦ v ⊢ cw ↦□ w -∗ (⌜cw ≠ c1⌝ : IProp GF) := by
  by_cases h : cw = c1
  · subst h
    iintro H1 H2
    icases typedPointsto_split _ _ _ $$ H1 with H1
    icases typedPointsto_split _ _ _ $$ H2 with H2
    simp only [TypedPointsto.typedPointstoDef]
    iNamedSuffix H1 "1"
    iNamedSuffix H2 "2"
    icases typedPointsto_split _ _ _ $$ freelist1 with F1
    icases typedPointsto_split _ _ _ $$ freelist2 with F2
    rw [typedPointstoDef_heap, typedPointstoDef_heap]
    icombine F1 F2 gives % ⟨Hv, _⟩
    exact absurd Hv (by rw [DFrac.valid_own_op_discard]; simp)
  · iintro _ _; ipureintro; exact h

mutual
/-- A frozen subtree stays frozen relative to a fresh context `c'`: no node of it has
`c'` as its context. -/
theorem frozen_retarget (c0 c' : Loc) (v : copyOnWriteContext V) :
    ∀ (n : Loc) (t : Tree (V × K)),
      c' ↦ v ∗ frozen o c0 f less n t ⊢ c' ↦ v ∗ frozen o c' f less n t
  | n, .node is cs => by
    rw [frozen_node, frozen_node]
    iintro ⟨Hc, ⟨%isl, %csl, %cw, %ps, #Hf, %Hne, #Hcw, #Hisl, #Hcsl, #Hch⟩⟩
    ihave #Hcwp : (cw ↦□ (copyOnWriteContext.mk f less : copyOnWriteContext V) : IProp GF) $$ [Hcw]
    · unfold isCow; icases Hcw with ⟨#H, -, -⟩; iexact H
    ihave %Hne' := cow_ne c' cw v _ $$ Hc Hcwp
    icases frozenList_retarget c0 c' v ps cs $$ [$Hc $Hch] with ⟨Hc, #Hch'⟩
    iframe Hc
    iexists isl, csl, cw, ps
    iframe Hf Hcw Hisl Hcsl Hch'
    ipureintro; exact Hne'

theorem frozenList_retarget (c0 c' : Loc) (v : copyOnWriteContext V) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      c' ↦ v ∗ frozenList o c0 f less ps ts ⊢ c' ↦ v ∗ frozenList o c' f less ps ts
  | [], [] => by rw [frozenList_nil, frozenList_nil]
  | p :: ps, t :: ts => by
    rw [frozenList_cons, frozenList_cons]
    iintro ⟨Hc, H1, H2⟩
    icases frozen_retarget c0 c' v p t $$ [$Hc $H1] with ⟨Hc, H1⟩
    icases frozenList_retarget c0 c' v ps ts $$ [$Hc $H2] with ⟨Hc, H2⟩
    iframe
  | [], _ :: _ => by rw [frozenList]; iintro ⟨_, %h⟩; exact h.elim
  | _ :: _, [] => by rw [frozenList]; iintro ⟨_, %h⟩; exact h.elim
end

mutual
/-- Freeze a subtree of a tree with context `c` relative to a fresh context `c1`: its
owned nodes become read-only (their points-tos persistent), and none of its nodes has
context `c1`. -/
theorem ownNode_freeze (c1 : Loc) (v : copyOnWriteContext V) :
    ∀ (n : Loc) (t : Tree (V × K)),
      isCow o c f less ∗ c1 ↦ v ∗ ownNode o c f less (DFrac.own 1) n t ⊢
        |==> (c1 ↦ v ∗ frozen o c1 f less n t)
  | n, .node is cs => by
    rw [ownNode_node]
    unfold ownedNode nodeShallow nodeFields
    simp only [Tree.items_node, Tree.children_node]
    iintro ⟨#Hcow, Hc1, (⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hfi, Hfc, Hfw⟩, Hisl, -, Hcsl, -⟩, Hch⟩ | Hfr)⟩
    · ihave #Hcp : (c ↦□ (copyOnWriteContext.mk f less : copyOnWriteContext V) : IProp GF) $$ []
      · unfold isCow; icases Hcow with ⟨#H, -, -⟩; iexact H
      ihave %Hne := cow_ne c1 c v _ $$ Hc1 Hcp
      imod ownNodes_freeze c1 v ps cs $$ [$Hcow $Hc1 $Hch] with ⟨Hc1, #Hch⟩
      ipersist Hfi
      ipersist Hfc
      ipersist Hfw
      ipersist Hisl
      ipersist Hcsl
      imodintro
      iframe Hc1
      rw [frozen_node]
      iexists isl, csl, c, ps
      unfold nodeFields
      iframe Hfi Hfc Hfw Hcow Hisl Hcsl Hch
      ipureintro; exact ⟨Hnn, Hne⟩
    · icases frozen_retarget o f less c c1 v n _ $$ [$Hc1 $Hfr] with ⟨Hc1, Hfr⟩
      imodintro
      iframe

theorem ownNodes_freeze (c1 : Loc) (v : copyOnWriteContext V) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      isCow o c f less ∗ c1 ↦ v ∗ ownNodes o c f less (DFrac.own 1) ps ts ⊢
        |==> (c1 ↦ v ∗ frozenList o c1 f less ps ts)
  | [], [] => by
    rw [ownNodes_nil, frozenList_nil]
    iintro ⟨_, Hc1, _⟩; imodintro; iframe
  | p :: ps, t :: ts => by
    rw [ownNodes_cons, frozenList_cons]
    iintro ⟨#Hcow, Hc1, H1, H2⟩
    imod ownNode_freeze c1 v p t $$ [$Hcow $Hc1 $H1] with ⟨Hc1, H1⟩
    imod ownNodes_freeze c1 v ps ts $$ [$Hcow $Hc1 $H2] with ⟨Hc1, H2⟩
    imodintro
    iframe
  | [], _ :: _ => by rw [ownNodes]; iintro ⟨_, _, %h⟩; exact h.elim
  | _ :: _, [] => by rw [ownNodes]; iintro ⟨_, _, %h⟩; exact h.elim
end

/-- `Clone` on the root: the tree is frozen relative to both fresh contexts. -/
theorem ownRoot_clone (c1 c2 : Loc) (v1 v2 : copyOnWriteContext V) (d : Nat) (r : Loc)
    (s : List (V × K)) :
    isCow o c f less ∗ c1 ↦ v1 ∗ c2 ↦ v2 ∗ ownRoot o c f less d (DFrac.own 1) r s ⊢
      |==> (c1 ↦ v1 ∗ c2 ↦ v2 ∗ ownRoot o c1 f less d (DFrac.own 1) r s ∗
        ownRoot o c2 f less d (DFrac.own 1) r s) := by
  unfold ownRoot
  iintro ⟨#Hcow, Hc1, Hc2, (%Hnil | ⟨%h, %tr, %Htr, Hn⟩)⟩
  · imodintro
    iframe
    isplitl
    · ileft; ipureintro; exact Hnil
    · ileft; ipureintro; exact Hnil
  · imod ownNode_freeze o c f less c1 v1 r tr $$ [$Hcow $Hc1 $Hn] with ⟨Hc1, #Hfr⟩
    icases frozen_retarget o f less c1 c2 v2 r tr $$ [$Hc2 $Hfr] with ⟨Hc2, #Hfr2⟩
    imodintro
    iframe Hc1 Hc2
    isplitl
    · iright; iexists h, tr; iframe %Htr
      iapply ownNode_of_frozen; iexact Hfr
    · iright; iexists h, tr; iframe %Htr
      iapply ownNode_of_frozen; iexact Hfr2

end lemmas

end Btree
end EtcdGrove
end Perennial
