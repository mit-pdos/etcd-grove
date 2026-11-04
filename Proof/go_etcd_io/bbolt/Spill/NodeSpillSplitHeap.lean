/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`): the heap steps. Fresh nodes put into a
bucket one by one (`wtxHeap_putNew`, `Write.wtxHeap_node_insert`), the points-tos of a list of
nodes distinct and fresh (`ptsL_nodup`, `ptsL_notin`, `wtxHeap_freshL`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitPut
public import Proof.go_etcd_io.bbolt.Write.NodeAdd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Fresh nodes into bucket `bl`** (record `B`), live. -/
theorem wtxHeap_putNew (tx : Loc) (dq : DFrac) (ps : List (Loc × NRec)) :
    ∀ (X : WX) (bl : Loc) (B : BRec), X.t.bs !! bl = some B → (ps.map (·.1)).Nodup →
      (∀ p ∈ ps, X.t.objs !! p.1 = none) → (∀ p ∈ ps, p.2.nv.parent' ≠ p.1) →
      wtxHeap (GF := GF) tx dq X ∗ ([∗list] p ∈ ps, objOwn X.v p.1 dq true (.node bl p.2)) ⊢
        wtxHeap tx dq (splitX X bl B [] ps) := by
  induction ps with
  | nil =>
    intro X bl B hb _ _ _
    have e : splitX X bl B [] [] = X.setBkt bl B := rfl
    iintro ⟨H, -⟩
    rw [e]
    have e2 : X.setBkt bl B = X := by
      unfold WX.setBkt
      have : X.t.bs.insert bl B = X.t.bs := GMap.map_eq fun k => by
        by_cases h : bl = k
        · subst h; rw [GMap.lookup_insert, hb]
        · rw [GMap.lookup_insert_ne _ _ h]
      rw [this]
    rw [e2]; iexact H
  | cons q ps ih =>
    intro X bl B hb hnd hf hp
    simp only [List.map_cons, List.nodup_cons] at hnd
    iintro ⟨H, Hq, Hps⟩
    ihave %Hok := wtxHeap_heapOK tx dq X $$ H
    have hq := hf q (List.mem_cons_self ..)
    ihave H := Write.wtxHeap_node_insert tx dq X bl q.1 B q.2 hb hq (hp q (List.mem_cons_self ..))
      $$ [H Hq]
    · iframe
    have hobjs : (X.addNode bl q.1 B q.2).t.objs = X.t.objs.insert q.1 (.node bl q.2) :=
      Write.objs_setNodeT_fresh X.t bl q.1 B q.2 Hok.2.1 hb hq
    have hb' : (X.addNode bl q.1 B q.2).t.bs !! bl = some { B with ns := B.ns.insert q.1 q.2 } :=
      GMap.lookup_insert _ _ _
    have hf' : ∀ p ∈ ps, (X.addNode bl q.1 B q.2).t.objs !! p.1 = none := by
      intro p hpm
      rw [hobjs, GMap.lookup_insert_ne _ _ (fun e => hnd.1 (List.mem_map.2 ⟨p, hpm, e.symm⟩))]
      exact hf p (List.mem_cons_of_mem _ hpm)
    have e : splitX (X.addNode bl q.1 B q.2) bl { B with ns := B.ns.insert q.1 q.2 } [] ps =
        splitX X bl B [] (q :: ps) := by
      unfold splitX WX.addNode
      simp only [GMap.insert_insert]
      rfl
    rw [← e]
    iapply ih _ bl _ hb' hnd.2 hf' (fun p hpm => hp p (List.mem_cons_of_mem _ hpm))
    iframe

omit hos in
/-- A node's points-to is none of a list of points-tos'. -/
theorem ptsL_notin {β : Type} (Q : Loc × node × β → IProp GF) (xs : List (Loc × node × β))
    (l : Loc) (v : node) :
    (l ↦ v : IProp GF) ∗ ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x) ⊢
      ⌜l ∉ xs.map (·.1)⌝ ∗ l ↦ v ∗ [∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x := by
  by_cases hm : l ∈ xs.map (·.1)
  · obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hz
    subst e
    iintro ⟨Hl, Hxs⟩
    icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hxs with ⟨⟨Hz, -⟩, -⟩
    iexfalso
    iapply Write.node_pointsto_excl z.1 z.2.1 v
    iframe
  · iintro ⟨Hl, Hxs⟩
    iframe
    ipureintro; exact hm

omit hos in
/-- The nodes of a list of points-tos are distinct. -/
theorem ptsL_nodup {β : Type} (Q : Loc × node × β → IProp GF) (xs : List (Loc × node × β)) :
    ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x) ⊢
      ⌜(xs.map (·.1)).Nodup⌝ ∗ [∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x := by
  induction xs with
  | nil => iintro H; iframe; ipureintro; exact List.nodup_nil
  | cons y xs ih =>
    iintro ⟨⟨Hy, Qy⟩, Hxs⟩
    icases ih $$ Hxs with ⟨%Hnd, Hxs⟩
    icases ptsL_notin Q xs y.1 y.2.1 $$ [Hy Hxs] with ⟨%Hno, Hy, Hxs⟩
    · iframe
    iframe
    ipureintro
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨Hno, Hnd⟩

omit hos in
/-- **The nodes of a list of points-tos are no node objects** of the heap. -/
theorem wtxHeap_freshL {β : Type} (Q : Loc × node × β → IProp GF) (tx : Loc) (X : WX)
    (xs : List (Loc × node × β)) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ∗ ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x) ⊢
      ⌜∀ x ∈ xs, X.t.objs !! x.1 = none⌝ ∗ wtxHeap tx (DFrac.own 1) X ∗
        [∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ Q x := by
  induction xs with
  | nil => iintro ⟨H, Hl⟩; iframe; ipureintro; intro x hx; cases hx
  | cons y xs ih =>
    iintro ⟨H, ⟨Hy, Qy⟩, Hxs⟩
    icases ih $$ [H Hxs] with ⟨%Hf, H, Hxs⟩
    · iframe
    icases Write.wtxHeap_fresh tx X y.1 y.2.1 $$ [H Hy] with ⟨H, Hy, %Hy⟩
    · iframe
    iframe
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Hy
    · exact Hf x hx

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
