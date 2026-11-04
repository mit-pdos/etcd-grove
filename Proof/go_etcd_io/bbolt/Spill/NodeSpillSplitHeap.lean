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

omit hos in
/-- Nodes given as objects are no node objects of the heap. -/
theorem wtxHeap_freshObjs (tx : Loc) (Y : WX) (bl : Loc) (v : View) (ps : List (Loc × NRec)) :
    wtxHeap (GF := GF) tx (DFrac.own 1) Y ∗
      ([∗list] p ∈ ps, objOwn v p.1 (DFrac.own 1) true (.node bl p.2)) ⊢
      ⌜∀ p ∈ ps, Y.t.objs !! p.1 = none⌝ ∗ wtxHeap tx (DFrac.own 1) Y ∗
        [∗list] p ∈ ps, objOwn v p.1 (DFrac.own 1) true (.node bl p.2) := by
  induction ps with
  | nil => iintro ⟨H, Hl⟩; iframe; ipureintro; intro x hx; cases hx
  | cons y ps ih =>
    iintro ⟨H, Hy, Hps⟩
    icases ih $$ [H Hps] with ⟨%Hf, H, Hps⟩
    · iframe
    icases objOwn_node_ptr_acc v y.1 (DFrac.own 1) true bl y.2 $$ Hy with ⟨Hp, Hyb⟩
    icases Write.wtxHeap_fresh tx Y y.1 y.2.nv $$ [H Hp] with ⟨H, Hp, %Hy⟩
    · iframe
    ihave Hy := Hyb $$ Hp
    iframe
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Hy
    · exact Hf x hx

/-- **The split's records into bucket `bl`** (record `B`): its nodes `Ls` (records `f`) and its
object out; back with new records `psOld` at `Ls` and fresh nodes `psNew` (no node its own parent),
to `splitX`, the fresh nodes no node objects before. -/
theorem wtxHeap_splitX (tx : Loc) (X : WX) (bl : Loc) (B : BRec) (Ls : List Loc) (f : Loc → NRec)
    (hb : X.t.bs !! bl = some B) (hnd : Ls.Nodup) (hf : ∀ l ∈ Ls, B.ns !! l = some (f l)) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ⊢
      ([∗list] l ∈ Ls, objOwn X.v l (DFrac.own 1) (decide (l ∈ X.live)) (.node bl (f l))) ∗
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      txFields tx (DFrac.own 1) X ∗ rootFill tx (DFrac.own 1) ∗
      (∀ (psOld psNew : List (Loc × NRec)), ⌜psOld.map (·.1) = Ls ∧
          ((psOld ++ psNew).map (·.1)).Nodup ∧ (∀ p ∈ psOld ++ psNew, p.2.nv.parent' ≠ p.1)⌝ -∗
        ([∗list] p ∈ psOld, objOwn X.v p.1 (DFrac.own 1) (decide (p.1 ∈ X.live)) (.node bl p.2)) -∗
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗
        txFields tx (DFrac.own 1) X -∗ rootFill tx (DFrac.own 1) -∗
        ([∗list] p ∈ psNew, objOwn X.v p.1 (DFrac.own 1) true (.node bl p.2)) -∗
        ⌜∀ p ∈ psNew, X.t.objs !! p.1 = none⌝ ∗ wtxHeap tx (DFrac.own 1) (splitX X bl B psOld psNew)) := by
  iintro H
  icases wtxHeap_setBkt_acc tx (DFrac.own 1) X bl B Ls f hb hnd hf $$ H
    with ⟨HL, Hb, Hf, Hrf, Hback⟩
  iframe HL Hb Hf Hrf
  iintro %psOld %psNew %Hc HO Hb Hf Hrf HN
  obtain ⟨hL, hnd2, hpo⟩ := Hc
  have hndO : (psOld.map (·.1)).Nodup := by
    rw [List.map_append] at hnd2; exact (List.nodup_append.1 hnd2).1
  have hndN : (psNew.map (·.1)).Nodup := by
    rw [List.map_append] at hnd2; exact (List.nodup_append.1 hnd2).2.1
  let B1 : BRec := { B with ns := nsIns B.ns psOld }
  let f' : Loc → NRec := fun l => (nsIns B.ns psOld !! l).getD (f l)
  have hf'p : ∀ p ∈ psOld, f' p.1 = p.2 := by
    intro p hp; simp only [f']; rw [nsIns_in _ _ hndO p hp]; rfl
  ihave H1 := Hback $$ %B1 %f' [] [HO] [Hb] [Hf] [Hrf]
  · ipureintro
    refine ⟨?_, ?_, rfl, ?_⟩
    · intro l hl
      rw [← hL] at hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hf'p p hp]; exact nsIns_in _ _ hndO p hp
    · intro l hl
      exact nsIns_out _ _ _ (by rw [hL]; exact hl)
    · intro l hl
      rw [← hL] at hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hf'p p hp]; exact hpo p (List.mem_append_left _ hp)
  · rw [← hL]
    rw [BigSepL.bigSepL_map (fun p : Loc × NRec => p.1)]
    iapply (BigSepL.bigSepL_mono ?_) $$ HO
    intro k p hk
    rw [hf'p p (List.mem_of_getElem? hk)]
  · rw [show objOwn (GF := GF) X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B1) =
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) from objOwn_bkt_ns _ _ _ _ B _]
    iexact Hb
  · iexact Hf
  · iexact Hrf
  icases wtxHeap_freshObjs tx (X.setBkt bl B1) bl X.v psNew $$ [H1 HN] with ⟨%Hfr, H1, HN⟩
  · iframe
  have hb1 : (X.setBkt bl B1).t.bs !! bl = some B1 := GMap.lookup_insert _ _ _
  have e : splitX (X.setBkt bl B1) bl B1 [] psNew = splitX X bl B psOld psNew := by
    unfold splitX WX.setBkt
    simp only [GMap.insert_insert, List.nil_append, B1, nsIns_append]
  have e0 : splitX X bl B psOld [] = X.setBkt bl B1 := by
    unfold splitX WX.setBkt
    simp only [List.append_nil, B1]
    rfl
  have hgrow : ∀ l, (X.t.objs !! l).isSome → ((X.setBkt bl B1).t.objs !! l).isSome := by
    rw [← e0]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg, -⟩ :=
      splitX_frame (psOld := psOld) (psNew := []) hb (psOld.map (·.1))
        (fun p hp => List.mem_map.2 ⟨p, by simpa using hp, rfl⟩) (fun p hp => by cases hp)
    exact hg
  isplitl []
  · ipureintro
    intro p hp
    have h := Hfr p hp
    cases hx : X.t.objs !! p.1 with
    | none => rfl
    | some o =>
      have := hgrow p.1 (by rw [hx]; rfl)
      rw [h] at this; cases this
  rw [← e]
  iapply wtxHeap_putNew tx (DFrac.own 1) psNew (X.setBkt bl B1) bl B1 hb1 hndN Hfr
    (fun p hp => hpo p (List.mem_append_right _ hp))
  iframe

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
