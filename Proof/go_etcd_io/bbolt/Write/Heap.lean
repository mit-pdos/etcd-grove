/-
U7's (`notes/bbolt-proof-plan.md`) heap facts: every bucket's node is an object
(`objs_isSome_node`, without `objsDisj`), and a fresh node joins the heap
(`wtxHeap_node_insert`, `Inv/WtxHeap`'s `wtxHeap_node_insert`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.Heap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section objs
variable [GooseExts]

private theorem foldl_ins_mono (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) (k : Loc)
    (h : (m !! k).isSome) :
    ((L.foldl (fun m' lr => m'.insert lr.1 (WObj.node bl lr.2)) m) !! k).isSome := by
  induction L generalizing m with
  | nil => exact h
  | cons a L ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases hk : a.1 = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk]; exact h

private theorem foldl_ins_in (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) (k : Loc)
    (h : k ∈ L.map Prod.fst) :
    ((L.foldl (fun m' lr => m'.insert lr.1 (WObj.node bl lr.2)) m) !! k).isSome := by
  induction L generalizing m with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with h | h
    · apply foldl_ins_mono; rw [← h]; simp
    · exact ih _ h

private def step (m : GMap Loc WObj) (bB : Loc × BRec) : GMap Loc WObj :=
  bB.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (.node bB.1 lr.2)) m

private theorem step_mono (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc)
    (h : (m !! k).isSome) : ((L.foldl step m) !! k).isSome := by
  induction L generalizing m with
  | nil => exact h
  | cons a L ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold step
    exact foldl_ins_mono _ _ _ _ h

private theorem step_in (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc)
    (h : ∃ bB ∈ L, (bB.2.ns !! k).isSome) : ((L.foldl step m) !! k).isSome := by
  induction L generalizing m with
  | nil => obtain ⟨_, h, _⟩ := h; simp at h
  | cons a L ih =>
    simp only [List.foldl_cons]
    obtain ⟨bB, hm, hk⟩ := h
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      apply step_mono
      unfold step
      apply foldl_ins_in
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hk
      exact List.mem_map.2 ⟨(k, r), (GMap.mem_toList _ _ _).2 hr, rfl⟩
    · exact ih _ ⟨bB, hm, hk⟩

private theorem objs_eq' (T : WTx) : T.objs = T.bs.toList.foldl step T.deadObjs := rfl

/-- Every bucket's node is an object. -/
theorem objs_isSome_node (T : WTx) (bl : Loc) (B : BRec) (n : Loc) (hb : T.bs !! bl = some B)
    (hn : (B.ns !! n).isSome) : (T.objs !! n).isSome := by
  rw [objs_eq']
  exact step_in _ _ _ ⟨(bl, B), (GMap.mem_toList _ _ _).2 hb, hn⟩

/-- A location no node object has is no bucket's node. -/
theorem objs_none (T : WTx) (l : Loc) (hl : T.objs !! l = none) :
    ∀ bl B, T.bs !! bl = some B → B.ns !! l = none := by
  intro bl B hb
  cases h : B.ns !! l with
  | none => rfl
  | some r =>
    have := objs_isSome_node T bl B l hb (by simp [h]); rw [hl] at this; cases this

theorem objsDisj_setNodeT_fresh (T : WTx) (bl n : Loc) (B : BRec) (r' : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hn : T.objs !! n = none) :
    objsDisj (T.setNodeT bl n B r') := by
  have hnn := objs_none T n hn
  intro c C hc k hk c' C' hc' hne
  by_cases hcb : c = bl
  · subst hcb
    simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
    subst hc
    simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hne)] at hc'
    by_cases hkn : k = n
    · subst hkn
      exact hnn c' C' hc'
    · simp only [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at hk
      exact hd c B hb k hk c' C' hc' hne
  · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
    have hkn : k ≠ n := by intro h; subst h; rw [hnn c C hc] at hk; cases hk
    by_cases hc'b : c' = bl
    · subst hc'b
      simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc'
      subst hc'
      simp only [GMap.lookup_insert_ne _ _ (Ne.symm hkn)]
      exact hd c C hc k hk c' B hb hne
    · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hc'b)] at hc'
      exact hd c C hc k hk c' C' hc' hne

/-- **The nodes after a fresh node joins bucket `bl`**: the node's record added. -/
theorem objs_setNodeT_fresh (T : WTx) (bl n : Loc) (B : BRec) (r' : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hn : T.objs !! n = none) :
    (T.setNodeT bl n B r').objs = T.objs.insert n (.node bl r') := by
  have hd' := objsDisj_setNodeT_fresh T bl n B r' hd hb hn
  have hnn := objs_none T n hn
  apply GMap.map_eq
  intro k
  by_cases hk2 : k = n
  · subst hk2
    rw [GMap.lookup_insert]
    exact objs_node _ bl { B with ns := B.ns.insert k r' } k r' hd' (by simp [WTx.setNodeT])
      (by simp)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
  by_cases hkn : ∃ c C rk, T.bs !! c = some C ∧ C.ns !! k = some rk
  · obtain ⟨c, C, rk, hC, hrk⟩ := hkn
    rw [objs_node T c C k rk hd hC hrk]
    by_cases hcb : c = bl
    · subst hcb
      rw [hb] at hC; cases hC
      exact objs_node _ c { B with ns := B.ns.insert n r' } k rk hd' (by simp [WTx.setNodeT])
        (by simp [Ne.symm hk2, hrk])
    · exact objs_node _ c C k rk hd'
        (by simp [WTx.setNodeT, Ne.symm hcb, hC]) hrk
  · have hno : ∀ c C, T.bs !! c = some C → C.ns !! k = none := by
      intro c C hC
      cases h : C.ns !! k with
      | none => rfl
      | some rk => exact absurd ⟨c, C, rk, hC, h⟩ hkn
    have hno' : ∀ c C, (T.setNodeT bl n B r').bs !! c = some C → C.ns !! k = none := by
      intro c C hC
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hC
        subst hC
        simp [Ne.symm hk2, hno c B hb]
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hC
        exact hno c C hC
    rw [objs_other T k hno, objs_other _ k hno']
    rfl

end objs

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A fresh node into the heap** (`Inv/WtxHeap`'s `wtxHeap_node_insert`): fresh among the node
objects (batch 14: a bucket may be at the same location as far as the heap can tell). -/
theorem wtxHeap_node_insert (tx : Loc) (dq : DFrac) (X : WX) (bl l : Loc) (B : BRec) (r : NRec)
    (hb : X.t.bs !! bl = some B) (hl : X.t.objs !! l = none) (hp : r.nv.parent' ≠ l) :
    wtxHeap (GF := GF) tx dq X ∗ objOwn X.v l dq true (.node bl r) ⊢
      wtxHeap tx dq (X.addNode bl l B r) := by
  have heq : X.addNode bl l B r = { X with t := X.t.setNodeT bl l B r, live := X.live.insert l () } :=
    rfl
  rw [heq]
  unfold wtxHeap
  iintro ⟨⟨%Hok, Hf, Hrf, Hm, Hbk⟩, Hl⟩
  have Hd := Hok.2.1
  have hln := objs_none X.t l hl
  isplitr
  · ipureintro
    refine ⟨Hok.1, objsDisj_setNodeT_fresh X.t bl l B r Hd hb hl, ?_, ?_, ?_, ?_⟩
    · intro c C hc
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc; exact Hok.2.2.1 c B hb
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.1 c C hc
    · intro c C k rk hc hk
      by_cases hcb : c = bl
      · subst hcb
        simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
        subst hc
        by_cases hkn : k = l
        · subst hkn
          simp only [GMap.lookup_insert, Option.some.injEq] at hk
          subst hk; exact hp
        · simp only [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at hk
          exact Hok.2.2.2.1 c B k rk hb hk
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.2.1 c C k rk hc hk
    · intro m y hm
      show ((X.t.setNodeT bl l B r).objs !! m).isSome
      rw [objs_setNodeT_fresh X.t bl l B r Hd hb hl]
      exact isSome_insert_of _ _ _ _ (Hok.2.2.2.2.1 m y hm)
    · intro c C hc
      by_cases hcb : c = bl
      · subst hcb; exact Hok.2.2.2.2.2 c B hb
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
        exact Hok.2.2.2.2.2 c C hc
  isplitl [Hf]
  · unfold txFields; simp only [WTx.setNodeT]; iexact Hf
  iframe
  rw [objs_setNodeT_fresh X.t bl l B r Hd hb hl, bobjs_setNodeT X.t bl l B r]
  dsimp only
  isplitl [Hl Hm]
  · iapply (BigSepM.bigSepM_insert (M := GMap Loc) hl).2
    isplitl [Hl]
    · simp only [GMap.mem_iff, GMap.lookup_insert, Option.isSome_some, _root_.decide_true]
      iexact Hl
    iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hm
    intro k o hk
    have hkl : k ≠ l := by
      intro h; subst h
      rw [show Std.get? X.t.objs k = X.t.objs !! k from rfl, hl] at hk; cases hk
    have : decide (k ∈ X.live.insert l ()) = decide (k ∈ X.live) := by
      simp [GMap.mem_iff, Ne.symm hkl]
    rw [this]
  iapply (bigSepM_insert_same (Φ := fun k B => objOwn (GF := GF) X.v k dq
    (decide (k ∈ X.liveB)) (.bkt B)) _ bl B { B with ns := B.ns.insert l r }
    (bobjs_bkt X.t bl B hb) (by simp only [objOwn, pageOwn])).2
  iexact Hbk

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
