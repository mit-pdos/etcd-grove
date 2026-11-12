/-
`node.spill` after its children's loop (U9z2, `notes/bbolt-proof-plan.md`; pure): **the frame of a
piece's step** (`pcStepX_frame'`): the piece and its parent touched. Built from the frames of a
node's record set (`spFrame_setNode'`), of `dereference` (`spFrame_deref`), of a remap's re-base
(`spFrame_rebase`), of an allocation's new buffer (`spFrame_addPage`), of `allocate`
(`spFrame_allocRes`) and of the written buffer (`spFrame_setBuf`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneFrame
public import Proof.go_etcd_io.bbolt.Spill.DerefRel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section frame
variable [GooseExts] [GoGlobalContext]

theorem optRel_mono' {α β : Type} {R S : α → β → Prop} {o1 : Option α} {o2 : Option β}
    (h : optRel R o1 o2) (hRS : ∀ a b, R a b → S a b) : optRel S o1 o2 := by
  cases o1 <;> cases o2 <;> simp only [optRel] at h ⊢
  exact hRS _ _ h

/-- **The frame of a node's record set**: only the node touched. -/
theorem spFrame_setNode' (X : WX) (bl l : Loc) (r' : NRec) :
    spFrame X (X.setNode bl l r') bl [l] := by
  cases hB : X.t.bs !! bl with
  | none =>
    have e : X.setNode bl l r' = X := by unfold WX.setNode; rw [hB]
    rw [e]; exact spFrame_refl _ _ _
  | some B =>
    have e : X.setNode bl l r' =
        { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := B.ns.insert l r' } } } := by
      unfold WX.setNode WX.setBkt; rw [hB]
    rw [e]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, meta_with_pgid_self _, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
      ?_, ?_, ?_, fun _ _ _ _ _ _ => Iff.rfl, ?_, ?_⟩
    · intro bl' hne B0 hB0
      refine ⟨B0, ?_, bktSim_refl B0, fun _ => optRel_nodeSim_refl _⟩
      show (X.t.bs.insert bl _) !! bl' = some B0
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hB0
    · intro bl' hne h0
      show (X.t.bs.insert bl _) !! bl' = none
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h0
    · intro B0 hB0
      rw [hB] at hB0; cases hB0
      refine ⟨_, GMap.lookup_insert _ _ _, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun l' hl' => ?_⟩
      have hne : l ≠ l' := fun e => hl' (by rw [e]; exact List.mem_singleton_self _)
      simp only
      rw [GMap.lookup_insert_ne _ _ hne]
      exact optRel_nodeSim_refl _
    · intro y hy
      rw [objs_isSome_iff] at hy ⊢
      rcases hy with hy | ⟨bl', B', hB', hy⟩
      · exact Or.inl hy
      · refine Or.inr ?_
        by_cases hb : bl = bl'
        · subst hb
          rw [hB] at hB'; cases hB'
          refine ⟨bl, _, GMap.lookup_insert _ _ _, ?_⟩
          simp only
          by_cases e2 : l = y
          · subst e2; rw [GMap.lookup_insert]; rfl
          · rw [GMap.lookup_insert_ne _ _ e2]; exact hy
        · refine ⟨bl', B', ?_, hy⟩
          show (X.t.bs.insert bl _) !! bl' = some B'
          rw [GMap.lookup_insert_ne _ _ hb]; exact hB'
    · intro bl' B0 B' l' r r2 hB0 hB' hr hr' hT _ hv
      change (X.t.bs.insert bl _) !! bl' = some B' at hB'
      by_cases hb : bl = bl'
      · subst hb
        rw [hB] at hB0; cases hB0
        have hne : l ≠ l' := fun e => hT rfl (by rw [e]; exact List.mem_singleton_self _)
        rw [GMap.lookup_insert] at hB'; cases hB'
        simp only at hr'
        rw [GMap.lookup_insert_ne _ _ hne, hr] at hr'; cases hr'; exact hv
      · rw [GMap.lookup_insert_ne _ _ hb, hB0] at hB'; cases hB'
        rw [hr] at hr'; cases hr'; exact hv

/-- **The frame of `dereference`** (some nodes' sources copied). -/
theorem spFrame_deref {X X' : WX} (h : derefStep X X') (hd : objsDisj X.t) (bl : Loc)
    (T : List Loc) : spFrame X X' bl T := by
  have h0 := h
  obtain ⟨hv, hlv, hhd, hnl, hrl, htt, hmv, hpm, hbf, -, -, hlb, hbs⟩ := h0
  have hBk : ∀ bl' B, X.t.bs !! bl' = some B → ∃ B', X'.t.bs !! bl' = some B' ∧ bktSim B B' ∧
      ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l) := by
    intro bl' B hB
    obtain ⟨B', hB', hs⟩ := optRel_some_l (hB ▸ hbs bl')
    have e := hs.1
    have e1 := congrArg BRec.bv e; have e2 := congrArg BRec.ib e
    have e3 := congrArg BRec.nm e; have e4 := congrArg BRec.bm e
    have e5 := congrArg BRec.ipg e
    exact ⟨B', hB', ⟨e1, e2, e3, e4, e5⟩,
      fun l => optRel_mono' (hs.2 l) fun _ _ hn => nodeStep_nodeSim hn⟩
  refine ⟨hrl, hhd, hnl, hlb, by rw [hv], by rw [hv], htt, meta_with_pgid_of_eq hmv, by rw [hmv]; exact Nat.le_refl _,
    fun _ _ hk => by rw [hbf]; exact hk, fun _ _ hk => by rw [hpm]; exact hk,
    fun bl' _ B hB => hBk bl' B hB, fun bl' _ h0 => optRel_none_l (h0 ▸ hbs bl'), ?_,
    fun _ _ _ _ _ _ => by rw [hlv], fun y hy => by rw [objs_isSome_step h hd y]; exact hy, ?_⟩
  · intro B hB
    obtain ⟨B', h1, h2, h3⟩ := hBk bl B hB
    exact ⟨B', h1, h2, fun l _ => h3 l⟩
  · intro bl' B B' l r r' hB hB' hr hr' _ _ hvs
    obtain ⟨B2, hB2, hs⟩ := optRel_some_l (hB ▸ hbs bl')
    rw [hB'] at hB2; cases hB2
    obtain ⟨r2, hr2, hns⟩ := optRel_some_l (hr ▸ hs.2 l)
    rw [hr'] at hr2; cases hr2
    rcases hns with rfl | hdr
    · exact hvs
    · intro _ w hw _
      exact Or.inr (hdr.2.2.2.1 w hw).2

/-- **The frame of a remap's re-base** (no live view source, `derefOK`). -/
theorem spFrame_rebase {X : WX} (b : Loc) (hd : objsDisj X.t) (hc : derefOK X) (bl : Loc)
    (T : List Loc) : spFrame X (X.rebase b) bl T := by
  have hBk : ∀ bl' B, X.t.bs !! bl' = some B → ∃ B', (X.rebase b).t.bs !! bl' = some B' ∧
      bktSim B B' ∧ ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l) := by
    intro bl' B hB
    refine ⟨B.unview, by rw [rebase_bs, hB]; rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun l => ?_⟩
    rw [unview_ns]
    cases B.ns !! l with
    | none => trivial
    | some r => exact unview_nodeSim r
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, meta_with_pgid_self _, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
    fun bl' _ B hB => hBk bl' B hB, fun bl' _ h0 => by rw [rebase_bs, h0]; rfl, ?_,
    fun _ _ _ _ _ _ => Iff.rfl, ?_, ?_⟩
  · intro B hB
    obtain ⟨B', h1, h2, h3⟩ := hBk bl B hB
    exact ⟨B', h1, h2, fun l _ => h3 l⟩
  · intro y hy
    rw [objs_isSome_iff] at hy ⊢
    rcases hy with hy | ⟨bl', B, hB, hy⟩
    · left
      show (X.t.dead.fmap _ !! y).isSome
      rw [GMap.lookup_fmap]; simpa using hy
    · right
      exact ⟨bl', B.unview, by rw [rebase_bs, hB]; rfl, by rw [unview_ns]; simpa using hy⟩
  · intro bl' B B' l r r' hB hB' hr hr' _ hl hv
    rw [rebase_bs, hB, Option.map_some] at hB'; cases hB'
    rw [unview_ns, hr, Option.map_some] at hr'; cases hr'
    have hv0 := hc l _ (objs_node X.t bl' B l r hd hB hr) hl
    simp only at hv0
    intro hleaf w hw hbk
    simp only [NRec.unview, List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    rcases hv hleaf w0 hw0 hbk with h1 | h1
    · exact absurd h1 (hv0.1 w0 hw0).2
    · right; show w0.vs.unview = _; rw [h1]; rfl

/-- **The frame of an allocation's new buffer** (at an id with no buffer). -/
theorem spFrame_addPage {X : WX} {id : w64} {p : Loc} {count : Nat} {hwm : w64}
    (hb : X.t.bufs !! id = none) (hp : X.t.pm !! id = none)
    (hh : X.t.mv.pgid'.toNat ≤ hwm.toNat) (bl : Loc) (T : List Loc) :
    spFrame X (X.addPage id p count hwm) bl T := by
  obtain ⟨a, b, c, d, e, f, g, -, -, -, -, m, n, o, q, r, z⟩ := spFrame_refl X bl T
  refine ⟨a, b, c, d, e, f, g, rfl, hh, ?_, ?_, m, n, o, q, r, z⟩
  · intro k bs hk
    show (X.t.bufs.insert id _) !! k = _
    rw [GMap.lookup_insert_ne _ _ (fun he => by subst he; rw [hb] at hk; cases hk)]; exact hk
  · intro k q' hk
    show (X.t.pm.insert id _) !! k = _
    rw [GMap.lookup_insert_ne _ _ (fun he => by subst he; rw [hp] at hk; cases hk)]; exact hk

/-- **The frame of `allocate`** (at an id with no buffer): no node touched. -/
theorem spFrame_allocRes {X X' : WX} {fl fl' : FLPg} {txid : w64} {count : Nat} {p : Loc}
    {id : w64} (h : allocRes X X' fl fl' txid count p id) (hd : objsDisj X.t)
    (hb : X.t.bufs !! id = none) (hp : X.t.pm !! id = none) (bl : Loc) (T : List Loc) :
    spFrame X X' bl T := by
  obtain ⟨-, -, Xr, hXr, hX'⟩ := h
  have hTT : ∀ l ∈ T ++ T, l ∈ T := fun l hl => (List.mem_append.1 hl).elim (fun h => h) (fun h => h)
  have hR : spFrame X Xr bl T ∧ Xr.t.bufs = X.t.bufs ∧ Xr.t.pm = X.t.pm ∧ Xr.t.mv = X.t.mv := by
    rcases hXr with rfl | ⟨Xd, b, hdr, rfl⟩
    · exact ⟨spFrame_refl _ _ _, rfl, rfl, rfl⟩
    · have hs := hdr.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact ⟨spFrame_mono (spFrame_trans (spFrame_deref hs hd bl T)
        (spFrame_rebase b (objsDisj_step hs hd) hdr.1 bl T)) hTT,
        hdr.2.2.2.2.2.2.2.2.1, hdr.2.2.2.2.2.2.2.1, hdr.2.2.2.2.2.2.1⟩
  obtain ⟨F, hbf, hpm, hmv⟩ := hR
  have hb' : Xr.t.bufs !! id = none := by rw [hbf]; exact hb
  have hp' : Xr.t.pm !! id = none := by rw [hpm]; exact hp
  rcases hX' with ⟨-, -, rfl⟩ | ⟨hid, -, hlt, rfl⟩
  · exact spFrame_mono (spFrame_trans F (spFrame_addPage hb' hp' (by rw [hmv]; exact Nat.le_refl _) bl T)) hTT
  · have e : (id + W64 (count : Int)).toNat = id.toNat + count := by word
    exact spFrame_mono (spFrame_trans F (spFrame_addPage hb' hp'
      (by rw [hmv, e, ← hid]; omega) bl T)) hTT

/-- **The frame of a buffer's write** at an id that had no buffer at the frame's start. -/
theorem spFrame_setBuf {X Y : WX} {bl : Loc} {T : List Loc} {id : w64} {pg : List w8}
    (h : spFrame X Y bl T) (hb : X.t.bufs !! id = none) : spFrame X (Y.setBuf id pg) bl T := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, q, r, z⟩ := h
  refine ⟨a, b, c, d, e, f, g, i, j, ?_, l, m, n, o, q, r, z⟩
  intro k' bs hk
  show (Y.t.bufs.insert id pg) !! k' = _
  rw [GMap.lookup_insert_ne _ _ (fun he => by subst he; rw [hb] at hk; cases hk)]
  exact k k' bs hk

/-- **The frame of a piece's step**: the piece and its parent touched. -/
theorem pcStepX_frame' {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hd : objsDisj Xi.t)
    (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hfl : ∀ y ∈ wi.fl.free, y.toNat < Xi.t.mv.pgid'.toNat) :
    spFrame Xi X3 bl [l, rl.nv.parent'] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbn⟩ := pcStepX_state hs hn hpl hG1 hfl
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, -, hal, -, -, -, -, -, -, -, rfl⟩ := hs
  have hG := hG1 X1 w1 stf hfr
  obtain ⟨-, hbf, hpm, -⟩ := pcFreed_basic hfr
  have hF1 : spFrame Xi X1 bl [l] ∧ objsDisj X1.t := by
    rcases hfr with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
    · exact ⟨spFrame_refl _ _ _, hd⟩
    · exact ⟨spFrame_setNode' _ _ _ _, objsDisj_setNode hd hn _⟩
  have hb1 : X1.t.bufs !! id = none := by rw [hbf]; exact hbn
  have hp1 : X1.t.pm !! id = none := by
    cases e : X1.t.pm !! id with
    | none => rfl
    | some _ =>
      have := (hG.2.2.2.2.2.1 id).1 (by rw [e]; rfl)
      rw [hb1] at this; cases this
  have F2 := spFrame_allocRes hal hF1.2 hb1 hp1 bl []
  unfold pcFin
  apply spFrame_setBuf _ hbn
  have F12 := spFrame_trans hF1.1 F2
  by_cases hp : rl.nv.parent' ≠ null
  · rw [if_pos (by simpa using hp)]
    exact spFrame_mono (spFrame_trans F12 (spFrame_trans (spFrame_setNode' X2 bl l _)
      (spFrame_setNode' _ bl rl.nv.parent' _))) (by intro y hy; simp at hy ⊢; grind)
  · rw [if_neg (by simpa using hp)]
    exact spFrame_mono (spFrame_trans F12 (spFrame_setNode' X2 bl l _))
      (by intro y hy; simp at hy ⊢; grind)

end frame

end Spill

end bbolt
end EtcdGrove
end Perennial
