/-
`node.spill`'s children's loop (U9h, `notes/bbolt-proof-plan.md`; pure): its invariant `spLoop`
(the branch `n` at iteration `i`: its branch facts `uBr`, the children before `i` spilled, the
slots and freeable pages, and the step, frame and slots relative to the start of `n`'s spill),
established at the start (`spLoop_init`), kept by a spilled child's spill (`spLoop_spilled`)
and by an unspilled child's (`spLoop_child`, over `ChildStep.uBr_childStep`), with the child's
pre (`spLoop_childPre`), an error's post (`spLoop_err`), and every entry finished after the loop
(`spLoop_fin`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Spill.SpErr
public import Proof.go_etcd_io.bbolt.Spill.ChildStep
public import Proof.go_etcd_io.bbolt.Spill.UTreeBnd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section loop
variable [GooseExts]

/-- **The children's loop's state** of `n`'s spill from `(X, w)` (record `r`, its frame `O`, its
slots `D0` and nodes `N0`), at iteration `i`, `(X', w')` after the steps `st`, `n`'s record `r'`
over the entries `es`, the fresh nodes `T` touched. -/
structure spLoop (X : WX) (w : WDb) (bl n : Loc) (r : NRec) (O : List Nat)
    (lo hi : Option (List w8)) (h : Nat) (D0 : List Nat) (N0 : List Loc) (E0 : List El)
    (X' : WX) (w' : WDb) (r' : NRec) (es : List UE) (i : Nat) (st : List FLStep) (T : List Loc) :
    Prop where
  br : uBr X' bl (spP X') X'.t.mv.pgid'.toNat n r' lo hi h es
  ile : i ≤ r'.cs.length
  done : ∀ k c, k < i → r'.cs[k]? = some c → spilledN X' bl c
  slot : slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ (ownSl X'.v r'.nv.pgid' ++ es.flatMap UE.D))
  free : spFree X' w'.fl w.wtxid (ownF r'.nv.pgid' ++ es.flatMap UE.F)
  step : spStep X X' w w' O st
  frame : spFrame X X' bl (N0 ++ T)
  fresh : ∀ l ∈ T, X.t.objs !! l = none
  EE : es.flatMap UE.E = E0
  nN : n ∈ N0
  NN : ∀ l ∈ es.flatMap UE.N, l ∈ N0
  Dk : ∀ s ∈ D0, s ∈ ownSl X'.v r'.nv.pgid' ++ es.flatMap UE.D ∨ s ∈ pendSlots w'.fl
  Dn : ∀ s ∈ ownSl X'.v r'.nv.pgid' ++ es.flatMap UE.D, s ∈ D0 ∨
    newSlot st X.t.mv.pgid'.toNat s
  Pd : ∀ x, spP X' !! x ≠ spP X !! x → x ∉ D0
  nv : r'.nv = { r.nv with inodes' := r'.nv.inodes', children' := r'.nv.children',
                           key' := r'.nv.key' }
  knil : r'.nv.key' = slice.nil ↔ r.nv.key' = slice.nil
  key : r'.key = r.key
  cap : r'.capOwn = r.capOwn
  live : n ∈ X'.live
  /-- (U9m) `n`'s children are its children at the start or nodes the loop made (its children's
  pieces): what `spEnd`'s last clause needs. -/
  chs : ∀ c ∈ r'.cs, c ∈ r.cs ∨ c ∈ T
  /-- (U9w3) The bucket's parent pointers (`spG_nilCh`'s premises after the loop). -/
  par : parOK X' bl

/-! ## Lists -/

theorem flatMap_split {α β : Type} {es : List α} {j : Nat} {e : α} (f : α → List β)
    (hj : es[j]? = some e) :
    es.flatMap f = (es.take j).flatMap f ++ f e ++ (es.drop (j + 1)).flatMap f := by
  have hlt : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  have he : es[j] = e := (List.getElem?_eq_some_iff.1 hj).2
  have hd : es.drop j = e :: es.drop (j + 1) := by rw [List.drop_eq_getElem_cons hlt, he]
  have := congrArg (List.flatMap f) (List.take_append_drop j es)
  rw [← this, List.flatMap_append, hd, List.flatMap_cons, List.append_assoc]

theorem mem_of_get {α : Type} {es : List α} {j : Nat} {e : α} (hj : es[j]? = some e) : e ∈ es :=
  List.mem_of_getElem? hj

/-! ## The start -/

/-- **The loop's invariant at its start**, from `n`'s branch facts. -/
theorem spLoop_init {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {es : List UE}
    (hb : uBr X bl (spP X) X.t.mv.pgid'.toNat n r lo hi h es)
    (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (hsl : slotInv w.fl X.t.mv.pgid'.toNat (O ++ (ownSl X.v r.nv.pgid' ++ es.flatMap UE.D)))
    (hfr : spFree X w.fl w.wtxid (ownF r.nv.pgid' ++ es.flatMap UE.F)) (hpar : parOK X bl) :
    spLoop X w bl n r O lo hi h (ownSl X.v r.nv.pgid' ++ es.flatMap UE.D)
      (n :: es.flatMap UE.N) (es.flatMap UE.E) X w r es 0 [] [] where
  br := hb
  ile := Nat.zero_le _
  done := fun _ _ hk => absurd hk (Nat.not_lt_zero _)
  slot := hsl
  free := hfr
  step := spStep_refl O hG hG.2.1
  frame := spFrame_refl X bl _
  fresh := fun _ hl => absurd hl (List.not_mem_nil)
  EE := rfl
  nN := List.mem_cons_self
  NN := fun _ hl => List.mem_cons_of_mem _ hl
  Dk := fun _ hs => Or.inl hs
  Dn := fun _ hs => Or.inl hs
  Pd := fun _ hx => absurd rfl hx
  nv := rfl
  knil := Iff.rfl
  key := rfl
  cap := rfl
  live := hb.un.1
  chs := fun _ hc => Or.inl hc
  par := hpar

/-! ## A spilled child -/

/-- An entry's unspilled child is no spilled node. -/
theorem uBr_ch_unspilled {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {r : NRec}
    {lo hi : Option (List w8)} {h : Nat} {es : List UE}
    (hb : uBr X bl P hwm n r lo hi h es) {e : UE} {c : Loc} (he : e ∈ es) (hc : e.ch = some c) :
    ∃ (j : Nat) (Fc Dc : List Nat) (Nc : List Loc) (Ec : List El),
      es[j]? = some (⟨some c, Fc, Dc, Nc, Ec⟩ : UE) ∧ ∃ rc, X.node bl c = some rc ∧
      rc.nv.spilled' = false := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
  have hjl : j < r.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 hj).1
  have hent := hb.ent j _ e (List.getElem?_eq_getElem hjl) hj
  cases hent with
  | child _ _ _ _ _ _ _ _ c' rc F D N E _ hrc _ _ _ _ _ hut =>
    cases hc
    obtain ⟨rc', hrc', hsp⟩ := uTree_N_unspilled hut c (uTree_head hut)
    exact ⟨j, F, D, N, E, hj, rc', hrc', hsp⟩
  | fin => cases hc

/-- **A spilled child** (`c.spill()` returns at once): the invariant at the next index. -/
theorem spLoop_spilled {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D0 : List Nat} {N0 : List Loc} {E0 : List El} {X' : WX} {w' : WDb}
    {r' : NRec} {es : List UE} {i : Nat} {st : List FLStep} {T : List Loc} {c : Loc} {rc : NRec}
    (hl : spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es i st T)
    (hc : r'.cs[i]? = some c) (hrc : X'.node bl c = some rc) (hsp : rc.nv.spilled' = true) :
    spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es (i + 1) st T ∧ spilledN X' bl c := by
  have hcs : spilledN X' bl c := by
    rcases hl.br.cs c (List.mem_of_getElem? hc) with ⟨e, he, hec⟩ | hs
    · obtain ⟨_, _, _, _, _, _, rc', hrc', hsp'⟩ := uBr_ch_unspilled hl.br he hec
      rw [hrc] at hrc'; cases hrc'; rw [hsp] at hsp'; cases hsp'
    · exact hs
  refine ⟨{ hl with ile := (List.getElem?_eq_some_iff.1 hc).1, done := ?_ }, hcs⟩
  intro k c' hk hc'
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · exact hl.done k c' hk hc'
  · rw [hc] at hc'; cases hc'; exact hcs

/-- **A spilled child's pre** (the piece case). -/
theorem spLoop_spilledPre {X' : WX} {w' : WDb} {bl c : Loc} {rc : NRec} (hc : spilledN X' bl c)
    (hrc : X'.node bl c = some rc) (hG : spG X' w'.wtxid (mapLen w'.ms) w'.fl)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase) : spPre X' w' bl c rc O lo hi h F D N E cs := by
  obtain ⟨hlv, rc', hrc', hb, hsp, -⟩ := hc
  rw [hrc] at hrc'; cases hrc'
  exact ⟨hrc, hG, Or.inl ⟨hsp, hb, hlv⟩⟩

/-! ## An unspilled child -/

/-- The other entries' slots, `n`'s own and the frame: the child's frame. -/
abbrev chO (O : List Nat) (v : View) (r : NRec) (es : List UE) (j : Nat) : List Nat :=
  O ++ ownSl v r.nv.pgid' ++ (es.take j ++ es.drop (j + 1)).flatMap UE.D

theorem slotInv_child {fl : FLPg} {hwm : Nat} {O : List Nat} {v : View} {r : NRec}
    {es : List UE} {j : Nat} {c : Loc} {Fc Dc : List Nat} {Nc : List Loc} {Ec : List El}
    (hj : es[j]? = some ⟨some c, Fc, Dc, Nc, Ec⟩)
    (hsl : slotInv fl hwm (O ++ (ownSl v r.nv.pgid' ++ es.flatMap UE.D))) :
    slotInv fl hwm (chO O v r es j ++ Dc) := by
  refine slotInv_perm ?_ hsl
  rw [flatMap_split UE.D hj]
  simp only [chO, List.flatMap_append, List.append_assoc]
  exact List.Perm.append_left _ (List.Perm.append_left _ (List.Perm.append_left _
    List.perm_append_comm))

/-- **An unspilled child's pre** (the child case), at iteration `i`. -/
theorem spLoop_childPre {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D0 : List Nat} {N0 : List Loc} {E0 : List El} {X' : WX} {w' : WDb}
    {r' : NRec} {es : List UE} {i : Nat} {st : List FLStep} {T : List Loc} {c : Loc}
    {j : Nat} {Fc Dc : List Nat} {Nc : List Loc} {Ec : List El}
    (hl : spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es i st T)
    (hj : es[j]? = some ⟨some c, Fc, Dc, Nc, Ec⟩) (hnn : n ≠ null)
    (hv : X'.v = View.ofC X'.v.base w'.C)
    (hfc0 : ∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat)
    (hts0 : ∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat) :
    ∃ rc, X'.node bl c = some rc ∧ rc.nv.spilled' = false ∧
      spPre X' w' bl c rc (chO O X'.v r' es j) (childLo lo (wKey r'.ws) j)
        (childHi hi (wKey r'.ws) r'.ws.length j) h Fc Dc Nc Ec (.child n r' j lo hi) := by
  have hb := hl.br
  have hjl : j < r'.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 hj).1
  have hent := hb.ent j _ _ (List.getElem?_eq_getElem hjl) hj
  have htx : w'.wtxid = w.wtxid := wtxid_of_C hl.step.1
  cases hent with
  | child _ _ _ _ _ _ _ _ _ rc _ _ _ _ hcm hrc hpar hpg hkey hknil hne hut =>
    obtain ⟨rc', hrc', hsp⟩ := uTree_N_unspilled hut c (uTree_head hut)
    rw [hrc] at hrc'; cases hrc'
    refine ⟨rc, hrc, hsp, hrc, by rw [htx]; exact hl.step.2.2.2.1, Or.inr ⟨hut, ?_, ?_, ?_⟩⟩
    · -- the context
      have hnN : n ∉ Nc := by
        have hnd := hb.Nnd
        intro hm
        exact (List.nodup_cons.1 hnd).1
          (List.mem_flatMap.2 ⟨_, mem_of_get hj, hm⟩)
      have hpg0 : r'.nv.pgid' ≠ W64 0 := fun h0 =>
        absurd (hb.pg0 h0 _ (mem_of_get hj)) (by simp)
      exact ⟨hpar, hnn, hnN, hb.node, hb.un, hb.leaf, hpg0, hcm,
        ⟨_, List.getElem?_eq_getElem hjl, hpg.symm, hkey.symm⟩, rfl, rfl, hknil, hne.2, hne.1⟩
    · exact slotInv_child hj hl.slot
    · refine ⟨fun id hid => ?_, hv, fun y hy => by
        rw [hl.step.1]; rw [hl.step.2.1] at hy; exact hfc0 y (applySteps_free_sub _ _ _ _ hy),
      fun s hs => by
        rw [hl.step.1] at hs
        exact Nat.lt_of_lt_of_le (hts0 s hs) hl.frame.2.2.2.2.2.2.2.2.1, hl.par⟩
      rw [htx]
      refine hl.free id (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, mem_of_get hj, hid⟩))

/-! ## An error -/

/-- **An error of a child's spill** at iteration `i`: `n`'s error's facts. -/
theorem spLoop_err {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D0 : List Nat} {N0 : List Loc} {E0 : List El} {X' : WX} {w' : WDb}
    {r' : NRec} {es : List UE} {i : Nat} {st : List FLStep} {T : List Loc}
    (hl : spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es i st T) {X'' : WX} {w'' : WDb}
    {st' : List FLStep} (he : spErr X' X'' w' w'' st') : spErr X X'' w w'' (st ++ st') :=
  spErr_trans (spErr_of_frame hl.frame hl.step.1 hl.step.2.1 hl.step.2.2.1) he

/-! ## After the loop -/

/-- **Every entry finished** after the loop (every child spilled). -/
theorem spLoop_fin {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D0 : List Nat} {N0 : List Loc} {E0 : List El} {X' : WX} {w' : WDb}
    {r' : NRec} {es : List UE} {i : Nat} {st : List FLStep} {T : List Loc}
    (hl : spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es i st T) (hlen : r'.cs.length ≤ i) :
    ∀ k wk e, r'.ws[k]? = some wk → es[k]? = some e →
      ∃ S E, e = ⟨none, [], pgSlots (spP X') S, [], E⟩ ∧
      fTree (spP X') X'.t.mv.pgid'.toNat wk.pgid.toNat wk.key
        (childHi hi (wKey r'.ws) r'.ws.length k) h S E := by
  intro k wk e hw he
  refine uEnt_fin_of_spilled (hl.br.ent k wk e hw he) (fun c hc => ?_)
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hc
  exact hl.done m c (Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hm).1 hlen) hm

end loop

end Spill

end bbolt
end EtcdGrove
end Perennial
