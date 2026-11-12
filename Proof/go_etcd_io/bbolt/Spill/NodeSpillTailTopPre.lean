/-
`node.spill`'s tail (U9w4, `notes/bbolt-proof-plan.md`; pure): **the new root's spill's pre**
(`tail_top_spPre`): a top node split in two or more pieces under a new root `pl` (page id `0`),
at the pieces' loop's end. The new root is an unspilled branch whose entries are the pieces'
finished subtrees (`tail_top_uTree`, from `pcLoop_piecesOK`), a top node, the root of its bucket's
root node's chain (`chain_ext`: the old chain, `n`, then `pl`; the chain's nodes kept modulo
sources, `tail_kept`), its slots the pieces', no page to free.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneMain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section lemmas
variable [GooseExts] [GoGlobalContext]

theorem newParent_fields (nv : node) (cs : GoSlice) :
    (newParent nv cs).parent' = null ∧ (newParent nv cs).isLeaf' = false ∧
    (newParent nv cs).spilled' = false ∧ (newParent nv cs).bucket' = nv.bucket' ∧
    (newParent nv cs).pgid' = W64 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An entry put for a piece, by data. -/
theorem dat_get {ws : List WEntry} {ps : List Piece} (h : ws.map wDat = ps.map pcDat) {i : Nat}
    {w : WEntry} (hw : ws[i]? = some w) :
    ∃ p, ps[i]? = some p ∧ w.pgid = p.id ∧ w.key = p.k ∧ w.value = [] := by
  have e := congrArg (·[i]?) h
  simp only [List.getElem?_map, hw, Option.map_some] at e
  cases ep : ps[i]? with
  | none => rw [ep] at e; cases e
  | some p =>
    rw [ep] at e
    simp only [Option.map_some, Option.some.injEq, wDat, pcDat, Prod.mk.injEq] at e
    exact ⟨p, rfl, e.2.1, e.2.2.1, e.2.2.2⟩

theorem dat_wKey {ws : List WEntry} {ps : List Piece} (h : ws.map wDat = ps.map pcDat) :
    wKey ws = pcKey ps := by
  funext m
  unfold wKey pcKey
  cases ew : ws[m]? with
  | some w =>
    obtain ⟨p, hp, -, hk, -⟩ := dat_get h ew
    rw [hp]; exact hk
  | none =>
    have hl : ws.length = ps.length := by simpa using congrArg List.length h
    have : ps[m]? = none := by
      rw [List.getElem?_eq_none_iff] at ew ⊢; omega
    rw [this]; rfl

/-- The new root's entries' descriptors: finished subtrees, no nodes. -/
def finUEs (P : Pages) (ps : List Piece) : List UE :=
  ps.map fun p => ⟨none, [], pgSlots P p.S, [], treeEls P p.id.toNat⟩

theorem finUEs_ch (P : Pages) (ps : List Piece) : (finUEs P ps).filterMap UE.ch = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [finUEs] at ih ⊢

theorem finUEs_N (P : Pages) (ps : List Piece) : (finUEs P ps).flatMap UE.N = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [finUEs] at ih ⊢

theorem finUEs_F (P : Pages) (ps : List Piece) : (finUEs P ps).flatMap UE.F = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [finUEs] at ih ⊢

theorem finUEs_D (P : Pages) (ps : List Piece) : (finUEs P ps).flatMap UE.D = pcSlots P ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [finUEs, List.map_cons, List.flatMap_cons, pcSlots] at ih ⊢; rw [ih]

theorem finUEs_E (P : Pages) (ps : List Piece) :
    (finUEs P ps).flatMap UE.E = ps.flatMap fun x => treeEls P x.id.toNat := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [finUEs, List.map_cons, List.flatMap_cons] at ih ⊢; rw [ih]

theorem onChain_refl_eq {B : BRec} {a x : Loc} (h : onChain B a a x) : x = a := by
  cases h with
  | self => rfl
  | up _ _ _ r _ hne _ => exact absurd rfl hne

/-- **The chain after the new root** (`B0` the bucket at the start, `Bf` at the end): the old
chain's nodes kept with their parents and spilled, `n` spilled under `pl`, `pl` a root. -/
theorem chain_ext {B0 Bf : BRec} {n pl : Loc} {rnf rpf : NRec}
    (hn0 : ∀ r, B0.ns !! n = some r → r.nv.parent' = null)
    (hnf : Bf.ns !! n = some rnf) (hnp : rnf.nv.parent' = pl) (hnsp : rnf.nv.spilled' = true)
    (hpl : pl ≠ null) (hplf : Bf.ns !! pl = some rpf) (hpp : rpf.nv.parent' = null)
    {a rt : Loc} (h : nodeRootIn B0 a rt) (hrt : rt = n)
    (hK : ∀ x, onChain B0 a n x → x ≠ n → ∃ r0 rf, B0.ns !! x = some r0 ∧ Bf.ns !! x = some rf ∧
      rf.nv.parent' = r0.nv.parent' ∧ rf.nv.spilled' = true) :
    nodeRootIn Bf a pl ∧
      ∀ x, onChain Bf a pl x → x ≠ pl → ∃ rx, Bf.ns !! x = some rx ∧ rx.nv.spilled' = true := by
  induction h with
  | top m r hm hp =>
    subst hrt
    refine ⟨nodeRootIn.up m pl rnf hnf (by rw [hnp]; exact hpl)
      (by rw [hnp]; exact nodeRootIn.top pl rpf hplf hpp), ?_⟩
    intro x hx hne
    cases hx with
    | self => exact ⟨rnf, hnf, hnsp⟩
    | up _ _ _ r' hr' _ hrest =>
      rw [hnf] at hr'; cases hr'
      rw [hnp] at hrest
      exact absurd (onChain_refl_eq hrest) hne
  | up m rt r hm hp hrest ih =>
    by_cases e : m = n
    · subst e; exact absurd (hn0 r hm) hp
    obtain ⟨r0, rf, h0, hf, hpar, hspf⟩ := hK m (onChain.self m n) e
    rw [hm] at h0; cases h0
    obtain ⟨ih1, ih2⟩ := ih hrt fun x hx hne => hK x (onChain.up m n x r hm e hx) hne
    refine ⟨nodeRootIn.up m pl rf hf (by rw [hpar]; exact hp) (by rw [hpar]; exact ih1), ?_⟩
    intro x hx hne
    cases hx with
    | self => exact ⟨rf, hf, hspf⟩
    | up _ _ _ r' hr' _ hrest' =>
      rw [hf] at hr'; cases hr'
      rw [hpar] at hrest'
      exact ih2 x hrest' hne

/-- **A node outside `n`'s tree is kept modulo sources** from the spill's start to the pieces'
loop (the parent `pl` fresh or `null`). -/
theorem tail_kept {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec} {Xf : WX}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hfr : spFrame X2 Xf bl (xs.map (·.1) ++ [pl]))
    (hplf : pl = null ∨ (X'.nilCh bl n r').t.objs !! pl = none) {l : Loc} (hlN : l ∉ N)
    {r : NRec} (hr : X.node bl l = some r) : ∃ r'', Xf.node bl l = some r'' ∧ nodeSim r r'' := by
  obtain ⟨-, -, -, -, -, -, hfr0, hT⟩ := spEnd_rec hpre hsp hend
  have hnN : n ∈ N := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨hut, -⟩
    · rw [hsp] at hs; cases hs
    · exact uTree_head hut
  have hlT : l ∉ N ++ T0 := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hlN hm
    · rw [node_none_of_objs (hT l hm)] at hr; cases hr
  obtain ⟨r1, hr1, hs1, -⟩ := spFrame_node hfr0 hr hlT
  have hne : l ≠ n := fun e => hlN (e ▸ hnN)
  have hr1' : (X'.nilCh bl n r').node bl l = some r1 := by
    unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ hne]; exact hr1
  have hnull : l ≠ null := by
    intro e; subst e
    obtain ⟨B, hB, hrB⟩ := node_bs_of hr
    rw [derefPre_null hpre.2.1.2.2.1 bl B hB] at hrB; cases hrB
  have hx : l ∉ xs.map (·.1) ++ [pl] := by
    rw [xs_map_head hsr.head]
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false]
    rintro ((e | ⟨x, hx, e⟩) | e)
    · exact hne e
    · subst e; rw [node_none_of_objs (hsr.fresh x hx)] at hr1'; cases hr1'
    · rcases hplf with h0 | h0
      · exact hnull (e.trans h0)
      · subst e; rw [node_none_of_objs h0] at hr1'; cases hr1'
  obtain ⟨r2, hr2, hs2, -⟩ := spFrame_node hsr.frame hr1' hx
  obtain ⟨r3, hr3, hs3, -⟩ := spFrame_node hfr hr2 hx
  exact ⟨r3, hr3, nodeSim_trans hs1 (nodeSim_trans hs2 hs3)⟩

/-- **The new root at the pieces' loop's end** (a top node split in two or more): fresh, live,
its children the pieces, its entries theirs, a top unspilled branch of `bl` owning its inodes. -/
theorem tail_top_par {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec} {Es : List (List El)} {Ds : List (List Nat)} {ps : List Piece}
    {Xf : WX} {wf : WDb} {stl : List FLStep} {rp : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E .top) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hL : pcLoop X' r' X2 w' bl O lo hi h xs wss pl rp0 [] 0 Es Ds xs.length ps Xf wf stl)
    (hpl : pl ≠ null) (hrp : Xf.node bl pl = some rp) :
    2 ≤ xs.length ∧ (X'.nilCh bl n r').t.objs !! pl = none ∧ pl ∈ Xf.live ∧
      rp.cs = xs.map (·.1) ∧ rp.nv.parent' = null ∧ rp.nv.isLeaf' = false ∧
      rp.nv.spilled' = false ∧ rp.nv.bucket' = bl ∧ rp.capOwn = true ∧ wsSorted rp.ws ∧
      rp.ws.map wDat = ps.map pcDat ∧ rp.ins.length = rp.ws.length := by
  have hrN : r'.nilCh.nv.parent' = null := by
    obtain ⟨-, -, -, hnv, -⟩ := spEnd_rec hpre hsp hend
    show r'.nv.parent' = null; rw [hnv]
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hsp] at hs; cases hs
    · exact hctx.1
  obtain ⟨-, -, -, -, hbl, -⟩ := tail_pre hpre hsp hend
  obtain ⟨rpi, hrpi, hplv, -, hcap, hsort, hws, hins, hcs, hnv, -⟩ := hL.par hpl
  rw [hrp] at hrpi; cases hrpi
  rcases hsr.par with ⟨-, -, h1⟩ | ⟨-, h2, -, hfr, hrp0, -⟩ | ⟨h1, -⟩
  · exact absurd h1 hpl
  · have hlen0 : xs.length ≠ 0 := by omega
    obtain ⟨f1, f2, f3, f4, -⟩ := newParent_fields r'.nilCh.nv rp0.nv.children'
    have hnv' : rp.nv.parent' = rp0.nv.parent' ∧ rp.nv.isLeaf' = rp0.nv.isLeaf' ∧
        rp.nv.spilled' = rp0.nv.spilled' ∧ rp.nv.bucket' = rp0.nv.bucket' := by
      rw [hnv]; exact ⟨rfl, rfl, rfl, rfl⟩
    rw [hrp0] at hnv' hcs
    refine ⟨h2, hfr, hplv, hcs, hnv'.1.trans f1, hnv'.2.1.trans f2, hnv'.2.2.1.trans f3,
      hnv'.2.2.2.trans (f4.trans hbl), hcap, hsort, ?_, hins⟩
    rw [hws]; unfold parWs; simp [hlen0]
  · exact absurd hrN h1

/-- **The new root's unspilled tree**: a branch of the pieces' finished subtrees. -/
theorem tail_top_uTree {Xf : WX} {bl pl : Loc} {rp : NRec} {lo hi : Option (List w8)} {h : Nat}
    {ps : List Piece} (hrp : Xf.node bl pl = some rp) (hpg : rp.nv.pgid' = W64 0)
    (hpk : piecesOK Xf bl pl (spP Xf) Xf.t.mv.pgid'.toNat lo hi h ps)
    (hlv : pl ∈ Xf.live) (hcs : rp.cs = ps.map Piece.l) (hleaf : rp.nv.isLeaf' = false)
    (hspl : rp.nv.spilled' = false) (hbl : rp.nv.bucket' = bl) (hcap : rp.capOwn = true)
    (hsort : wsSorted rp.ws) (hws : rp.ws.map wDat = ps.map pcDat)
    (hins : rp.ins.length = rp.ws.length) (h2 : 2 ≤ ps.length) :
    uTree Xf bl (spP Xf) Xf.t.mv.pgid'.toNat pl lo hi (h + 1) [] (pcSlots (spP Xf) ps) [pl]
      (ps.flatMap fun x => treeEls (spP Xf) x.id.toNat) := by
  obtain ⟨-, hnd, hp⟩ := hpk
  have hlen : rp.ws.length = ps.length := by simpa using congrArg List.length hws
  have hwk := dat_wKey hws
  let es : List UE := finUEs (spP Xf) ps
  have hun : uNode Xf bl pl rp lo hi := by
    refine ⟨hlv, hbl, hspl, hcap, hins, hsort, fun e he => ?_, fun h0 => absurd hpg h0⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨p, hpi, -, hk, hv⟩ := dat_get hws hi
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hkin, hkl, hkb, -⟩ := hp i p hpi
    rw [hk, hv]
    exact ⟨hkin, hkl, by simpa using hkb⟩
  have H := uTree.branch (X := Xf) (bl := bl) (P := spP Xf) (hwm := Xf.t.mv.pgid'.toNat)
    pl rp lo hi h es hrp hun hleaf (by omega) (by simp [es, finUEs, hlen]) ?_ (by rw [finUEs_ch]; exact List.nodup_nil) ?_
    (by rw [hcs]; exact hnd) (by rw [finUEs_N]; exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) ?_
  · have e1 : ownF rp.nv.pgid' ++ es.flatMap UE.F = [] := by simp [ownF, hpg, es, finUEs_F]
    have e2 : ownSl Xf.v rp.nv.pgid' ++ es.flatMap UE.D = pcSlots (spP Xf) ps := by
      simp [ownSl, hpg, es, finUEs_D]
    have e3 : pl :: es.flatMap UE.N = [pl] := by rw [finUEs_N]
    have e4 : es.flatMap UE.E = ps.flatMap fun x => treeEls (spP Xf) x.id.toNat := finUEs_E _ _
    rw [e1, e2, e3, e4] at H
    exact H
  · intro i w e hw he
    obtain ⟨p, hpi, hpg', hk, -⟩ := dat_get hws hw
    simp only [es, finUEs, List.getElem?_map, hpi, Option.map_some, Option.some.injEq] at he
    subst he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hf⟩ := hp i p hpi
    refine uEnt.fin pl lo hi rp.ws rp.cs h i w p.S _ ?_
    rw [hpg', hk, hwk, hlen]; exact hf
  · intro c hc
    right
    rw [hcs] at hc
    obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hpm
    obtain ⟨rl, hrl, hlvl, hbll, hspll, hcsl, -, -, -, hwl, -⟩ := hp i p hi
    exact ⟨hlvl, rl, hrl, hbll, hspll, hcsl, hwl⟩
  · intro _ e he
    simp only [es, finUEs, List.mem_map] at he
    obtain ⟨p, -, rfl⟩ := he
    rfl

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
