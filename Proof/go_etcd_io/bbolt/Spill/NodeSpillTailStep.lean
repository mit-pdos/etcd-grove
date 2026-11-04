/-
`node.spill` after its children's loop (U9y, `notes/bbolt-proof-plan.md`; pure): **a piece's step
keeps the pieces' loop's invariant** (`pcInv_stepX`, what `Spill/NodeSpillTailInv.pcInv_step`
states, with the objects disjoint, the free ids no view pages and the piece's `insLens`).
`pcStep` (U9y) carries the allocation's freelist steps, the parent's inodes' count after its put and
the piece's key slice not nil, which the invariant needs.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitPcPre
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState
public import Proof.go_etcd_io.bbolt.Spill.PcStepSlots
public import Proof.go_etcd_io.bbolt.Spill.PcStepFrame
public import Proof.go_etcd_io.bbolt.Spill.PcStepPar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section step
variable [GooseExts] [GoGlobalContext]

theorem node_ne_null {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl)
    {bl l : Loc} {r : NRec} (hr : X.node bl l = some r) : l ≠ null := by
  intro he; subst he
  unfold WX.node at hr
  cases e : X.t.bs !! bl with
  | none => rw [e] at hr; cases hr
  | some B =>
    rw [e] at hr
    have := (hG.2.2.1.2.2.1 bl B e).2
    simp only [Option.bind_some] at hr
    rw [this] at hr; cases hr

/-- **A piece's step keeps the invariant** (the free ids no view pages, the
objects disjoint: `spillTail_gen`'s `H3`). -/
theorem pcInv_stepX {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) (x : Loc × node × List Inode) (rl : NRec) (X3 : WX) (w2 : WDb)
    (st' : List FLStep) (id : w64)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) (hx : xs[i]? = some x)
    (hrl : Xi.node bl x.1 = some rl)
    (hs : pcStep Xi wi bl x.1 rl (pcCount (insSize rl.ins)) X3 w2 st' id)
    (hd : objsDisj Xi.t) (hfv : ∀ y ∈ wi.fl.free, Xi.v.pages !! y.toNat = none)
    (hlr : insLens rl.ins rl.ws) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl (i + 1) X3 w2 (st ++ st') := by
  obtain ⟨rl', hrl', -, -, hpp⟩ := pcInv_pre' hpre hsp xs pl i Xi wi st x hI hx
  rw [hrl] at hrl'; cases hrl'
  replace hpp := hpp hlr
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps, stl, hend, hlens, hsr, hfit, rfl,
    hEs, hents, hD, hcs, hL⟩ := hI
  have hil : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
  obtain ⟨ws, hws⟩ : ∃ ws, wss[i]? = some ws :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hil)⟩
  obtain ⟨Sb, Eb, hDi, hEi, hSb⟩ := hents i ws hws
  let pn : Piece := ⟨x.1, id, wssKey wss i, nodePages id.toNat ws.length Sb⟩
  obtain ⟨hlv, hbl, -, hG1, hne, hil0, -, hpf, -, -, -, hparp, hins31⟩ := hpp
  obtain ⟨rk, hrk, -, hsim⟩ := hL.todo i x ws (Nat.le_refl _) hx hws
  rw [hrl] at hrk; cases hrk
  obtain ⟨-, -, hxbl, hxlf, -, hxpg, hxpl, hxch, -⟩ := hsr.prec i x ws hx hws
  have hnv : rl.nv = { x.2.1 with key' := rl.nv.key' } := by
    rw [hsim.1]; unfold splitRec; split <;> rfl
  have hrpl : rl.nv.parent' = pl := by rw [hnv]; exact hxpl
  have hGi := hL.step.2.2.2.1
  have hnn : ∀ {l : Loc} {r : NRec}, Xi.node bl l = some r → l ≠ null :=
    fun hr => node_ne_null hGi hr
  have hpl1 : rl.nv.parent' ≠ null → rl.nv.parent' ≠ x.1 := fun h => (hparp h).elim fun _ hh => hh.2.2.1
  obtain ⟨ra, rp, s, ins, q, hX3l, hsa, hpar3, hlive3, hpg3, htx3, hmk3, hext3, hc0, hbuf3,
    hbnone⟩ := pcStepX_state hs hrl hpl1 hG1
    (fun y hy => hL.slot.2.2.2 y (List.mem_append_left _ hy))
  have hG3 := pcStepX_spG hs hrl hlv hne (fun h => ⟨hpl1 h, (hparp h).elim fun _ hh => hh.2.1⟩) hd hG1
    (fun y hy => hL.slot.2.2.2 y hy) hfv hL.vb
  have hfr3 := pcStepX_frame' hs hrl hd hpl1 hG1
    (fun y hy => hL.slot.2.2.2 y (List.mem_append_left _ hy))
  obtain ⟨hPid, hPne⟩ := spP_bufs_insert hbuf3 hpg3
  have hfresh := pcStepX_fresh hs hL.slot
  have hplen := hL.len
  -- the pieces' nodes other than `x`'s are neither it nor the parent
  have hoth : ∀ k x', xs[k]? = some x' → k ≠ i → x'.1 ∉ [x.1, rl.nv.parent'] := by
    intro k x' hx' hki hm
    rcases List.mem_cons.1 hm with he | hm
    · have hkl := (List.getElem?_eq_some_iff.1 hx').1
      apply hki
      have hkm : k < (xs.map (·.1)).length := by simpa using hkl
      have him : i < (xs.map (·.1)).length := by simpa using hil
      refine (List.Nodup.getElem_inj (i := k) (j := i) (hi := hkm) (hj := him) hsr.nd).1 ?_
      simp only [List.getElem_map]
      rw [(List.getElem?_eq_some_iff.1 hx').2, (List.getElem?_eq_some_iff.1 hx).2]; exact he
    · rw [List.mem_singleton, hrpl] at hm
      by_cases hpn : pl = null
      · obtain ⟨rk, hrk, -⟩ : ∃ rk, Xi.node bl x'.1 = some rk ∧ True := by
          rcases Nat.lt_or_ge k i with hk | hk
          · obtain ⟨p, hp⟩ : ∃ p, ps[k]? = some p :=
              ⟨_, List.getElem?_eq_getElem (by rw [hplen]; exact hk)⟩
            obtain ⟨wk, hwk⟩ : ∃ wk, wss[k]? = some wk := ⟨_, List.getElem?_eq_getElem
              (by rw [hsr.len]; exact (List.getElem?_eq_some_iff.1 hx').1)⟩
            obtain ⟨rk, hrk, -⟩ := hL.done k x' p wk hx' hp hwk
            exact ⟨rk, hrk, trivial⟩
          · obtain ⟨wk, hwk⟩ : ∃ wk, wss[k]? = some wk := ⟨_, List.getElem?_eq_getElem
              (by rw [hsr.len]; exact (List.getElem?_eq_some_iff.1 hx').1)⟩
            obtain ⟨rk, hrk, -⟩ := hL.todo k x' wk hk hx' hwk
            exact ⟨rk, hrk, trivial⟩
        exact hnn hrk (hm.trans hpn)
      · obtain ⟨-, -, -, hnot, -⟩ := hL.par hpn
        exact hnot (hm ▸ List.mem_map_of_mem (f := (·.1)) (List.mem_of_getElem? hx'))
  -- the slots
  have hDl : i < Ds.length := by rw [hL.Dlen]; exact hil
  have hDs : (Ds.drop i).flatten = Ds.getD i [] ++ (Ds.drop (i + 1)).flatten := by
    rw [List.drop_eq_getElem_cons hDl, List.flatten_cons]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hDl]
  have hnd := hL.slot.1
  unfold pcOwn at hnd
  rw [hDs] at hnd
  have hDiPS : ∀ y ∈ Ds.getD i [], y ∉ pcSlots (spP Xi) ps := by
    intro y hy hy'
    have hsub : (Ds.getD i [] ++ pcSlots (spP Xi) ps).Sublist
        (O ++ ((if i = 0 then ownSl X'.v r'.nv.pgid' else []) ++
          (Ds.getD i [] ++ (Ds.drop (i + 1)).flatten) ++ pcSlots (spP Xi) ps)) :=
      (((List.sublist_append_left _ _).trans (List.sublist_append_right _ _)).append
        (List.Sublist.refl _)).trans (List.sublist_append_right _ _)
    exact (List.nodup_append.1 (hnd.sublist hsub)).2.2 y hy y hy' rfl
  have hown : ∀ y, (y ∈ Ds.getD i [] ∨ y ∈ pcSlots (spP Xi) ps) →
      y ∈ O ++ ((if i = 0 then ownSl X'.v r'.nv.pgid' else []) ++ (Ds.drop i).flatten ++
        pcSlots (spP Xi) ps) := by
    intro y hy
    rw [hDs]
    rcases hy with hy | hy
    · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_append_left _ hy)))
    · exact List.mem_append_right _ (List.mem_append_right _ hy)
  have hneid : ∀ y, (y ∈ Ds.getD i [] ∨ y ∈ pcSlots (spP Xi) ps) → y ≠ id.toNat := by
    intro y hy he
    rcases hfresh y (hown y hy) with h1 | h1 <;> omega
  have hpid : ∀ p ∈ ps, p.id.toNat ∈ pgSlots (spP Xi) p.S := by
    intro p hp
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
    have hkl : k < xs.length := by have := (List.getElem?_eq_some_iff.1 hk).1; omega
    obtain ⟨xk, hxk⟩ : ∃ xk, xs[k]? = some xk := ⟨_, List.getElem?_eq_getElem hkl⟩
    obtain ⟨wk, hwk⟩ : ∃ wk, wss[k]? = some wk :=
      ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hkl)⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hftc, hst⟩ := hL.done k xk p wk hxk hk hwk
    by_cases hpn : pl = null
    · exact mem_pgSlots_self (sTree_root_mem (hst hpn).1)
    · have hft := hftc hpn
      obtain ⟨pg, hpg, -⟩ := hft.2.1
      exact mem_pgSlots_self ((hft.1.has _).1 (treeHas.root _ pg hpg))
  have hSbag : ∀ m < ws.length, ∀ y ∈ Sb m, spP X3 !! y = spP X' !! y := by
    intro m hm y hy
    have hyD : y ∈ Ds.getD i [] := by
      rw [hDi]; exact List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, mem_pgSlots_self hy⟩
    rw [hPne y (hneid y (Or.inl hyD))]
    apply Classical.byContradiction; intro hne
    obtain ⟨p, hp, he⟩ := hL.agree y hne
    exact hDiPS y hyD (List.mem_flatMap.2 ⟨p, hp, he ▸ hpid p hp⟩)
  have hv' : Xi.v.pages = X'.v.pages := by
    rw [hL.step.2.2.1, hsr.same.2.2.2, nilCh_v]
  have hA : (if i = 0 then ownSl X'.v r'.nv.pgid' else []) = ownSl Xi.v rl.nv.pgid' := by
    have hpg' : rl.nv.pgid' = x.2.1.pgid' := by rw [hnv]
    rw [hpg', hxpg]
    by_cases hi0 : i = 0
    · simp only [hi0, ite_true]; rw [ownSl_congr hv']; rfl
    · simp only [hi0, ite_false]; unfold ownSl; simp
  have hcnt : pcCount (insSize rl.ins) - 1 < 2 ^ 32 := by
    have e : insSize rl.ins = 16 + (pageBody true (wsMs rl.ws)).length := by
      rw [body_ws, insSize_ws rl.ins rl.ws hlr hil0]
    have := hpf.2.1
    unfold pcCount; omega
  have hPS : pcSlots (spP X3) ps = pcSlots (spP Xi) ps := by
    unfold pcSlots
    refine flatMap_congr' fun p hp => pgSlots_congr fun y hy => hPne y (hneid y (Or.inr
      (List.mem_flatMap.2 ⟨p, hp, mem_pgSlots_self hy⟩)))
  have hpn : pgSlots (spP X3) pn.S =
      List.range' id.toNat (pcCount (insSize rl.ins)) ++ Ds.getD i [] := by
    show pgSlots (spP X3) (id.toNat :: (List.range ws.length).flatMap Sb) = _
    unfold pgSlots
    rw [List.flatMap_cons, hPid]
    simp only []
    unfold pcPage
    rw [wPage_overflow]
    have : (W32 ((pcCount (insSize rl.ins) - 1 : Nat) : Int)).toNat =
        pcCount (insSize rl.ins) - 1 := by word
    rw [this, show 1 + (pcCount (insSize rl.ins) - 1) = pcCount (insSize rl.ins) by omega,
      hDi, List.flatMap_assoc]
    congr 1
    refine flatMap_congr' fun m hm => ?_
    exact (pgSlots_congr (fun y hy => hSbag m (List.mem_range.1 hm) y hy))
  have hfin : pcSlots (spP X3) (ps ++ [pn]) =
      pcSlots (spP Xi) ps ++ (List.range' id.toNat (pcCount (insSize rl.ins)) ++
        Ds.getD i []) := by
    rw [← hpn, ← hPS]; unfold pcSlots; simp
  -- the piece's first key
  have hw0k : ra.w0.key = wssKey wss i := by
    have hwd : ra.ws.map wDat = ws.map wDat := hsa.2.2.1.trans (hsim.2.2.1.trans (by
      unfold splitRec; split <;> rfl))
    unfold wssKey; rw [hws]
    show (ra.ws.headD default).key = wKey ws 0
    cases ews : ws with
    | nil => rw [ews] at hwd; simp at hwd; rw [hwd]; rfl
    | cons e es =>
      rw [ews] at hwd
      cases era : ra.ws with
      | nil => rw [era] at hwd; simp at hwd
      | cons e' es' =>
        rw [era] at hwd
        simp only [List.map_cons, List.cons.injEq] at hwd
        simp [wKey, wDat_key hwd.1]
  refine ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps ++ [pn], stl ++ st', hend, hlens,
    hsr, hfit, by rw [List.append_assoc], hEs, hents, ?_, hcs, ?_⟩
  rotate_left
  exact {
    len := by rw [List.length_append, hplen]; rfl
    start := fun h => absurd h (Nat.succ_ne_zero _)
    vb := fun y pg hy => Nat.lt_of_lt_of_le (hL.vb y pg (hpg3 ▸ hy)) hmk3
    ile := hil
    pcl := by
      intro k p x' hp hx'
      rcases Nat.lt_or_ge k ps.length with hk | hk
      · rw [List.getElem?_append_left hk] at hp; exact hL.pcl k p x' hp hx'
      · rw [List.getElem?_append_right hk] at hp
        have hk0 : k - ps.length = 0 := by
          cases e : k - ps.length with
          | zero => rfl
          | succ _ => rw [e] at hp; simp at hp
        rw [hk0] at hp; simp at hp; subst hp
        have : k = i := by omega
        subst this; rw [hx] at hx'; cases hx'; rfl
    Elen := hL.Elen
    Dlen := hL.Dlen
    step := spStep_trans hL.step (pcStepX_step hs hrl hG3 hL.slot (by
      intro hpg
      have hpg' : rl.nv.pgid' = x.2.1.pgid' := by rw [hnv]
      rw [hpg', hxpg] at hpg ⊢
      by_cases hi0 : i = 0
      · subst hi0
        simp only [ite_true] at hpg ⊢
        change r'.nv.pgid' ≠ W64 0 at hpg
        change r'.nv.pgid'.toNat ∈ _
        refine List.mem_append_left _ (List.mem_append_left _ ?_)
        show _ ∈ (if 0 = 0 then ownSl X'.v r'.nv.pgid' else [])
        rw [if_pos rfl]
        unfold ownSl; rw [if_neg hpg]
        exact mem_pgSlots_self (List.mem_singleton_self _)
      · rw [if_neg hi0] at hpg; exact absurd rfl hpg))
    frame := spFrame_mono (spFrame_trans hL.frame hfr3) (by
      intro l' hl'
      rcases List.mem_append.1 hl' with h' | h'
      · exact h'
      · rcases List.mem_cons.1 h' with rfl | h'
        · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_getElem? hx))
        · rw [List.mem_singleton] at h'; subst h'; rw [hrpl]
          exact List.mem_append_right _ (List.mem_singleton_self _))
    todo := by
      intro k x' ws' hk hx' hws'
      obtain ⟨rk, hrk, hlvk, hsk⟩ := hL.todo k x' ws' (by omega) hx' hws'
      obtain ⟨rk', hrk', hsk', hlk⟩ := spFrame_node hfr3 hrk (hoth k x' hx' (by omega))
      exact ⟨rk', hrk', hlk.2 hlvk, nodeSim_trans hsk hsk'⟩
    done := by
      intro k x' p ws' hx' hp hws'
      rcases Nat.lt_or_ge k ps.length with hk | hk
      · rw [List.getElem?_append_left hk] at hp
        obtain ⟨rk, hrk, hlvk, hb, hspd, hcs', hch', hpar', hpg', hwd, hpk, hkey, hftc, hst⟩ :=
          hL.done k x' p ws' hx' hp hws'
        obtain ⟨rk', hrk', hsk, hlk⟩ := spFrame_node hfr3 hrk (hoth k x' hx' (by omega))
        have hag : ∀ y ∈ pgSlots (spP Xi) p.S, spP X3 !! y = spP Xi !! y := by
          intro y hy
          apply hPne y
          intro hye
          have hyL : y ∈ O ++ ((if i = 0 then ownSl X'.v r'.nv.pgid' else []) ++
              (Ds.drop i).flatten ++ pcSlots (spP Xi) ps) :=
            List.mem_append_right _ (List.mem_append_right _
              (List.mem_flatMap.2 ⟨p, List.mem_of_getElem? hp, hy⟩))
          rcases hfresh y hyL with h1 | h1 <;> omega
        refine ⟨rk', hrk', hlk.2 hlvk, by rw [hsk.1]; exact hb, by rw [hsk.1]; exact hspd,
          by rw [hsk.2.2.2.2.1]; exact hcs', by rw [hsk.1]; exact hch', by rw [hsk.1]; exact hpar',
          by rw [hsk.1]; exact hpg', hsk.2.2.1.trans hwd, hpk, fun hpl => ?_,
          fun hpl => (fTree_agree hag hmk3 (hftc hpl)).1, fun hpl => ?_⟩
        rotate_left
        · have hagS : ∀ y ∈ p.S, spP X3 !! y = spP Xi !! y :=
            fun y hy => hag y (mem_pgSlots_self hy)
          exact ⟨sTree_agree hagS hmk3 (hst hpl).1, by
            rw [treeEls_agree (hst hpl).1 hagS]; exact (hst hpl).2⟩
        obtain ⟨h1, h2⟩ := hkey hpl
        exact ⟨hsk.2.2.2.2.2.1.trans h1, fun he => h2 (hsk.2.1.1 he)⟩
      · rw [List.getElem?_append_right hk] at hp
        have hk0 : k - ps.length = 0 := by
          cases e : k - ps.length with
          | zero => rfl
          | succ _ => rw [e] at hp; simp at hp
        rw [hk0] at hp; simp at hp; subst hp
        have : k = i := by omega
        subst this; rw [hx] at hx'; cases hx'; rw [hws] at hws'; cases hws'
        have hft_new : pl ≠ null → fTree (spP X3) X3.t.mv.pgid'.toNat id.toNat (wssKey wss k)
            (childHi hi (wssKey wss) xs.length k) h (nodePages id.toNat ws.length Sb)
            (Es.getD k []) := sorry
        have hst_new : pl = null → sTree (spP X3) X3.t.mv.pgid'.toNat id.toNat lo hi h
            (nodePages id.toNat ws.length Sb) ∧
            treeEls (spP X3) id.toNat = Es.getD k [] := sorry
        have hcs0 : ra.cs = [] := by
          rw [hsa.2.2.2.2.1, hsim.2.2.2.2.1]; unfold splitRec; split <;> rfl
        have hwd : ra.ws.map wDat = ws.map wDat := hsa.2.2.1.trans (hsim.2.2.1.trans (by
          unfold splitRec; split <;> rfl))
        have hra := hsa.1
        rw [hrpl] at hX3l
        refine ⟨_, hX3l, by rw [hlive3]; exact hlv, ?_⟩
        unfold pcRec
        by_cases hpn : pl ≠ null
        · rw [if_pos (by simpa using hpn)]
          obtain ⟨rpi, hrpi, -⟩ := hparp (by rw [hrpl]; exact hpn)
          obtain ⟨-, -, -, hk0'⟩ := hpar3 (by rw [hrpl]; exact hpn) rpi hrpi
          refine ⟨by simp only []; rw [hra]; exact hbl, rfl, hcs0,
            by simp only []; rw [hra]; show rl.nv.children' = _; rw [hnv]; exact hxch,
            by simp only []; rw [hra]; exact hrpl, rfl, hwd, rfl, fun _ => ⟨?_, hk0'⟩, hft_new,
            hst_new⟩
          show ra.w0.key = wssKey wss k
          unfold wssKey; rw [hws]
          show (ra.ws.headD default).key = wKey ws 0
          cases ews : ws with
          | nil => rw [ews] at hwd; simp at hwd; rw [hwd]; rfl
          | cons e es =>
            rw [ews] at hwd
            cases era : ra.ws with
            | nil => rw [era] at hwd; simp at hwd
            | cons e' es' =>
              rw [era] at hwd
              simp only [List.map_cons, List.cons.injEq] at hwd
              simp [wKey, wDat_key hwd.1]
        · rw [if_neg (by simpa using hpn)]
          refine ⟨by simp only []; rw [hra]; exact hbl, rfl, hcs0,
            by simp only []; rw [hra]; show rl.nv.children' = _; rw [hnv]; exact hxch,
            by simp only []; rw [hra]; exact hrpl, rfl, hwd, rfl, fun h' => absurd h' hpn,
            hft_new, hst_new⟩
    slot := by
      have hsl0 : slotInv wi.fl Xi.t.mv.pgid'.toNat (O ++ (ownSl Xi.v rl.nv.pgid' ++
          (Ds.getD i [] ++ (Ds.drop (i + 1)).flatten ++ pcSlots (spP Xi) ps))) := by
        have := hL.slot; unfold pcOwn at this; rw [hDs, hA] at this; simpa only [List.append_assoc] using this
      have h5 := pcStepX_slot hs hG1 hsl0
      unfold pcOwn
      rw [hfin]
      refine slotInv_perm ?_ h5
      rw [List.perm_iff_count]; intro a
      simp only [List.count_append, Nat.add_one_ne_zero, ite_false, List.count_nil]
      omega
    agree := by
      intro y hy
      by_cases h1 : spP Xi !! y = spP X' !! y
      · by_cases h2 : y = id.toNat
        · exact ⟨pn, List.mem_append_right _ (List.mem_singleton_self _), h2⟩
        · exact absurd (by rw [hPne y h2, h1]) hy
      · obtain ⟨p, hp, he⟩ := hL.agree y h1
        exact ⟨p, List.mem_append_left _ hp, he⟩
    par := by
      intro hpn
      obtain ⟨rpi0, hrpi0, hplv, hnot, hcap, hsort, hpw, -, hcs0, hnv0, hkey0, hkn0⟩ := hL.par hpn
      have hpn' : rl.nv.parent' ≠ null := by rw [hrpl]; exact hpn
      obtain ⟨hX3p, hsimp, hinsl, -⟩ := hpar3 hpn' rpi0 (by rw [hrpl]; exact hrpi0)
      rw [hrpl] at hX3p
      -- the parent's put: the piece's entry spliced in after the done pieces'
      -- the keys around the piece's entry in the parent (TODO U9z2: from spCtx's entry `j`, n's
      -- entries within `[lo, hi)` and sorted, the split's pieces' keys, splitRec's `key'`)
      have hkeys : (j < bs.length ∨ (bs = [] ∧ j = 0)) ∧
          (i = 0 → bs ≠ [] → wKey bs j = pcOldKey ra) ∧ (i ≠ 0 → pcOldKey ra = pn.k) ∧
          (i = 0 → 0 < j → go.GoStringLt (wKey bs (j - 1)) pn.k) ∧
          (i ≠ 0 → ∀ p, ps[i - 1]? = some p → go.GoStringLt p.k pn.k) ∧
          (j + 1 < bs.length → go.GoStringLt pn.k (wKey bs (j + 1))) := sorry
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hkeys
      have hcore := parPut (ws := rp.ws) (k := pcOldKey ra) (e := pcEnt ra id) (pn := pn)
        (by rw [hsimp.2.2.1]; exact hpw) (wsSorted_of_dat hsimp.2.2.1 hsort) hplen k1
        (by show (W32 0, id, ra.w0.key, ([] : List w8)) = (W32 0, id, wssKey wss i, []); rw [hw0k])
        k2 k3 k4 k5 k6
      refine ⟨_, hX3p, by rw [hlive3]; exact hplv, hnot, ?_, hcore.1, hcore.2, hinsl,
        by show rp.cs = _; rw [hsimp.2.2.2.2.1]; exact hcs0, ?_,
        by show rp.key = _; rw [hsimp.2.2.2.2.2.1]; exact hkey0,
        by show rp.nv.key' = _ ↔ _; rw [hsimp.2.1]; exact hkn0⟩
      · show rp.capOwn = true
        rw [hsimp.2.2.2.2.2.2]; exact hcap
      · -- DEFECT (pcLoop.par): the parent's key slice may change source (nodeSim), so its
        -- struct is `rp0`'s only modulo `key'` too
        sorry }
  -- the slots' bookkeeping
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hc0' : 0 < pcCount (insSize rl.ins) := hc0
  have hold : pcOwn X' r' Ds i ps Xi = ownSl Xi.v rl.nv.pgid' ++
      (Ds.getD i [] ++ (Ds.drop (i + 1)).flatten) ++ pcSlots (spP Xi) ps := by
    unfold pcOwn; rw [hDs, hA]
  have hnew : pcOwn X' r' Ds (i + 1) (ps ++ [pn]) X3 = (Ds.drop (i + 1)).flatten ++
      (pcSlots (spP Xi) ps ++ (List.range' id.toNat (pcCount (insSize rl.ins)) ++
        Ds.getD i [])) := by
    unfold pcOwn; rw [if_neg (Nat.succ_ne_zero _), hfin]; simp
  have hb62 : ∀ s ∈ ownSl Xi.v rl.nv.pgid', s < 2 ^ 62 := fun s hs' =>
    (hL.slot.2.1 s (List.mem_append_right _ (by
      rw [hold]; exact List.mem_append_left _ (List.mem_append_left _ hs')))).2.1
  have hpend := pcStep_pend hs hb62
  have hmk : X.t.mv.pgid'.toNat ≤ Xi.t.mv.pgid'.toNat := by
    have h1 : X.t.mv.pgid'.toNat ≤ X'.t.mv.pgid'.toNat := by
      rcases hend with ⟨-, rfl, -⟩ | ⟨-, h', es, i', -, hl, -⟩
      · exact Nat.le_refl _
      · exact hl.frame.2.2.2.2.2.2.2.2.1
    have h2 : X2.t.mv = X'.t.mv := by
      rw [hsr.same.1]; unfold WX.nilCh WX.killL; exact setNode_mv _ _ _ _
    have h3 := hL.frame.2.2.2.2.2.2.2.2.1
    rw [h2] at h3; omega
  refine ⟨fun s hs' => ?_, fun s hs' => ?_, fun x hx => ?_⟩
  · rcases hD1 s hs' with h | h
    · rw [hold] at h; rw [hnew]
      simp only [List.mem_append] at h ⊢
      rcases h with (h | h | h) | h
      · exact Or.inr (hpend s (Or.inr h))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr (hpend s (Or.inl h))
  · rw [hnew] at hs'
    simp only [List.mem_append] at hs'
    have hold' : s ∈ pcOwn X' r' Ds i ps Xi →
        s ∈ D ∨ newSlot (st0 ++ stl ++ st') X.t.mv.pgid'.toNat s := by
      intro h
      rcases hD2 s h with h | h
      · exact Or.inl h
      · exact Or.inr (newSlot_mono h (fun y hy => List.mem_append_left _ hy) (Nat.le_refl _))
    rcases hs' with h | h | h | h
    · exact hold' (by rw [hold]; simp [h])
    · exact hold' (by rw [hold]; simp [h])
    · exact Or.inr (newSlot_mono (pcStep_newSlot hs s h)
        (fun y hy => List.mem_append_right _ hy) hmk)
    · exact hold' (by
        rw [hold]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ h)))
  · by_cases hx3 : spP X3 !! x = spP Xi !! x
    · exact hD3 x (by rw [← hx3]; exact hx)
    · have hxe : x = id.toNat := Classical.byContradiction fun hne => hx3 (hPne x hne)
      subst hxe
      intro hm
      rcases hD1 _ hm with h | h
      · rcases hfresh _ (List.mem_append_right _ h) with h1 | h1 <;> omega
      · exact pcStep_id_pend hs hL.slot h

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
