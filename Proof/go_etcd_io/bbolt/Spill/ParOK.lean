/-
`node.spill` (U9w3, `notes/bbolt-proof-plan.md`; pure): **the children's parent pointers**
(`parOK`, `Spill/UTree`) through the spill's steps: a frame whose touched nodes keep them
(`parOK_frame`), a node's record set keeping its parent and not adding children
(`parOK_setNode`, the sort's permutation `parOK_perm`), the kill of `n`'s children (`parOK_nilCh`),
the split (`parOK_split`), the pieces' loop (`parOK_pcLoop`); and what the kill needs of them
(`parOK_uniq`: no other live node has `n`'s children).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section par
variable [GooseExts] [GoGlobalContext]

/-- An untouched node after a frame was a node before. -/
theorem spFrame_node_back {X X' : WX} {bl : Loc} {T : List Loc} (hfr : spFrame X X' bl T)
    {B : BRec} (hB : X.t.bs !! bl = some B) {m : Loc} {r' : NRec} (h' : X'.node bl m = some r')
    (hm : m ∉ T) : ∃ r, X.node bl m = some r := by
  obtain ⟨B', hB', -, hns⟩ := hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B hB
  have := hns m hm
  unfold WX.node at h' ⊢
  rw [hB'] at h'; rw [hB]
  simp only [Option.bind_some] at h' ⊢
  cases e : B.ns !! m with
  | none => rw [e, h'] at this; simp [optRel] at this
  | some r => exact ⟨r, rfl⟩

/-- **The parent pointers through a frame**: the touched live nodes' children point to them, and
an untouched live node's touched children still point to it. -/
theorem parOK_frame {X X' : WX} {bl : Loc} {T : List Loc} (h : parOK X bl)
    (hfr : spFrame X X' bl T) {B : BRec} (hB : X.t.bs !! bl = some B)
    (hT : ∀ l ∈ T, ∀ rl, X'.node bl l = some rl → l ∈ X'.live →
      ∀ c ∈ rl.cs, ∃ rc, X'.node bl c = some rc ∧ rc.nv.parent' = l)
    (hU : ∀ m rm, X.node bl m = some rm → m ∉ T → m ∈ X.live → ∀ c ∈ rm.cs, c ∈ T →
      ∃ rc, X'.node bl c = some rc ∧ rc.nv.parent' = m) :
    parOK X' bl := by
  intro m rm' hm' hlv'
  by_cases hmT : m ∈ T
  · exact hT m hmT rm' hm' hlv'
  · obtain ⟨rm, hm⟩ := spFrame_node_back hfr hB hm' hmT
    obtain ⟨rm2, hm2, hsim, hliv⟩ := spFrame_node hfr hm hmT
    rw [hm'] at hm2; cases hm2
    have hlv : m ∈ X.live := hliv.1 hlv'
    intro c hc
    rw [hsim.2.2.2.2.1] at hc
    by_cases hcT : c ∈ T
    · exact hU m rm hm hmT hlv c hc hcT
    · obtain ⟨rc, hrc, hp⟩ := h m rm hm hlv c hc
      obtain ⟨rc', hrc', hs', -⟩ := spFrame_node hfr hrc hcT
      exact ⟨rc', hrc', by rw [nodeSim_parent hs', hp]⟩

/-- **A node's record set** keeping its parent and adding no children. -/
theorem parOK_setNode {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) (r' : NRec) (hpar : r'.nv.parent' = r.nv.parent')
    (hcs : ∀ c ∈ r'.cs, c ∈ r.cs) : parOK (X.setNode bl n r') bl := by
  have hnode : ∀ l, (X.setNode bl n r').node bl l = if l = n then some r' else X.node bl l := by
    intro l
    by_cases e : l = n
    · subst e; rw [if_pos rfl]; exact WX.setNode_node_same hn r'
    · rw [if_neg e]; exact WX.setNode_node_ne bl r' e
  -- a child's node after, pointing to `m` if it did before
  have hch : ∀ m c rc, X.node bl c = some rc → rc.nv.parent' = m →
      ∃ rc', (X.setNode bl n r').node bl c = some rc' ∧ rc'.nv.parent' = m := by
    intro m c rc hc hp
    by_cases e : c = n
    · subst e; rw [hn] at hc; cases hc
      exact ⟨r', by rw [hnode, if_pos rfl], by rw [hpar, hp]⟩
    · exact ⟨rc, by rw [hnode, if_neg e]; exact hc, hp⟩
  intro m rm' hm' hlv'
  rw [WX.setNode_live] at hlv'
  rw [hnode] at hm'
  intro c hc
  by_cases e : m = n
  · subst e; rw [if_pos rfl] at hm'; cases hm'
    obtain ⟨rc, hrc, hp⟩ := h m r hn hlv' c (hcs c hc)
    exact hch m c rc hrc hp
  · rw [if_neg e] at hm'
    obtain ⟨rc, hrc, hp⟩ := h m rm' hm' hlv' c hc
    exact hch m c rc hrc hp

/-- **The sort of `n`'s children** (a permutation). -/
theorem parOK_perm {X : WX} {bl n : Loc} {rn : NRec} {l : List Loc} (h : parOK X bl)
    (hn : X.node bl n = some rn) (hp : rn.cs.Perm l) :
    parOK (X.setNode bl n { rn with cs := l }) bl :=
  parOK_setNode h hn _ rfl fun c hc => hp.symm.subset hc

/-- Fewer live nodes. -/
theorem parOK_killL {X : WX} {bl : Loc} (h : parOK X bl) (L : List Loc) :
    parOK (X.killL L) bl := by
  intro m rm hm hlv c hc
  rw [killL_node] at hm
  rw [killL_live] at hlv
  obtain ⟨rc, hrc, hp⟩ := h m rm hm hlv.1 c hc
  exact ⟨rc, by rw [killL_node]; exact hrc, hp⟩

/-- **`n.children = nil`**. -/
theorem parOK_nilCh {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) : parOK (X.nilCh bl n r) bl :=
  parOK_killL (parOK_setNode h hn r.nilCh rfl (fun c hc => by simp [NRec.nilCh] at hc)) r.cs

/-- **What the kill of `n`'s children needs**: each is a node of `bl` whose parent is `n` (not
`null`), and no other live node has one of them as a child. -/
theorem parOK_uniq {X : WX} {bl n : Loc} {r : NRec} (h : parOK X bl)
    (hn : X.node bl n = some r) (hlv : n ∈ X.live) :
    (∀ c ∈ r.cs, ∃ rc, X.node bl c = some rc ∧ rc.nv.parent' = n) ∧
    (∀ m rm, X.node bl m = some rm → m ∈ X.live → m ≠ n → ∀ c ∈ rm.cs, c ∉ r.cs) := by
  refine ⟨h n r hn hlv, fun m rm hm hmlv hne c hc hcn => hne ?_⟩
  obtain ⟨rc, hrc, hp⟩ := h m rm hm hmlv c hc
  obtain ⟨rc', hrc', hp'⟩ := h n r hn hlv c hcn
  rw [hrc] at hrc'; cases hrc'
  rw [← hp, hp']

/-- The split's pieces: childless, under `pl`. -/
theorem split_pieces {X1 X2 : WX} {bl n : Loc} {rN : NRec} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {rp' : NRec}
    (hsr : splitRel0 X1 X2 bl n rN xs wss pl rp') (hcs0 : rN.cs = []) :
    ∀ x ∈ xs, ∃ rx, X2.node bl x.1 = some rx ∧ rx.cs = [] ∧ rx.nv.parent' = pl ∧
      x.2.1.parent' = pl := by
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  have hil : i < wss.length := by rw [hsr.len]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hnd, -, -, -, -, -, hp, -, -⟩ := hsr.prec i x _ hi (List.getElem?_eq_getElem hil)
  refine ⟨_, hnd, ?_, ?_, hp⟩
  · unfold splitRec; split <;> simp [hcs0]
  · unfold splitRec; split <;> exact hp

/-- **The split** of `n` (record `rN`, childless after the kill). -/
theorem parOK_split {X1 X2 : WX} {bl n : Loc} {rN : NRec} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {rp' : NRec} (h : parOK X1 bl)
    (hsr : splitRel0 X1 X2 bl n rN xs wss pl rp') (hn : X1.node bl n = some rN) (hcs0 : rN.cs = [])
    (hnull1 : X1.node bl null = none) (hnull2 : X2.node bl null = none) : parOK X2 bl := by
  obtain ⟨B, hB, -⟩ := node_bs_of hn
  have hpc := split_pieces hsr hcs0
  have hmemT : ∀ l, l ∈ xs.map (·.1) ++ [pl] ↔ (∃ x ∈ xs, x.1 = l) ∨ l = pl := by
    intro l; simp
  -- a node of `X1` pointing to `pl`, after (in the case of an existing parent)
  have hkeep : ∀ rp, X1.node bl pl = some rp →
      rp' = { rp with nv := { rp.nv with children' := rp'.nv.children' },
                      cs := rp.cs ++ (xs.drop 1).map (·.1) } → X2.node bl pl = some rp' →
      ∀ c rc, X1.node bl c = some rc → rc.nv.parent' = pl →
      ∃ rc', X2.node bl c = some rc' ∧ rc'.nv.parent' = pl := by
    intro rp hrp hrpe hrp2 c rc hc hp
    by_cases hcx : ∃ x ∈ xs, x.1 = c
    · obtain ⟨x, hx, rfl⟩ := hcx
      obtain ⟨rx, h1, -, h2, -⟩ := hpc x hx
      exact ⟨rx, h1, h2⟩
    · by_cases hcp : c = pl
      · subst hcp; rw [hrp] at hc; cases hc
        exact ⟨_, hrp2, by rw [hrpe]; exact hp⟩
      · obtain ⟨rc', h1, h2, -⟩ := spFrame_node hsr.frame hc (by rw [hmemT]; exact fun h' => h'.elim hcx hcp)
        exact ⟨rc', h1, by rw [nodeSim_parent h2, hp]⟩
  refine parOK_frame h hsr.frame hB ?_ ?_
  · intro l hl rl hrl hlv c hc
    by_cases hlx : ∃ x ∈ xs, x.1 = l
    · obtain ⟨x, hx, rfl⟩ := hlx
      obtain ⟨rx, h1, h2, -⟩ := hpc x hx
      rw [h1] at hrl; cases hrl; rw [h2] at hc; cases hc
    · have hlp : l = pl := by rw [hmemT] at hl; exact hl.resolve_left hlx
      subst hlp
      rcases hsr.par with ⟨-, -, rfl⟩ | ⟨-, -, -, -, hrpe, h2, -⟩ | ⟨-, -, rp, hrp, hrpe, h2, hlv'⟩
      · rw [hnull2] at hrl; cases hrl
      · rw [h2] at hrl; cases hrl
        rw [hrpe] at hc
        simp only [newParRec, List.mem_map] at hc
        obtain ⟨x, hx, rfl⟩ := hc
        obtain ⟨rx, h1, -, h3, -⟩ := hpc x hx
        exact ⟨rx, h1, h3⟩
      · rw [h2] at hrl; cases hrl
        rw [hrpe] at hc
        simp only [List.mem_append, List.mem_map] at hc
        rcases hc with hc | ⟨x, hx, rfl⟩
        · obtain ⟨rc, hrc, hp⟩ := h l rp hrp (hlv'.1 hlv) c hc
          exact hkeep rp hrp hrpe h2 c rc hrc hp
        · obtain ⟨rx, h1, -, h3, -⟩ := hpc x (List.mem_of_mem_drop hx)
          exact ⟨rx, h1, h3⟩
  · intro m rm hm hmT hlv c hc hcT
    obtain ⟨rc, hrc, hp⟩ := h m rm hm hlv c hc
    have hmn : m ≠ null := by intro e; rw [e, hnull1] at hm; cases hm
    rw [hmemT] at hcT
    rcases hcT with ⟨x, hx, rfl⟩ | rfl
    · -- a piece: `n` (the others are fresh)
      have hxn : x.1 = n := by
        have hne := hsr.ne
        have hhd := hsr.head
        cases e : xs with
        | nil => exact absurd e hne
        | cons x0 rest =>
          rw [e] at hhd hx
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact hhd
          · have h1 := hsr.fresh x (by rw [e]; exact hx')
            have h2 := node_objs hrc
            rw [h1] at h2; cases h2
      rw [hxn, hn] at hrc; cases hrc
      obtain ⟨rx, h1, -, h3, -⟩ := hpc x hx
      refine ⟨rx, h1, ?_⟩
      rw [h3]
      rcases hsr.par with ⟨h0, -, -⟩ | ⟨h0, -⟩ | ⟨-, rfl, -⟩
      · exact absurd (hp.symm.trans h0) hmn
      · exact absurd (hp.symm.trans h0) hmn
      · exact hp
    · rcases hsr.par with ⟨-, -, rfl⟩ | ⟨-, -, -, h0, -⟩ | ⟨-, -, rp, hrp, hrpe, h2, -⟩
      · rw [hnull1] at hrc; cases hrc
      · have h1 := node_objs hrc; rw [h0] at h1; cases h1
      · rw [hrp] at hrc; cases hrc
        exact ⟨_, h2, by rw [hrpe]; exact hp⟩

/-- The pieces at iteration `i` of their loop: childless, under `pl`. -/
theorem pcLoop_pieces {X' X2 Xi : WX} {r' rp0 : NRec} {w2 wi : WDb} {bl pl : Loc} {O : List Nat}
    {lo hi : Option (List w8)} {h0 : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {i : Nat} {ps : List Piece} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O lo hi h0 xs wss pl rp0 bs j Es Ds i ps Xi wi stl)
    (hlen : wss.length = xs.length) (hpx : ∀ x ∈ xs, x.2.1.parent' = pl) :
    ∀ x ∈ xs, ∃ rx, Xi.node bl x.1 = some rx ∧ rx.cs = [] ∧ rx.nv.parent' = pl := by
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
  have hkl : k < wss.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
  by_cases hki : k < i
  · have hkp : k < ps.length := by rw [hL.len]; exact hki
    obtain ⟨rk, h1, -, -, -, h2, -, h3, -⟩ := hL.done k x _ _ hk (List.getElem?_eq_getElem hkp)
      (List.getElem?_eq_getElem hkl)
    exact ⟨rk, h1, h2, h3⟩
  · obtain ⟨rk, h1, -, hs⟩ := hL.todo k x _ (by omega) hk (List.getElem?_eq_getElem hkl)
    refine ⟨rk, h1, ?_, ?_⟩
    · rw [hs.2.2.2.2.1]; unfold splitRec; split <;> simp [NRec.nilCh]
    · rw [nodeSim_parent hs]; unfold splitRec; split <;> exact hpx x hx

/-- **The pieces' loop** (from the split's state `X2`, the parent's record `rp0` there). -/
theorem parOK_pcLoop {X' X2 Xi : WX} {r' rp0 : NRec} {w2 wi : WDb} {bl pl : Loc} {O : List Nat}
    {lo hi : Option (List w8)} {h0 : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {i : Nat} {ps : List Piece} {stl : List FLStep} (h : parOK X2 bl)
    (hL : pcLoop X' r' X2 w2 bl O lo hi h0 xs wss pl rp0 bs j Es Ds i ps Xi wi stl)
    {B : BRec} (hB : X2.t.bs !! bl = some B)
    (hlen : wss.length = xs.length) (hpx : ∀ x ∈ xs, x.2.1.parent' = pl)
    (hp2 : ∀ x ∈ xs, ∃ rx, X2.node bl x.1 = some rx ∧ rx.nv.parent' = pl)
    (hrp0 : pl ≠ null → X2.node bl pl = some rp0 ∧ pl ∈ X2.live)
    (hnull : X2.node bl null = none) (hnulli : Xi.node bl null = none) : parOK Xi bl := by
  have hpc := pcLoop_pieces hL hlen hpx
  have hmemT : ∀ l, l ∈ xs.map (·.1) ++ [pl] ↔ (∃ x ∈ xs, x.1 = l) ∨ l = pl := by
    intro l; simp
  refine parOK_frame h hL.frame hB ?_ ?_
  · intro l hl rl hrl hlv c hc
    by_cases hlx : ∃ x ∈ xs, x.1 = l
    · obtain ⟨x, hx, rfl⟩ := hlx
      obtain ⟨rx, h1, h2, -⟩ := hpc x hx
      rw [h1] at hrl; cases hrl; rw [h2] at hc; cases hc
    · have hlp : l = pl := by rw [hmemT] at hl; exact hl.resolve_left hlx
      subst hlp
      have hpn : l ≠ null := by intro e; rw [e, hnulli] at hrl; cases hrl
      obtain ⟨hrp, hplv⟩ := hrp0 hpn
      obtain ⟨rpi, h1, -, -, -, -, -, -, h2, h3, -⟩ := hL.par hpn
      rw [h1] at hrl; cases hrl
      rw [h2] at hc
      obtain ⟨rc, hrc, hp⟩ := h l rp0 hrp hplv c hc
      by_cases hcx : ∃ x ∈ xs, x.1 = c
      · obtain ⟨x, hx, rfl⟩ := hcx
        obtain ⟨rx, h4, -, h5⟩ := hpc x hx
        exact ⟨rx, h4, h5⟩
      · by_cases hcp : c = l
        · subst hcp; rw [hrp] at hrc; cases hrc
          exact ⟨_, h1, by rw [h3]; exact hp⟩
        · obtain ⟨rc', h4, h5, -⟩ := spFrame_node hL.frame hrc (by rw [hmemT]; exact fun h' => h'.elim hcx hcp)
          exact ⟨rc', h4, by rw [nodeSim_parent h5, hp]⟩
  · intro m rm hm hmT hlv c hc hcT
    obtain ⟨rc, hrc, hp⟩ := h m rm hm hlv c hc
    rw [hmemT] at hcT
    rcases hcT with ⟨x, hx, rfl⟩ | rfl
    · obtain ⟨rx, h1, h2⟩ := hp2 x hx
      rw [h1] at hrc; cases hrc
      exact absurd (by rw [hmemT]; right; exact hp.symm.trans h2) hmT
    · have hpn : c ≠ null := by intro e; rw [e, hnull] at hrc; cases hrc
      obtain ⟨hrp, -⟩ := hrp0 hpn
      obtain ⟨rpi, h1, -, -, -, -, -, -, -, h3, -⟩ := hL.par hpn
      rw [hrp] at hrc; cases hrc
      exact ⟨rpi, h1, by rw [h3]; exact hp⟩

end par

end Spill

end bbolt
end EtcdGrove
end Perennial
