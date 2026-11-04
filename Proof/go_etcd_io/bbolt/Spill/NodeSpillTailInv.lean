/-
`node.spill` after its children's loop (U9s, `notes/bbolt-proof-plan.md`; pure): **the pieces'
loop's invariant** (`pcInv`) and the facts `Spill/NodeSpillTailWp.spillTail_gen` takes of it
(`tail_pre`, `pcInv_init`, `pcInv_pre`, `pcInv_step`, `pcInv_err`, `pcInv_end`, `pcInv_done`,
`pcInv_top`), which `Spill/NodeSpillPieces.spillTail_wp` passes it.

The invariant, at iteration `i` of the loop over the split's pieces `xs` (under the parent `pl`),
relative to the spill's start `(X, w)` (`n`'s record `rn`) through the state after the children's
loop (`spEnd`: `X'`, `n`'s record `r'`) and the split (`splitRel`: `X2`, the pieces' entries
`wss`, the parent's record `rp0`): the pieces before `i` written (`ps`: each a spilled childless
node at its page, a finished subtree from its first key, `Es k` its leaf elements), the rest as
the split left them (modulo sources), the parent's entries the base's (the parent's at the start,
or none for a new root) with the done pieces' spliced in at `j`, the slots owned (`O`, the rest's
child slots `Ds`, `n`'s page until it is freed, the done pieces' trees), the spill's step and
frame from `X2`, and the page map changed only at the done pieces' pages.

The lemmas are stated over `pcInv` only through `spillTail_gen`'s interface, so `pcInv`'s fields
can be changed without touching the WP.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDefs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesKill
public import Proof.go_etcd_io.bbolt.Spill.SplitModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section inv
variable [GooseExts] [GoGlobalContext]

/-- The first key of piece `k` (its entries `wss[k]`'s first). -/
def wssKey (wss : List (List WEntry)) (k : Nat) : List w8 := wKey ((wss[k]?).getD []) 0

/-- **The parent's entries** after `i` pieces of a node at entry `j` of the base `bs` are done
(`ps`): the base until the first piece's put, then entry `j` replaced by the pieces'. -/
def parWs (bs : List WEntry) (j i : Nat) (ps : List Piece) : List (w32 × w64 × List w8 × List w8) :=
  if i = 0 then bs.map wDat
  else (bs.take j).map wDat ++ ps.map pcDat ++ (bs.drop (j + 1)).map wDat

/-- **The pieces' loop's state** (see the module doc) after the split, from `(X2, w2)`. -/
structure pcLoop (X' : WX) (r' : NRec) (X2 : WX) (w2 : WDb) (bl : Loc) (O : List Nat)
    (hi : Option (List w8)) (h0 : Nat) (xs : List (Loc × node × List Inode))
    (wss : List (List WEntry)) (pl : Loc) (bs : List WEntry) (j : Nat)
    (Es : List (List El)) (Ds : List (List Nat)) (i : Nat) (ps : List Piece) (Xi : WX)
    (wi : WDb) (stl : List FLStep) : Prop where
  len : ps.length = i
  ile : i ≤ xs.length
  pcl : ∀ (k : Nat) (p : Piece) (x : Loc × node × List Inode), ps[k]? = some p → xs[k]? = some x → p.l = x.1
  Elen : Es.length = xs.length
  Dlen : Ds.length = xs.length
  step : spStep X2 Xi w2 wi O stl
  frame : spFrame X2 Xi bl (xs.map (·.1) ++ [pl])
  todo : ∀ (k : Nat) (x : Loc × node × List Inode) (ws : List WEntry), i ≤ k → xs[k]? = some x → wss[k]? = some ws → ∃ rk,
    Xi.node bl x.1 = some rk ∧ x.1 ∈ Xi.live ∧
    nodeSim (splitRec r'.nilCh x ws (decide (k = 0)) (decide (xs.length = 1))) rk
  done : ∀ (k : Nat) (x : Loc × node × List Inode) (p : Piece) (ws : List WEntry), xs[k]? = some x → ps[k]? = some p → wss[k]? = some ws → ∃ rk,
    Xi.node bl x.1 = some rk ∧ x.1 ∈ Xi.live ∧ rk.nv.bucket' = bl ∧ rk.nv.spilled' = true ∧
    rk.cs = [] ∧ rk.nv.children' = slice.nil ∧ rk.nv.parent' = pl ∧ rk.nv.pgid' = p.id ∧ rk.ws.map wDat = ws.map wDat ∧
    p.k = wssKey wss k ∧ (pl ≠ null → rk.key = p.k ∧ rk.nv.key' ≠ slice.nil) ∧
    fTree (spP Xi) Xi.t.mv.pgid'.toNat p.id.toNat p.k (childHi hi (wssKey wss) xs.length k) h0
      p.S (Es.getD k [])
  slot : slotInv wi.fl Xi.t.mv.pgid'.toNat
    (O ++ ((if i = 0 then ownSl X'.v r'.nv.pgid' else []) ++ (Ds.drop i).flatten ++
      pcSlots (spP Xi) ps))
  agree : ∀ x : Nat, spP Xi !! x ≠ spP X' !! x → ∃ p ∈ ps, x = p.id.toNat
  par : pl ≠ null → ∃ rpi, Xi.node bl pl = some rpi ∧ pl ∈ Xi.live ∧ pl ∉ xs.map (·.1) ∧
    rpi.capOwn = true ∧ wsSorted rpi.ws ∧ rpi.ws.map wDat = parWs bs j i ps ∧
    rpi.ins.length = rpi.ws.length

/-- **The pieces' loop's invariant** (see the module doc): `n`'s spill from `(X, w)` (as
`node.spill.spec'`), at iteration `i` over the pieces `xs` under `pl`, at `(Xi, wi)` after the
steps `st` from `w`. -/
def pcInv (X : WX) (w : WDb) (bl n : Loc) (rn : NRec) (O : List Nat) (lo hi : Option (List w8))
    (h : Nat) (D : List Nat) (N : List Loc) (E : List El) (cs : SpCase)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) : Prop :=
  ∃ (X' : WX) (w' : WDb) (r' : NRec) (st0 : List FLStep) (T : List Loc) (X2 : WX)
    (wss : List (List WEntry)) (rp0 : NRec) (bs : List WEntry) (j h0 : Nat) (Es : List (List El))
    (Ds : List (List Nat)) (ps : List Piece) (stl : List FLStep),
    spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T ∧ insLens r'.ins r'.ws ∧
    splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0 ∧
    (∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) ∧
    st = st0 ++ stl ∧ Es.flatten = E ∧
    (∀ s ∈ D, s ∈ ownSl X'.v r'.nv.pgid' ++ Ds.flatten ∨ s ∈ pendSlots w'.fl) ∧
    (match cs with
     | .child pl' rp j' _ _ => pl = pl' ∧ j = j' ∧ bs.map wDat = rp.ws.map wDat
     | .top => bs = [] ∧ j = 0) ∧
    pcLoop X' r' X2 w' bl O hi h0 xs wss pl bs j Es Ds i ps Xi wi stl

end inv

section lemmas
variable [GooseExts] [GoGlobalContext]

/-- The children's loop's database facts (the committed state, the freelist, the base pages). -/
theorem spEnd_db {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc} {E : List El}
    {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧ X'.v.pages = X.v.pages := by
  rcases hend with ⟨-, rfl, rfl, -, rfl, -⟩ | ⟨-, h', es, i, -, hl, -⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨hl.step.1, hl.step.2.1, hl.step.2.2.1⟩

theorem nilCh_v (X : WX) (bl n : Loc) (r : NRec) : (X.nilCh bl n r).v = X.v := by
  unfold WX.nilCh WX.killL; exact WX.setNode_v _ _ _ _

/-- The database facts of the steps before iteration `i`. -/
theorem pcInv_db {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {xs : List (Loc × node × List Inode)} {pl : Loc} {i : Nat} {Xi : WX}
    {wi : WDb} {st : List FLStep}
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) :
    wi.C = w.C ∧ wi.fl = w.fl.applySteps w.wtxid st ∧ Xi.v.pages = X.v.pages := by
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, h0, Es, Ds, ps, stl, hend, -, hsr, -, rfl, -, -,
    -, hL⟩ := hI
  obtain ⟨hC, hfl, hpg⟩ := spEnd_db hend
  obtain ⟨hC2, hfl2, hpg2, -⟩ := hL.step
  refine ⟨hC2.trans hC, ?_, ?_⟩
  · rw [hfl2, wtxid_of_C hC, hfl, applySteps_append]
  · rw [hpg2, hsr.same.2.2.2, nilCh_v, hpg]

/-- **The size bound of `n`'s inodes** (`splitStep_wp`'s `hsz`). Open (U9s): nothing bounds the
number of a node's inodes, so `insSize` (each inode at most `16 + bboltEntryMax`) has no bound
below `2 ^ 63` from the spill's pre; a shared-statement question (see U9s's report). -/
theorem tail_insSize {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    insSize r'.ins < 2 ^ 63 := by
  sorry

theorem killL_node (X : WX) (L : List Loc) (bl l : Loc) : (X.killL L).node bl l = X.node bl l :=
  rfl

/-- The unspilled root of a tree is no child of its own. -/
theorem uTree_not_own_child {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {rn : NRec} (hut : uTree X bl P hwm n lo hi h F D N E) (hn : X.node bl n = some rn)
    (hsp : rn.nv.spilled' = false) : n ∉ rn.cs := by
  intro hm
  cases e : rn.nv.isLeaf' with
  | true =>
    cases hut with
    | leaf _ r' _ _ _ hr _ _ hcs => rw [hn] at hr; cases hr; rw [hcs] at hm; cases hm
    | branch _ r' _ _ _ _ hr _ hl => rw [hn] at hr; cases hr; rw [e] at hl; cases hl
  | false =>
  obtain ⟨h1, es, -, -, -, -, -, hb⟩ := uBr_of_uTree hut hn e
  rcases hb.cs n hm with ⟨e, he, hec⟩ | ⟨-, rc, hrc, -, hsp', -⟩
  · obtain ⟨j, Fc, Dc, Nc, Ec, hj, -⟩ := uBr_ch_unspilled hb he hec
    have hjl : j < rn.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hent := hb.ent j _ _ (List.getElem?_eq_getElem hjl) hj
    cases hent with
    | child _ _ _ _ _ _ _ _ _ rc _ _ _ _ hcm hrc hpar hpg hkey hknil hne hut' =>
      exact (List.nodup_cons.1 hb.Nnd).1
        (List.mem_flatMap.2 ⟨_, List.mem_of_getElem? hj, uTree_head hut'⟩)
  · rw [hn] at hrc; cases hrc; rw [hsp] at hsp'; cases hsp'

/-- `n`'s record after the children's loop: an unspilled node, its struct but the slices as at
the start, its children its own or fresh ones; the frame. -/
theorem spEnd_rec {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    X'.node bl n = some r' ∧ n ∈ X'.live ∧ uNode X' bl n r' lo hi ∧
    r'.nv = { rn.nv with inodes' := r'.nv.inodes', children' := r'.nv.children',
                         key' := r'.nv.key' } ∧ r'.capOwn = rn.capOwn ∧
    (∀ c ∈ r'.cs, c ∈ rn.cs ∨ X.t.objs !! c = none) ∧ spFrame X X' bl (N ++ T) ∧
    (∀ l ∈ T, X.t.objs !! l = none) := by
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, -, -, -⟩
  · rw [hsp] at hs; cases hs
  rcases hend with ⟨hleaf, hX, -, hr, -, hT⟩ | ⟨hleaf, h', es, i, -, hl, -, hch⟩
  · have hun : uNode X bl n rn lo hi := by
      cases hut with
      | leaf _ r'' _ _ _ hr' hu => rw [hn] at hr'; cases hr'; exact hu
      | branch _ r'' _ _ _ _ hr' hu => rw [hn] at hr'; cases hr'; exact hu
    rw [hX, hr, hT]
    exact ⟨hn, hun.1, hun, rfl, rfl, fun c hc => Or.inl hc, spFrame_refl _ _ _,
      fun _ hl => absurd hl List.not_mem_nil⟩
  · exact ⟨hl.br.node, hl.live, hl.br.un, hl.nv, hl.cap,
      fun c hc => (hch c hc).imp_right (hl.fresh c), hl.frame, hl.fresh⟩

/-- `n`'s entries after the children's loop hold no stale bytes (`liveFresh`). -/
theorem tail_wsLive {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) : wsLive r'.ws := by
  obtain ⟨hn', hlv', -⟩ := spEnd_rec hpre hsp hend
  have hlf : liveFresh X' := by
    rcases hend with ⟨-, hX, -, -, -, -⟩ | ⟨-, h', es, i, -, hl, -⟩
    · rw [hX]; exact hpre.2.1.2.2.2.1
    · exact hl.step.2.2.2.1.2.2.2.1
  obtain ⟨B, HB, Hr⟩ := node_bs_of hn'
  exact (hlf bl B n r' HB Hr hlv').1

/-- **What the steps before the loop need** (`spillTail_gen`'s `hn'`, `hlv'`, `hS`); the size
bound is `tail_insSize`. -/
theorem tail_pre {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) :
    X'.node bl n = some r' ∧ n ∈ X'.live ∧
    ((X'.nilCh bl n r').node bl n = some r'.nilCh ∧ n ∈ (X'.nilCh bl n r').live ∧
      r'.nilCh.nv.bucket' = bl ∧ r'.nilCh.capOwn = true ∧ r'.nilCh.nv.spilled' = false ∧
      r'.nilCh.ins.length = r'.nilCh.ws.length ∧ insSize r'.nilCh.ins < 2 ^ 63 ∧
      (r'.nilCh.nv.parent' ≠ null → ∃ rp,
        (X'.nilCh bl n r').node bl r'.nilCh.nv.parent' = some rp ∧
        r'.nilCh.nv.parent' ∈ (X'.nilCh bl n r').live)) := by
  have hsz := tail_insSize hpre hsp hend
  obtain ⟨hn', hlv', hun', hnv, hcap, hcs', hfr, hT⟩ := spEnd_rec hpre hsp hend
  obtain ⟨hn, -, hc⟩ := hpre
  rcases hc with ⟨hs, -⟩ | ⟨hut, hctx, -, -⟩
  · rw [hsp] at hs; cases hs
  have hnN : n ∈ N := uTree_head hut
  have hnot : n ∉ r'.cs := by
    intro hm
    rcases hcs' n hm with hm | hm
    · exact uTree_not_own_child hut hn hsp hm
    · rw [node_none_of_objs hm] at hn; cases hn
  have hspl : r'.nv.spilled' = false := by rw [hnv]; exact hsp
  refine ⟨hn', hlv', ?_, ?_, hun'.2.1, hun'.2.2.2.1, hspl, hun'.2.2.2.2.1, hsz, ?_⟩
  · unfold WX.nilCh; rw [killL_node]; exact WX.setNode_node_same hn' _
  · unfold WX.nilCh; rw [killL_live, WX.setNode_live]; exact ⟨hlv', hnot⟩
  · intro hpn
    have hpar : r'.nilCh.nv.parent' = rn.nv.parent' := by
      show r'.nv.parent' = rn.nv.parent'; rw [hnv]
    rw [hpar] at hpn ⊢
    cases cs with
    | top => exact absurd hctx.1 hpn
    | child pl rp j plo phi =>
      obtain ⟨hpl, -, hplN, hrp, hunp, -, -, -, -, -, -, -, hcsN⟩ := hctx
      rw [hpl]
      have hplT : pl ∉ N ++ T := by
        intro hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hplN hm
        · rw [node_none_of_objs (hT pl hm)] at hrp; cases hrp
      obtain ⟨rp', hrp', -, hliv⟩ := spFrame_node hfr hrp hplT
      have hne : pl ≠ n := fun he => hplN (he ▸ hnN)
      refine ⟨rp', ?_, ?_⟩
      · unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ hne]; exact hrp'
      · unfold WX.nilCh; rw [killL_live, WX.setNode_live]
        refine ⟨hliv.2 hunp.1, fun hm => ?_⟩
        rcases hcs' pl hm with hm | hm
        · exact hplN (hcsN pl hm)
        · rw [node_none_of_objs hm] at hrp; cases hrp

/-- **The invariant at the loop's start**, after the split. -/
theorem pcInv_init {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) (hlens : insLens r'.ins r'.ws)
    (X2 : WX) (xs : List (Loc × node × List Inode)) (wss : List (List WEntry)) (pl : Loc)
    (rp' : NRec) (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp')
    (hfit : ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl 0 X2 w' st := by
  sorry

/-- **A piece's premises** (`pieceOne_wp`'s) at iteration `i`. -/
theorem pcInv_pre {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) (x : Loc × node × List Inode)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) (hx : xs[i]? = some x) :
    ∃ rl, Xi.node bl x.1 = some rl ∧ pcPre Xi wi bl x.1 rl := by
  sorry

/-- **A piece's step** keeps the invariant. -/
theorem pcInv_step {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) (x : Loc × node × List Inode) (rl : NRec) (X3 : WX) (w2 : WDb)
    (st' : List FLStep) (id : w64)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) (hx : xs[i]? = some x)
    (hrl : Xi.node bl x.1 = some rl)
    (hs : pcStep Xi wi bl x.1 rl (pcCount (insSize rl.ins)) X3 w2 st' id) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl (i + 1) X3 w2 (st ++ st') := by
  sorry

/-- **An error at iteration `i`**: the error's facts from the spill's start. -/
theorem pcInv_err {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX)
    (wi : WDb) (st : List FLStep) (X'' : WX) (w'' : WDb) (st' : List FLStep)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st)
    (he : w''.C = wi.C ∧ w''.fl = wi.fl.applySteps wi.wtxid st' ∧ X''.v.pages = Xi.v.pages) :
    w''.C = w.C ∧ w''.fl = w.fl.applySteps w.wtxid (st ++ st') ∧ X''.v.pages = X.v.pages := by
  obtain ⟨hC, hfl, hpg⟩ := pcInv_db hI
  refine ⟨he.1.trans hC, ?_, he.2.2.trans hpg⟩
  rw [he.2.1, wtxid_of_C hC, hfl, applySteps_append]

/-- **The loop's end**: `n`'s record, its parent the pieces'. -/
theorem pcInv_end {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (xs : List (Loc × node × List Inode)) (pl : Loc) (Xf : WX) (wf : WDb)
    (st : List FLStep) (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl xs.length Xf wf st) :
    ∃ rf, Xf.node bl n = some rf ∧ n ∈ Xf.live ∧ rf.nv.parent' = pl ∧
      rf.nv.children' = slice.nil ∧ rf.cs = [] ∧
      (pl ≠ null → ∃ rp, Xf.node bl pl = some rp ∧ pl ∈ Xf.live) := by
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, h0, Es, Ds, ps, stl, hend, -, hsr, -, -, -, -,
    -, hL⟩ := hI
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 := by
    cases e : xs with
    | nil => exact absurd e hsr.ne
    | cons a _ => exact ⟨a, rfl⟩
  have hx0n : x0.1 = n := by
    have := hsr.head; rw [List.head?_eq_getElem?, hx0] at this; simpa using this
  have hlen0 : 0 < xs.length := (List.getElem?_eq_some_iff.1 hx0).1
  obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hL.len]; exact hlen0)⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, wss[0]? = some w0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hlen0)⟩
  obtain ⟨rk, hrk, hlv, -, -, hcs, hch, hpar, -⟩ := hL.done 0 x0 p0 w0 hx0 hp0 hw0
  rw [hx0n] at hrk hlv
  refine ⟨rk, hrk, hlv, hpar, hch, hcs, fun hpl => ?_⟩
  obtain ⟨rpi, hrpi, hplv, -⟩ := hL.par hpl
  exact ⟨rpi, hrpi, hplv⟩

/-- **The post without a new root** (the child case, or an unsplit top node). -/
theorem pcInv_done {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (Xf : WX) (wf : WDb) (st : List FLStep)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl xs.length Xf wf st)
    (hc : pl = null ∨ ∃ rp, Xf.node bl pl = some rp ∧ rp.nv.pgid' ≠ W64 0) :
    spDone X Xf w wf bl n rn O lo hi h D N E cs st := by
  sorry

/-- **The new root's spill** (a top node split in two or more): its pre, and its success giving
`n`'s. -/
theorem pcInv_top {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (Xf : WX) (wf : WDb) (st : List FLStep)
    (rp : NRec) (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl xs.length Xf wf st)
    (hpl : pl ≠ null) (hrp : Xf.node bl pl = some rp) (hpg : rp.nv.pgid' = W64 0) :
    ∃ h2 F2 D2 N2, spPre Xf wf bl pl rp O lo hi h2 F2 D2 N2 E .top ∧
      ∀ Xg wg st2, spDone Xf Xg wf wg bl pl rp O lo hi h2 D2 N2 E .top st2 →
        spDone X Xg w wg bl n rn O lo hi h D N E cs (st ++ st2) := by
  sorry

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
