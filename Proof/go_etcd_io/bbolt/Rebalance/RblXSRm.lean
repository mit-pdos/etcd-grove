/-
`rblX` through an empty leaf's removal (U8b, `Rebalance/RblXSteps.lean`'s `rblX_rm`): the bucket
step `rbl_rm`, the tree `rm_tree`, the freelist `flView_free`, the reached nodes (no path from the
root passes through the leaf, which has no children), assembled by `rblX_kill`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSKill
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSFl
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSFree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rm
variable [GooseExts]

/-- A path that avoids a childless node `n` survives its removal. -/
theorem descIn_drop (B B' : BRec) (n : Loc) (hnc : ∀ rn, B.ns !! n = some rn → rn.cs = [])
    (hk : ∀ a ra, B.ns !! a = some ra → a ≠ n → ∃ ra', B'.ns !! a = some ra' ∧
      ∀ c ∈ ra.cs, c ≠ n → c ∈ ra'.cs) :
    ∀ a d, descIn B a d → d ≠ n → descIn B' a d := by
  intro a d h
  induction h with
  | self x => intro _; exact descIn.self x
  | child a c d ra ha hc hd ih =>
    intro hdn
    have han : a ≠ n := by intro he; subst he; rw [hnc ra ha] at hc; cases hc
    have hcn : c ≠ n := by
      intro he; subst he
      cases hd with
      | self => exact hdn rfl
      | child _ c' _ rc hrc hc' _ => rw [hnc rc hrc] at hc'; cases hc'
    obtain ⟨ra', ha', hcs⟩ := hk a ra ha han
    exact descIn.child a c d ra' ha' (hcs c hc hcn) (ih hdn)

theorem rootEnts_of_leaves (X X' : WX) (hrl : X'.rl = X.rl)
    (h : (X'.leaves X.rl).flatten = (X.leaves X.rl).flatten) : rootEnts X' = rootEnts X := by
  unfold rootEnts; rw [flatMap_filterMap_flatten, flatMap_filterMap_flatten, hrl, h]

theorem rblX_rm' (X : WX) (fl : FLPg) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (pl : Loc)
    (rp : NRec) (i : Nat) (w : WEntry) (sI sC : GoSlice) (pg : List w8)
    (hI : rblX X fl bl (some n)) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hleaf : r.nv.isLeaf' = true) (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null)
    (hrp : B.ns !! pl = some rp) (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid')
    (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) :
    rblX (X.kill bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) bl (some pl) ∧
    rblRel X fl (X.kill bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)) n
        { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg)) X.t.mv.txid' ∧
    r.nv.pgid' ≠ W64 0 ∧ 2 ≤ rp.ws.length := by
  have hI' := hI
  obtain ⟨⟨-, -, -, htx, -⟩, hBk, -, -, -, -, -, hLR, hFV, hU, hX, hPL, -⟩ := hI'
  obtain ⟨hrb, -, -, hrt, hlive⟩ := hBk bl B hb
  rw [if_pos rfl] at hrb
  have hrb' := hrb
  obtain ⟨hc, ⟨bnd, hk⟩, -, -⟩ := hrb'
  obtain ⟨hB', hent, hlook, hpl', h2⟩ :=
    rbl_rm X.v _ bl B n r pl rp i w sI sC hrb hr hleaf hemp hpl hpn hrp hw hwp
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpgne, hnotp, honly, hnd, h0⟩ :=
    rm_basic X.v _ bl B n r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hp0 : r.nv.pgid' ≠ W64 0 := by
    intro he; have := (hc.2.2.2.2.2.2.2.1 n r hr).2.2.2.2.2.2.2.2.2.1 h0
    cases this with
    | page _ _ h2' _ _ _ _ _ => rw [he] at h2'; simp at h2'
  obtain ⟨pg', hpg', -, -, -, hcan⟩ := rblX_canFree' X fl bl (some n) B n r hI hb hr hp0
  rw [hpg] at hpg'; cases hpg'
  -- names
  have hrp'v : (rmParent rp i n sI sC).nv.pgid' = rp.nv.pgid' := rfl
  have hk2 : ∀ y ry', (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).ns !! y = some ry' →
      y ≠ n ∧ ∃ ry, B.ns !! y = some ry ∧ ry'.nv.pgid' = ry.nv.pgid' := by
    intro y ry' hy
    rcases hlook y ry' hy with rfl | ⟨hyn, hy'⟩
    · rw [hpl'] at hy; cases hy
      exact ⟨fun h => hnlpl h.symm, rp, hrp, rfl⟩
    · exact ⟨hyn, ry', hy', rfl⟩
  have hk3 : ∀ y ry, B.ns !! y = some ry → y ≠ n →
      ((rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).ns !! y).isSome = true := by
    intro y ry hy hyn
    by_cases hyp : y = pl
    · rw [rm_ns, if_pos hyp]; rfl
    · rw [rm_ns, if_neg hyp, if_neg hyn, hy]; rfl
  have hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null := hk.2.1
  obtain ⟨hrt', hlv, hpos1, hpos2⟩ :=
    rm_tree X bl B n r pl rp i w sI sC hb hc hroot hr hleaf hemp hpl hpn hrp hw hwp hrt
  -- the node's position
  obtain ⟨rt, hrtI, hdI⟩ := hLR.2 bl B n r hb hr (hlive n r hr)
  have hE := node_pos X bl B hb hc hroot hrt h0 rt n hrtI hdI r hr
  have hEx := posExtent_node X bl B hb hc h0 n r hr hp0 pg hpg
  let B' := rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)
  let rn : NRec := { r with nv := { r.nv with pgid' := W64 0 } }
  have hdom : ∀ c, ((X.kill bl B' n rn).t.bs !! c).isSome = (X.t.bs !! c).isSome := by
    intro c; rw [kill_look]; split
    · subst c; rw [hb]; rfl
    · rfl
  have hlvx : ((X.kill bl B' n rn).leaves bl).flatten = (X.leaves bl).flatten := by
    rw [kill_leaves]; exact hlv
  have hfl := flView_free X (X.kill bl B' n rn) fl bl r.nv.pgid' (1 + pageOverflow pg)
    X.t.mv.txid' hFV hU rfl hdom (by rw [hb]; simp)
    (fun c hc' => ⟨by rw [kill_positions, setBkt_positions_other X bl B B' hb rfl c hc'],
      by rw [kill_posExtent, setBkt_posExtent_other X bl B' c hc']⟩)
    (fun q hq => hpos1 q (by rw [← kill_positions]; exact hq))
    (fun q hq hqE => by rw [kill_positions]; exact hpos2 q hq hqE)
    (fun q hq => by
      rw [kill_posExtent]
      exact rm_posExtent X bl B n r pl rp i w sI sC hb hc hr hleaf hpl hpn hrp hw hwp q hq)
    hE hEx ⟨pg, hpg⟩
    (by
      apply rootEnts_of_leaves X (X.kill bl B' n rn) rfl
      by_cases hrl : X.rl = bl
      · rw [hrl]; exact hlvx
      · rw [kill_leaves, setBkt_leaves_other X bl B B' hb rfl _ hrl])
    (by
      rw [kill_bktLoc]; funext nm; unfold bktLoc
      show ((X.setBkt bl B').t.bs !! X.rl).bind _ = _
      rw [setBkt_look]; split
      · rename_i h; rw [h, hb]; rfl
      · rfl)
    hcan (hX _ pg hpg) hPL (by omega)
  have hlr : ∀ l r', B'.ns !! l = some r' → l ∈ (X.kill bl B' n rn).live →
      ∃ rt, nodeRootIn B' B'.bv.rootNode' rt ∧ descIn B' rt l := by
    intro l r' hl hll
    obtain ⟨hln, hlx⟩ := (kill_live X bl B' n rn l).1 hll
    obtain ⟨-, ry, hry, -⟩ := hk2 l r' hl
    obtain ⟨rt, hrtI, hd⟩ := hLR.2 bl B l ry hb hry hlx
    have hrte : ∃ rr, rt = B.bv.rootNode' ∧ B.ns !! rt = some rr ∧ rr.nv.parent' = null := by
      cases hrtI with
      | top _ rr hrr hp' => exact ⟨rr, rfl, hrr, hp'⟩
      | up _ _ rr hrr hp' _ => exact absurd (hroot rr hrr) hp'
    obtain ⟨rr, hrt0, hrr, hrrp⟩ := hrte
    have hrtn : rt ≠ n := by
      intro he; rw [he, hr] at hrr; cases hrr; rw [hpl] at hrrp; exact hpn hrrp
    obtain ⟨rr', hrr'⟩ := Option.isSome_iff_exists.1 (hk3 rt rr hrr hrtn)
    have hrr'p : rr'.nv.parent' = null := by
      have := hlook rt rr' hrr'
      rcases this with he | ⟨-, he⟩
      · subst he; rw [hpl'] at hrr'; cases hrr'; rw [hrp] at hrr; cases hrr; exact hrrp
      · rw [hrr] at he; cases he; exact hrrp
    refine ⟨rt, ?_, ?_⟩
    · show nodeRootIn B' B.bv.rootNode' rt
      rw [← hrt0]; exact nodeRootIn.top rt rr' hrr' hrr'p
    · apply descIn_drop B B' n _ _ rt l hd hln
      · intro rn0 hrn0
        rw [hr] at hrn0; cases hrn0
        cases hcs : r.cs with
        | nil => rfl
        | cons c cs =>
          obtain ⟨rc, hrc, hpc⟩ :=
            (hc.2.2.2.2.2.2.2.1 n r hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c (by rw [hcs]; simp)
          exact absurd hpc (hnotp c rc hrc)
      · intro a ra ha han
        by_cases hap : a = pl
        · subst hap; rw [hrp] at ha; cases ha
          refine ⟨rmParent rp i n sI sC, by
            show (rmBkt B n a r.nv.pgid' (rmParent rp i n sI sC)).ns !! a = _
            rw [rm_ns, if_pos rfl], fun c hc' hcn => ?_⟩
          show c ∈ rp.cs.eraseIdx (rp.cs.idxOf n)
          rw [cs_erase]; exact (List.mem_erase_of_ne hcn).2 hc'
        · refine ⟨ra, by
            show (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).ns !! a = _
            rw [rm_ns, if_neg hap, if_neg han]; exact ha, fun c hc' _ => hc'⟩
  obtain ⟨h1, h2'⟩ := rblX_kill X fl bl (some n) (some pl) B B' n rn r.nv.pgid'
    (1 + pageOverflow pg) X.t.mv.txid' hI hb (by rw [hr]; rfl) ⟨rfl, rfl, rfl⟩ hk2
    (fun y ry' hy x hx => by
      rcases hlook y ry' hy with rfl | ⟨-, hy'⟩
      · rw [hpl'] at hy; cases hy
        exact ⟨y, rp, hrp, rfl, List.mem_of_mem_eraseIdx hx⟩
      · exact ⟨y, ry', hy', rfl, hx⟩)
    hk3 (fun y j c hp => ⟨_, _, rm_pos X.v _ bl B n r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp
      h2 y j c hp⟩)
    hB' hent ((kill_rtOK X bl B' n rn bl).2 hrt') hlvx hfl hlr hcan ⟨pg, hpg, rfl⟩
  exact ⟨h1, h2', hp0, h2⟩

end rm

end bbolt
end EtcdGrove
end Perennial
